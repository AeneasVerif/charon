{ charon
, lib
, python3Packages
, writers
}:

(writers.writePython3Bin "charon-zulip-bot"
  {
    libraries = [ python3Packages.zulip ];
    flakeIgnore = [ "E501" ];
  } ''
  import argparse
  import logging
  import os
  import re
  import resource
  import signal
  import socket
  import subprocess
  import tempfile
  from pathlib import Path

  import zulip


  ADMIN_ROLES = {100, 200}
  MAX_SOURCE_BYTES = 64 * 1024
  MAX_OUTPUT_BYTES = 1024 * 1024
  MAX_INLINE_OUTPUT = 6000
  ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
  RUST_BLOCK = re.compile(
      r"```(?:rust|rs)?[ \t]*\r?\n(.*?)\r?\n```", re.IGNORECASE | re.DOTALL
  )


  class ShutdownRequested(BaseException):
      pass


  class ZulipClientWithSystemdNotification(zulip.Client):
      """Wraps the Zulip client to emit a systemd "ready" notification when the
      bot is ready to receive messages.
      """
      def register(self, *args, **kwargs):
          result = super().register(*args, **kwargs)
          notify_socket = os.environ.get("NOTIFY_SOCKET")
          if result.get("result") == "success" and notify_socket is not None:
              if notify_socket.startswith("@"):
                  notify_socket = "\0" + notify_socket[1:]
              with socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM) as notifier:
                  notifier.connect(notify_socket)
                  notifier.sendall(b"READY=1")
              del os.environ["NOTIFY_SOCKET"]
          return result


  def reply_request(message, content):
      if message["type"] == "stream":
          return {
              "type": "stream",
              "to": message["stream_id"],
              "topic": message["subject"],
              "content": content,
          }
      recipients = [recipient["id"] for recipient in message["display_recipient"]]
      return {"type": "private", "to": recipients, "content": content}


  def extract_source(content):
      blocks = RUST_BLOCK.findall(content)
      if len(blocks) != 1:
          raise ValueError("Please provide exactly one fenced `rust` code block.")
      source = blocks[0]
      if len(source.encode()) > MAX_SOURCE_BYTES:
          raise ValueError(f"The Rust source must be at most {MAX_SOURCE_BYTES // 1024} KiB.")
      return source


  def run_charon(source, timeout):
      with tempfile.TemporaryDirectory(prefix="charon-zulip-bot-") as directory:
          directory = Path(directory)
          source_path = directory / "input.rs"
          output_path = directory / "charon-output.txt"
          source_path.write_text(source)

          with output_path.open("wb") as output:
              process = subprocess.Popen(
                  ["${charon}/bin/charon", "ui_test", source_path.name],
                  cwd=directory,
                  stdout=output,
                  stderr=subprocess.STDOUT,
                  start_new_session=True,
                  preexec_fn=lambda: resource.setrlimit(
                      resource.RLIMIT_FSIZE, (MAX_OUTPUT_BYTES, MAX_OUTPUT_BYTES)
                  ),
              )
              timed_out = False
              try:
                  returncode = process.wait(timeout=timeout)
              except subprocess.TimeoutExpired:
                  timed_out = True
                  os.killpg(process.pid, signal.SIGKILL)
                  returncode = process.wait()

          output = ANSI_ESCAPE.sub("", output_path.read_text(errors="replace"))
          truncated = output_path.stat().st_size >= MAX_OUTPUT_BYTES
          if timed_out:
              output += f"\nCharon was stopped after {timeout} seconds."
          elif truncated:
              output += f"\nOutput was truncated after {MAX_OUTPUT_BYTES // 1024} KiB."
          if not output:
              output = "Charon produced no output."
          return returncode, output


  def fenced(content):
      longest_ticks = max((len(run) for run in re.findall(r"`+", content)), default=0)
      fence = "`" * max(3, longest_ticks + 1)
      return f"{fence}rust\n{content}\n{fence}"


  def main():
      parser = argparse.ArgumentParser(
          description="Run Charon on Rust snippets sent to a Zulip bot."
      )
      parser.add_argument("zuliprc", type=Path, help="configuration for a generic Zulip bot")
      parser.add_argument(
          "--timeout",
          type=int,
          default=15,
          help="maximum duration of one Charon invocation in seconds (default: 15)",
      )
      args = parser.parse_args()
      if args.timeout <= 0:
          parser.error("--timeout must be positive")

      logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
      client = ZulipClientWithSystemdNotification(config_file=str(args.zuliprc), client="CharonZulipBot")
      profile = client.get_profile()
      if profile.get("result") != "success":
          parser.error(f"failed to read the bot profile: {profile.get('msg', 'unknown error')}")
      bot_user_id = profile["user_id"]
      shutdown_requested = False
      handling_message = False

      def request_shutdown(_signum, _frame):
          nonlocal shutdown_requested
          shutdown_requested = True
          if not handling_message:
              raise ShutdownRequested

      def send_reply(message, content):
          result = client.send_message(reply_request(message, content))
          if result.get("result") != "success":
              logging.error("failed to send Zulip reply: %s", result.get("msg", result))

      def handle_event(event):
          nonlocal handling_message
          if shutdown_requested:
              raise ShutdownRequested
          handling_message = True
          try:
              message = event["message"]
              if message["sender_id"] == bot_user_id:
                  return
              if message["type"] == "stream" and "mentioned" not in event.get("flags", []):
                  return

              try:
                  user_result = client.get_user_by_id(message["sender_id"])
                  if user_result.get("result") != "success":
                      raise RuntimeError(user_result.get("msg", "unknown Zulip API error"))
                  user = user_result["user"]
                  if not user.get("is_active") or user.get("role") not in ADMIN_ROLES:
                      send_reply(message, "Only organization owners and administrators can run Charon.")
                      return

                  source = extract_source(message["content"])
                  returncode, output = run_charon(source, args.timeout)
                  heading = "Charon succeeded:" if returncode == 0 else f"Charon failed (exit status {returncode}):"
                  if len(output) <= MAX_INLINE_OUTPUT:
                      send_reply(message, f"{heading}\n\n{fenced(output)}")
                  else:
                      with tempfile.NamedTemporaryFile(
                          mode="w+", encoding="utf-8", suffix="-charon-output.txt"
                      ) as output_file:
                          output_file.write(output)
                          output_file.flush()
                          output_file.seek(0)
                          upload = client.upload_file(output_file)
                      if upload.get("result") != "success":
                          raise RuntimeError(upload.get("msg", "failed to upload Charon output"))
                      send_reply(message, f"{heading} [full output]({upload['url']})")
              except ValueError as error:
                  send_reply(message, str(error))
              except Exception:
                  logging.exception("failed to process Zulip message %s", message.get("id"))
                  send_reply(message, "The Charon bot encountered an internal error.")
          finally:
              handling_message = False
              if shutdown_requested:
                  raise ShutdownRequested

      try:
          # When receiving SIGTERM, finish processing the current message then
          # stop processing any new ones and shut down.
          signal.signal(signal.SIGTERM, request_shutdown)
          logging.info("waiting for Zulip messages as %s", profile["full_name"])
          client.call_on_each_event(handle_event, event_types=["message"])
      except ShutdownRequested:
          logging.info("shutdown requested; all active work is complete")


  if __name__ == "__main__":
      main()
'').overrideAttrs (_: {
  meta = {
    description = "Zulip bot that runs Charon on Rust snippets";
    mainProgram = "charon-zulip-bot";
    platforms = lib.platforms.unix;
  };
})
