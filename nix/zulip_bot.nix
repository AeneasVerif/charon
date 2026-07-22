{ charon
, jailNixLib
, lib
, pkgs
, python3Packages
, writers
}:

let
  maxTmpfsBytes = 256 * 1024 * 1024;
  jail = jailNixLib.extend {
    inherit pkgs;
    # The default jail also provides a shell, coreutils, and fake passwd files.
    # Charon needs none of those inside the sandbox.
    basePermissions = combinators: with combinators; [
      bind-nix-store-runtime-closure
    ];
  };
  sandboxedCharon = jail "charon-sandbox" "${charon}/bin/charon" (combinators: with combinators; [
    (unsafe-add-raw-args (lib.concatStringsSep " " [
      "--disable-userns"
      "--cap-drop ALL"
      "--hostname charon-sandbox"
      "--clearenv"
      "--proc /proc"
      "--remount-ro /proc"
      "--dev /dev"
      "--size ${toString maxTmpfsBytes} --tmpfs /tmp"
      "--size ${toString maxTmpfsBytes} --tmpfs /work"
      "--chdir /work"
    ]))
    (set-env "HOME" "/tmp")
    (set-env "TMPDIR" "/tmp")
    (set-env "PATH" "/empty")
    (add-runtime ''
      if (( $# != 1 )); then
        echo "Usage: charon-sandbox INPUT_RS" >&2
        exit 2
      fi
      INPUT_RS=$(realpath -- "$1")
      if [[ ! -f "$INPUT_RS" ]]; then
        echo "Input is not a regular file: $1" >&2
        exit 2
      fi
      RUNTIME_ARGS+=(--ro-bind "$INPUT_RS" /work/input.rs)
    '')
    (set-argv [ "ui_test" "input.rs" ])
  ]);
  sandboxedCharonWithLimits = pkgs.writeShellApplication {
    name = "charon-sandbox-limited";
    runtimeInputs = [ pkgs.util-linux ];
    text = ''
      if (( $# != 2 )) || [[ ! "$1" =~ ^[1-9][0-9]*$ ]]; then
        echo "Usage: charon-sandbox-limited TIMEOUT INPUT_RS" >&2
        exit 2
      fi
      exec ${lib.getExe' pkgs.util-linux "prlimit"} \
        --core=0 \
        --fsize=1048576 \
        --as=2147483648 \
        --nproc=256 \
        --nofile=128 \
        --cpu="$1:$1" \
        -- ${sandboxedCharon}/bin/charon-sandbox "$2"
    '';
  };
in
(writers.writePython3Bin "charon-zulip-bot"
  {
    libraries = [ python3Packages.zulip ];
    flakeIgnore = [ "E501" ];
  } ''
  import argparse
  import logging
  import math
  import os
  import re
  import signal
  import sqlite3
  import socket
  import subprocess
  import tempfile
  import time
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
                  [
                      "${sandboxedCharonWithLimits}/bin/charon-sandbox-limited",
                      str(timeout),
                      str(source_path),
                  ],
                  stdout=output,
                  stderr=subprocess.STDOUT,
                  # The sandbox installs a PID-1 helper whose environment is
                  # readable through `/proc/1/environ`, so scrub the environment
                  # before the wrapper starts, not only before Charon starts.
                  env={},
                  start_new_session=True,
              )
              timed_out = False
              try:
                  returncode = process.wait(timeout=timeout)
              except subprocess.TimeoutExpired:
                  timed_out = True
                  os.killpg(process.pid, signal.SIGKILL)
                  returncode = process.wait()

          output = ANSI_ESCAPE.sub("", output_path.read_text(errors="replace"))
          output = output.removeprefix("# Final LLBC before serialization:\n\n")
          truncated = output_path.stat().st_size >= MAX_OUTPUT_BYTES
          if timed_out:
              output += f"\nCharon was stopped after {timeout} seconds."
          elif truncated:
              output += f"\nOutput was truncated after {MAX_OUTPUT_BYTES // 1024} KiB."
          if not output:
              output = "Charon produced no output."
          return returncode, output


  def fenced(content):
      # Tilde fences keep the Rust block from colliding with the surrounding
      # backtick-delimited Zulip spoiler.
      longest_tildes = max((len(run) for run in re.findall(r"~+", content)), default=0)
      fence = "~" * max(3, longest_tildes + 1)
      return f"{fence}rust\n{content}\n{fence}"


  def spoiler(content):
      return f"```spoiler Charon result\n{content}\n```"


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
      parser.add_argument(
          "--cooldown",
          type=int,
          default=5,
          help="minimum time between requests by one user in seconds (default: 5)",
      )
      parser.add_argument(
          "--database",
          type=Path,
          help=(
              "path to the response database (default: responses.sqlite3 in "
              "$STATE_DIRECTORY, $XDG_STATE_HOME/charon-zulip-bot, or "
              "~/.local/state/charon-zulip-bot)"
          ),
      )
      args = parser.parse_args()
      if args.timeout <= 0:
          parser.error("--timeout must be positive")
      if args.cooldown < 0:
          parser.error("--cooldown must be non-negative")

      if args.database is None:
          if state_directory := os.environ.get("STATE_DIRECTORY"):
              database_directory = Path(state_directory.split(":", 1)[0])
          elif xdg_state_home := os.environ.get("XDG_STATE_HOME"):
              database_directory = Path(xdg_state_home) / "charon-zulip-bot"
          else:
              database_directory = Path.home() / ".local/state/charon-zulip-bot"
          args.database = database_directory / "responses.sqlite3"
      args.database.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
      database = sqlite3.connect(args.database)
      database.execute("""
          CREATE TABLE IF NOT EXISTS responses (
              source_message_id INTEGER PRIMARY KEY,
              response_message_id INTEGER NOT NULL,
              sender_id INTEGER NOT NULL
          )
      """)
      database.commit()
      args.database.chmod(0o600)

      logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
      logging.info("using response database %s", args.database)
      client = ZulipClientWithSystemdNotification(config_file=str(args.zuliprc), client="CharonZulipBot")
      profile = client.get_profile()
      if profile.get("result") != "success":
          parser.error(f"failed to read the bot profile: {profile.get('msg', 'unknown error')}")
      bot_user_id = profile["user_id"]
      shutdown_requested = False
      handling_message = False
      last_request_by_user = {}

      def request_shutdown(_signum, _frame):
          nonlocal shutdown_requested
          shutdown_requested = True
          if not handling_message:
              raise ShutdownRequested

      def send_reply(message, content):
          result = client.send_message(reply_request(message, content))
          if result.get("result") != "success":
              logging.error("failed to send Zulip reply: %s", result.get("msg", result))
              return None
          return result["id"]

      def is_admin(sender_id):
          user_result = client.get_user_by_id(sender_id)
          if user_result.get("result") != "success":
              raise RuntimeError(user_result.get("msg", "unknown Zulip API error"))
          user = user_result["user"]
          return user.get("is_active") and user.get("role") in ADMIN_ROLES

      def response_content(content):
          try:
              source = extract_source(content)
          except ValueError as error:
              return str(error)

          returncode, output = run_charon(source, args.timeout)
          heading = None if returncode == 0 else f"Charon failed (exit status {returncode}):"
          if len(output) <= MAX_INLINE_OUTPUT:
              content = fenced(output)
              return content if heading is None else f"{heading}\n\n{content}"

          with tempfile.NamedTemporaryFile(
              mode="w+", encoding="utf-8", suffix="-charon-output.txt"
          ) as output_file:
              output_file.write(output)
              output_file.flush()
              output_file.seek(0)
              upload = client.upload_file(output_file)
          if upload.get("result") != "success":
              raise RuntimeError(upload.get("msg", "failed to upload Charon output"))
          content = f"[full output]({upload['url']})"
          return content if heading is None else f"{heading} {content}"

      def handle_event(event):
          nonlocal handling_message
          if shutdown_requested:
              raise ShutdownRequested
          handling_message = True
          try:
              if event["type"] == "message":
                  message = event["message"]
                  if message["sender_id"] == bot_user_id:
                      return
                  if message["type"] == "stream" and "mentioned" not in event.get("flags", []):
                      return

                  try:
                      if not is_admin(message["sender_id"]):
                          send_reply(
                              message,
                              "Only organization owners and administrators can run Charon.",
                          )
                          return

                      now = time.monotonic()
                      retry_after = args.cooldown - (
                          now - last_request_by_user.get(message["sender_id"], -math.inf)
                      )
                      if retry_after > 0:
                          send_reply(
                              message,
                              f"Please wait {math.ceil(retry_after)} seconds before running Charon again.",
                          )
                          return
                      last_request_by_user[message["sender_id"]] = now

                      content = spoiler(response_content(message["content"]))
                  except Exception:
                      logging.exception("failed to process Zulip message %s", message.get("id"))
                      content = "The Charon bot encountered an internal error."

                  response_message_id = send_reply(message, content)
                  if response_message_id is not None:
                      with database:
                          database.execute(
                              """
                              INSERT INTO responses (
                                  source_message_id, response_message_id, sender_id
                              ) VALUES (?, ?, ?)
                              ON CONFLICT(source_message_id) DO UPDATE SET
                                  response_message_id = excluded.response_message_id,
                                  sender_id = excluded.sender_id
                              """,
                              (message["id"], response_message_id, message["sender_id"]),
                          )
                  return

              if event["type"] == "update_message":
                  if event.get("rendering_only") or "content" not in event:
                      return
                  mapping = database.execute(
                      """
                      SELECT response_message_id, sender_id
                      FROM responses
                      WHERE source_message_id = ?
                      """,
                      (event["message_id"],),
                  ).fetchone()
                  if mapping is None:
                      return
                  response_message_id, sender_id = mapping

                  try:
                      if not is_admin(sender_id):
                          content = "Only organization owners and administrators can run Charon."
                      else:
                          # Edits replace an existing request, so they deliberately
                          # bypass the cooldown for new requests.
                          content = spoiler(response_content(event["content"]))
                  except Exception:
                      logging.exception(
                          "failed to process edited Zulip message %s", event["message_id"]
                      )
                      content = "The Charon bot encountered an internal error."

                  result = client.update_message(
                      {"message_id": response_message_id, "content": content}
                  )
                  if result.get("result") != "success":
                      logging.error(
                          "failed to update Zulip response %s: %s",
                          response_message_id,
                          result.get("msg", result),
                      )
          finally:
              handling_message = False
              if shutdown_requested:
                  raise ShutdownRequested

      try:
          # When receiving SIGTERM, finish processing the current message then
          # stop processing any new ones and shut down.
          signal.signal(signal.SIGTERM, request_shutdown)
          logging.info("waiting for Zulip messages as %s", profile["full_name"])
          client.call_on_each_event(
              handle_event, event_types=["message", "update_message"]
          )
      except ShutdownRequested:
          logging.info("shutdown requested; all active work is complete")
      finally:
          database.close()


  if __name__ == "__main__":
      main()
'').overrideAttrs (_: {
  meta = {
    description = "Zulip bot that runs Charon on Rust snippets";
    mainProgram = "charon-zulip-bot";
    platforms = lib.platforms.linux;
  };
})
