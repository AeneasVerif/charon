import argparse
import re
import subprocess
from pathlib import Path


UNSUPPORTED_FEATURES = (
    "generic_const_exprs",
    "adt_const_params",
    "min_generic_const_args",
    "effects",
    "transmutability",
    "loop_match",
    "default_type_parameter_fallback",
    "negative_bounds",
    "repr_simd",
    "rustc_private",
    "default_field_values",
)

EXPENSIVE_RUSTC_STRESS_TESTS = {
    "associated-consts/issue-93775.rs",
    "bench/issue-32062.rs",
    "closures/many-closures.rs",
    "closures/issue-72408-nested-closures-exponential.rs",
    "codegen/normalization-overflow/recursion-issue-139659.rs",
    "codegen/no-codegen-blowup-in-deeply-nested-struct.rs",
    "debuginfo/debuginfo-inline-callsite-location-macro-1.rs",
    "debuginfo/debuginfo-inline-callsite-location-macro-2.rs",
    "drop/or-pattern-drop-order.rs",
    "expr/if/expr-stack-overflow.rs",
    "expr/weird-exprs.rs",
    "generics/issue-32498.rs",
    "impl-trait/example-calendar.rs",
    "iterators/issue-58952-filter-type-length.rs",
    "iterators/iter-map-fold-type-length.rs",
    "macros/type-macros-hlist.rs",
    "match/match-stack-overflow-72933-.rs",
    "query-system/query_depth.rs",
}

SPECIAL_UNSUPPORTED_FILES = {
    "abi/unsized-args-in-c-abi-issues-94223-115845.rs",
    "attributes/export/crate-type.rs",
    "attributes/export/crate-type-2.rs",
    "attributes/export/exportable.rs",
    "attributes/export/lang-item.rs",
    "cfg/assume-incomplete-release/auxiliary/ver-cfg-rel.rs",
    "codegen/incorrect-arch-intrinsic.rs",
    "codegen/incorrect-llvm-intrinsic-signature.rs",
    "codegen/unknown-llvm-intrinsic.rs",
    "compile-flags/invalid/invalid-llvm-passes.rs",
    "duplicate/dupe-symbols-7.rs",
    "duplicate/dupe-symbols-8.rs",
    "error-codes/E0511.rs",
    "intrinsics/non-integer-atomic.rs",
    "limits/huge-array-simple-32.rs",
    "limits/huge-array-simple-64.rs",
    "limits/huge-array.rs",
    "limits/huge-enum.rs",
    "limits/huge-struct.rs",
    "limits/issue-15919-32.rs",
    "limits/issue-15919-64.rs",
    "limits/vtable.rs",
    "link-native-libs/suggest-libname-only-1.rs",
    "link-native-libs/suggest-libname-only-2.rs",
    "lint/non-snake-case/non-snake-ffi-issue-31924.rs",
    "lto/issue-11154.rs",
    "macros/auxiliary/macro-comma-support.rs",
    "meta/no_std-extern-libc.rs",
    "nll/polonius/array-literal-index-oob-2024.rs",
    "parser/issues/auxiliary/issue-21146-inc.rs",
}

VALID_EDITIONS = {"2015", "2018", "2021", "2024", "future"}
CFG_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class TestFile:
    def __init__(self, path: Path):
        self.path = path
        self.path_str = path.as_posix()
        self.lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        self.one_line_text = " ".join(self.lines)
        self.scoped_comments = self._scoped_comments()

    def _scoped_comments(self) -> list[tuple[set[str], str]]:
        comments = []
        for line in self.lines:
            match = re.match(r"^//@? ?\[([^]]+)\] ?(.*)", line)
            if match is None:
                continue
            revs = set(re.sub(r"\s+", "", match.group(1)).split(","))
            comments.append((revs, match.group(2)))
        return comments

    def has_magic_comment(self, magic: str) -> bool:
        pattern = re.compile(r"^//@? ?" + re.escape(magic))
        return any(pattern.match(line) for line in self.lines)

    def revisions(self) -> list[str]:
        revisions = []
        for line in self.lines:
            match = re.match(r"^//@? ?revisions:\s*(.*)", line)
            if match is not None:
                revisions.extend(match.group(1).split())
        return revisions

    def case_revisions(self) -> list[str]:
        return self.revisions() or [""]

    def has_revision_magic_comment(self, rev: str, magic: str) -> bool:
        if self.has_magic_comment(magic):
            return True
        if not rev:
            return False
        return any(rev in revs and comment.startswith(magic) for revs, comment in self.scoped_comments)

    def directive_values(self, rev: str, directive: str) -> list[str]:
        values = []
        global_pattern = re.compile(r"^//@? ?" + re.escape(directive) + r":\s*(.*)")
        scoped_pattern = re.compile(r"^" + re.escape(directive) + r":\s*(.*)")

        for line in self.lines:
            match = global_pattern.match(line)
            if match is not None:
                values.append(match.group(1))

        if rev:
            for revs, comment in self.scoped_comments:
                match = scoped_pattern.match(comment)
                if rev in revs and match is not None:
                    values.append(match.group(1))

        return values

    def has_feature(self, feature: str) -> bool:
        feature_pattern = re.escape(feature)
        pattern = re.compile(
            rf"#!\[feature\(\s*{feature_pattern}(?:[^A-Za-z0-9_]|$)"
            rf"|#!\[feature\([^]]*[^A-Za-z0-9_]{feature_pattern}(?:[^A-Za-z0-9_]|$)"
        )
        return pattern.search(self.one_line_text) is not None


def revision_suffix(rev: str) -> str:
    return f".{rev}" if rev else ""


def case_file(path: Path, rev: str) -> Path:
    return Path(f"{path}{revision_suffix(rev)}")


def strip_rs_extension(path: Path) -> Path:
    path_str = path.as_posix()
    if path_str.endswith(".rs"):
        return Path(path_str[:-3])
    return path


def split_compile_flags(flags: str) -> list[str]:
    split_flags = []
    token = []
    quote = None
    escaped = False

    for ch in flags:
        if escaped:
            token.append(ch)
            escaped = False
            continue

        if ch == "\\" and quote != "'":
            escaped = True
            continue

        if quote is not None:
            if ch == quote:
                quote = None
            else:
                token.append(ch)
            continue

        if ch in {"'", '"'}:
            if token:
                token.append(ch)
            else:
                quote = ch
        elif ch.isspace():
            if token:
                split_flags.append("".join(token))
                token = []
        else:
            token.append(ch)

    if escaped:
        token.append("\\")

    if token:
        split_flags.append("".join(token))

    return split_flags


def has_unsupported_edition(test_file: TestFile, rev: str) -> bool:
    return any(edition not in VALID_EDITIONS for edition in test_file.directive_values(rev, "edition"))


def has_unsupported_compile_flags(test_file: TestFile, rev: str) -> bool:
    for flags in test_file.directive_values(rev, "compile-flags"):
        padded = f" {flags} "
        if (
            " @" in padded
            or " --explain " in padded
            or " --explain=" in padded
            or " --print " in padded
            or " --print=" in padded
            or " -V " in padded
            or " -vV " in padded
            or " --version " in padded
            or " --verbose " in padded
            or " --error-format " in padded
            or " --error-format=" in padded
            or " --color " in padded
            or " --color=" in padded
            or " --json " in padded
            or " --json=" in padded
            or " -Cllvm-args" in padded
            or " -C llvm-args" in padded
            or " -Zterminal-urls" in padded
            or " -Zunpretty" in padded
            or " unpretty=" in padded
            or " print-type-sizes " in padded
            or " -Zprint-type-sizes" in padded
            or " parse-crate-root-only " in padded
            or " -Zparse-crate-root-only" in padded
        ):
            return True
    return False


def has_auxiliary_path_attr(test_file: TestFile) -> bool:
    return any(re.search(r'#\[path *= *".*auxiliary/', line) for line in test_file.lines)


def is_expensive_rustc_stress_test(path: Path) -> bool:
    return path.as_posix().removeprefix("test-results/") in EXPENSIVE_RUSTC_STRESS_TESTS


def unsupported_build_settings(test_file: TestFile, rev: str) -> bool:
    path = test_file.path
    path_parts = set(path.parts)
    return (
        test_file.path_str.removeprefix("test-results/") in SPECIAL_UNSUPPORTED_FILES
        or (path.parent / "compiletest-ignore-dir").exists()
        or "auxiliary" in path_parts
        or test_file.has_revision_magic_comment(rev, "ignore-test")
        or test_file.has_revision_magic_comment(rev, "ignore-auxiliary")
        or test_file.has_revision_magic_comment(rev, "known-bug")
        or test_file.has_revision_magic_comment(rev, "only-")
        or test_file.has_revision_magic_comment(rev, "needs-asm-support")
        or test_file.has_revision_magic_comment(rev, "needs-subprocess")
        or test_file.has_revision_magic_comment(rev, "needs-")
        or test_file.has_revision_magic_comment(rev, "dont-check-compiler-stderr")
        or test_file.has_revision_magic_comment(rev, "stderr-per-bitwidth")
        or test_file.has_revision_magic_comment(rev, "ignore-parallel-frontend")
        or test_file.has_revision_magic_comment(rev, "aux-build")
        or test_file.has_revision_magic_comment(rev, "aux-crate")
        or test_file.has_revision_magic_comment(rev, "proc-macro")
        or test_file.has_revision_magic_comment(rev, "rustc-env")
        or has_unsupported_edition(test_file, rev)
        or has_unsupported_compile_flags(test_file, rev)
        or has_auxiliary_path_attr(test_file)
    )


def unsupported_feature(test_file: TestFile) -> bool:
    return any(test_file.has_feature(feature) for feature in UNSUPPORTED_FEATURES)


def rustc_args(test_file: TestFile, rev: str) -> list[str]:
    args = []
    for flags in test_file.directive_values(rev, "compile-flags"):
        args.extend(split_compile_flags(flags))

    edition = ""
    for value in test_file.directive_values(rev, "edition"):
        if value:
            edition = value
    if edition:
        args.append(f"--edition={edition}")

    if rev and CFG_IDENT_RE.match(rev):
        args.extend(["--cfg", rev])

    return args


def run_revision(test_file: TestFile, rev: str, charon: str, timeout: int) -> None:
    current_case_file = case_file(test_file.path, rev)
    status_path = Path(f"{current_case_file}.charon-status")

    if unsupported_build_settings(test_file, rev):
        status_path.write_text("unsupported-build-settings", encoding="utf-8")
        return

    if is_expensive_rustc_stress_test(test_file.path):
        status_path.write_text("stress-test", encoding="utf-8")
        return

    if unsupported_feature(test_file):
        status_path.write_text("unsupported-feature", encoding="utf-8")
        return

    output_path = Path(f"{current_case_file}.charon-output")
    cmd = [
        charon,
        "rustc",
        "--dest-file",
        f"{current_case_file}.llbc",
        "--",
        test_file.path.as_posix(),
        *rustc_args(test_file, rev),
    ]

    with output_path.open("wb") as output:
        try:
            completed = subprocess.run(
                cmd,
                stdout=output,
                stderr=subprocess.STDOUT,
                timeout=timeout,
                check=False,
            )
            status = completed.returncode
        except subprocess.TimeoutExpired:
            status = 124

    status_path.write_text(str(status), encoding="utf-8")


def run_test(args: argparse.Namespace) -> None:
    test_file = TestFile(args.file)
    for rev in test_file.case_revisions():
        run_revision(test_file, rev, args.charon, args.timeout)


def expects_success(test_file: TestFile, rev: str) -> bool:
    if (
        test_file.has_revision_magic_comment(rev, "run-pass")
        or test_file.has_revision_magic_comment(rev, "build-pass")
        or test_file.has_revision_magic_comment(rev, "check-pass")
    ):
        return True

    base = strip_rs_extension(test_file.path)
    if rev:
        if Path(f"{base}.{rev}.stderr").is_file():
            return False
        if Path(f"{base}.stderr").is_file():
            return False
        return True

    return not Path(f"{base}.stderr").is_file()


def output_text(current_case_file: Path) -> str:
    output_path = Path(f"{current_case_file}.charon-output")
    return output_path.read_text(encoding="utf-8", errors="replace")


def classify_got(status: int, output: str) -> str:
    if status == 0:
        return "success"
    if status == 124:
        return "stack overflow/timeout"
    if "error: internal compiler error" in output or re.search(r"thread .rustc. .* panicked", output):
        return "internal compiler error"
    if status in {101, 255}:
        if "fatal runtime error: stack overflow" in output:
            return "stack overflow/timeout"
        return "panic"
    if status == 2:
        return "failure in rustc"
    return "failure in charon"


def analyze_revision(test_file: TestFile, rev: str) -> str:
    current_case_file = case_file(test_file.path, rev)
    status_text = Path(f"{current_case_file}.charon-status").read_text(encoding="utf-8")

    if status_text == "stress-test":
        result = "⊘ stress-test"
    elif status_text.startswith("unsupported"):
        result = f"⊘ {status_text}"
    else:
        output = output_text(current_case_file)
        if test_file.path_str.removeprefix("test-results/") in SPECIAL_UNSUPPORTED_FILES:
            result = "⊘ unsupported-build-settings"
        elif re.search(r"error.E0601", output):
            result = "⊘ unsupported-build-settings"
        elif re.search(r"error.E0463", output):
            result = "⊘ unsupported-build-settings"
        elif re.search(r"error.E0583", output):
            result = "⊘ unsupported-build-settings"
        else:
            got = classify_got(int(status_text), output)
            marker = "❌"
            extras = ""

            if expects_success(test_file, rev):
                expected = "success"
                if got == "success":
                    if Path(f"{current_case_file}.llbc").exists():
                        marker = "✅"
                        if re.search(r"The extraction generated .* warnings", output):
                            extras = "warnings"
                        else:
                            extras = "no warnings"
                    else:
                        extras = "without llbc output"
            else:
                expected = "failure"
                if got == "failure in rustc":
                    marker = "✅"
                elif got != "success":
                    got = "other failure"

            if extras:
                extras = f" ({extras})"
            result = f"{marker} expected: {expected:<18}  got: {got}{extras}"

    return f"{current_case_file}: {result}"


def analyze_test(args: argparse.Namespace) -> None:
    test_file = TestFile(args.file)
    for rev in test_file.case_revisions():
        print(analyze_revision(test_file, rev))


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(required=True)

    run_parser = subparsers.add_parser("run")
    run_parser.add_argument("--charon", required=True)
    run_parser.add_argument("--timeout", type=int, default=10)
    run_parser.add_argument("file", type=Path)
    run_parser.set_defaults(func=run_test)

    analyze_parser = subparsers.add_parser("analyze")
    analyze_parser.add_argument("file", type=Path)
    analyze_parser.set_defaults(func=analyze_test)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
