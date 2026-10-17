#!/usr/bin/env python3
"""Build all default proof roots and audit the printed theorem dependencies."""

import argparse
from pathlib import Path
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Path to the pinned toolchain's lake executable")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|partial)\b")
    for source in root.glob("*.lean"):
        for number, line in enumerate(source.read_text().splitlines(), 1):
            if forbidden.search(line):
                sys.exit(f"Forbidden proof escape or declaration at {source.name}:{number}: {line}")

    build = subprocess.run([args.lake, "build"], cwd=root, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, check=False)
    print(build.stdout, end="")
    if build.returncode:
        sys.exit(build.returncode)
    if "sorryAx" in build.stdout:
        sys.exit("A theorem depends on a proof placeholder")

    allowed = {"propext", "Classical.choice", "Quot.sound"}
    checked = set()
    for name, dependencies in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", build.stdout):
        actual = {dependency.strip() for dependency in dependencies.split(",") if dependency.strip()}
        if extra := actual - allowed:
            sys.exit(f"Unexpected axioms in {name}: {sorted(extra)}")
        checked.add(name)
    checked.update(re.findall(r"'([^']+)' does not depend on any axioms", build.stdout))
    required = {
        "pipeline_sound", "dsl_pipeline_sound", "compiled_parallel_reference",
        "compiled_execution_reference", "dsl_execution_reference", "evaluate_calls_safe",
        "compiled_handler_trace_reference", "compiled_admission_no_unseen_predecessor",
        "compiled_admit_safe", "admit_conserves_events", "compiled_boundary_signals",
        "compiled_boundary_conserves_outputs", "compiled_domain_has_owner",
        "globalFold_matches_grouped_fold",
    }
    if missing := required - {name.rsplit(".", 1)[-1] for name in checked}:
        sys.exit(f"Missing principal theorem axiom reports: {sorted(missing)}")
    print(f"Proof audit passed: {len(checked)} theorem reports, standard logical axioms only.")


if __name__ == "__main__":
    main()
