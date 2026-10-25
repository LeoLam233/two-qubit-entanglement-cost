#!/usr/bin/env python3
"""Build manuscript/EC2_PROOF.pdf from the sole canonical TeX source.

Requires Python 3 and pdfLaTeX with the packages listed in the README.
Use --log-dir PATH to retain compiler output, .log and .aux files.
The fixed SOURCE_DATE_EPOCH and pdfTeX build settings make repeated builds
byte-identical with the same TeX distribution and package versions.
"""
from pathlib import Path
import argparse
import hashlib
import os
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "manuscript" / "EC2_PROOF.tex"
DESTINATION = ROOT / "manuscript" / "EC2_PROOF.pdf"
SOURCE_DATE_EPOCH = "1792517193"  # Public baseline commit, 2026-10-20 17:26:33 UTC.
PRELUDE = (
    r"\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=15"
    r"\input{EC2_PROOF.tex}"
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-dir", type=Path, help="retain all build diagnostics")
    args = parser.parse_args()
    if not SOURCE.is_file():
        parser.error(f"Canonical source is missing: {SOURCE}")
    if not shutil.which("pdflatex"):
        parser.error("pdflatex is required; install TeX Live or MiKTeX (see README)")
    log_dir = args.log_dir.resolve() if args.log_dir else None
    if log_dir:
        log_dir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(SOURCE_DATE_EPOCH=SOURCE_DATE_EPOCH, FORCE_SOURCE_DATE="1", TZ="UTC")
    print(f"Source SHA-256: {sha256(SOURCE)}", flush=True)
    print(f"SOURCE_DATE_EPOCH={SOURCE_DATE_EPOCH}; FORCE_SOURCE_DATE=1; TZ=UTC", flush=True)
    print("pdfLaTeX version:", subprocess.check_output(
        ["pdflatex", "--version"], text=True, env=env).splitlines()[0], flush=True)
    with tempfile.TemporaryDirectory(prefix=".ec2-paper-", dir=SOURCE.parent) as tmp:
        out = Path(tmp).resolve()
        # Keep both build products and automatic cleanup inside the manuscript
        # directory, including in sandboxes with restricted system temp access.
        if out.parent != SOURCE.parent.resolve():
            raise RuntimeError("Unexpected build directory outside manuscript")
        command = [
            "pdflatex", "-interaction=nonstopmode", "-halt-on-error",
            "-file-line-error", "-no-shell-escape", "-recorder",
            "-jobname=EC2_PROOF", f"-output-directory={out}", PRELUDE,
        ]
        previous_aux = None
        try:
            for run in range(1, 5):
                print(f"Pass {run} command: {subprocess.list2cmdline(command)}", flush=True)
                result = subprocess.run(command, cwd=SOURCE.parent, env=env,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                output = result.stdout.decode("utf-8", errors="replace")
                print(output, end="", flush=True)
                print(f"Pass {run} exit status: {result.returncode}", flush=True)
                if log_dir:
                    (log_dir/f"pdflatex-pass-{run}.txt").write_text(output, encoding="utf-8")
                if result.returncode:
                    raise SystemExit(result.returncode)
                aux = (out/"EC2_PROOF.aux").read_bytes()
                tex_log = (out/"EC2_PROOF.log").read_text(encoding="utf-8", errors="replace")
                rerun = "Rerun to get" in tex_log or "Rerun to get" in output
                if run >= 2 and aux == previous_aux and not rerun:
                    break
                previous_aux = aux
            else:
                raise SystemExit("References did not stabilize after four passes")
            bad = re.findall(
                r"[^\n]*(?:undefined|multiply defined|Missing character:|Overfull \\[hv]box|destination with the same identifier|duplicate ignored)[^\n]*",
                tex_log, flags=re.I)
            if bad:
                raise SystemExit("Unresolved build diagnostics:\n"+"\n".join(bad))
            shutil.copyfile(out/"EC2_PROOF.pdf", DESTINATION)
            print(f"Written: {DESTINATION}", flush=True)
            print(f"PDF SHA-256: {sha256(DESTINATION)}", flush=True)
        finally:
            if log_dir:
                for suffix in ["log", "aux", "out", "fls"]:
                    path = out/f"EC2_PROOF.{suffix}"
                    if path.exists():
                        shutil.copyfile(path, log_dir/path.name)


if __name__ == "__main__":
    main()
