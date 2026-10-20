#!/usr/bin/env python3
"""Rebuild the public manuscript PDF from the Markdown source.

Requires: pandoc, xelatex and a standard LaTeX distribution with Latin Modern.
The mathematics after the source front matter is preserved unchanged.
"""
from pathlib import Path
import subprocess
import tempfile
import shutil

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "manuscript" / "EC2_PROOF.md"
DESTINATION = ROOT / "manuscript" / "EC2_PROOF.pdf"

def main():
    with tempfile.TemporaryDirectory(prefix="ec2-paper-") as tmp:
        out = Path(tmp)
        tex = out / "ec2-paper.tex"
        subprocess.run([
            "pandoc", str(SOURCE), "--from=markdown+tex_math_single_backslash",
            "--to=latex", "--standalone", "--output", str(tex),
            "-V", "geometry:margin=0.94in", "-V", "fontsize=10pt",
            "-V", "colorlinks=true", "-V", "urlcolor=blue", "-V", "linkcolor=blue",
        ], check=True)
        text = tex.read_text(encoding="utf-8")
        needle = r"\author{Dehao Lin}"
        assert text.count(needle) == 1, "Unexpected Pandoc author representation"
        # Only the title block is changed here, not the mathematical proof text.
        replacement = (
            r"\author{Dehao Lin\\[3pt]"
            r"{\small School of Physics, Sun Yat-sen University, Guangzhou, China}\\[2pt]"
            r"{\small \href{mailto:lindh9@mail2.sysu.edu.cn}{lindh9@mail2.sysu.edu.cn}}}"
        )
        text = text.replace(needle, replacement)
        tex.write_text(text, encoding="utf-8")
        subprocess.run([
            "xelatex", "-interaction=nonstopmode", "-halt-on-error",
            "-output-directory", str(out), str(tex),
        ], check=True, cwd=out, stdout=subprocess.DEVNULL)
        shutil.copy2(out / "ec2-paper.pdf", DESTINATION)
    print("Written", DESTINATION)

if __name__ == "__main__":
    main()
