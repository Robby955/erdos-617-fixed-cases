"""Typeset the preprint, its two-page introduction, or the twelve-color paper."""

import argparse
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent
PROOF = ROOT / "proof"
REPOSITORY = "https://github.com/Robby955/erdos-617-fixed-cases"
RELEASE_TAG = "cutoff-2026-11-27"
CHAPTERS = [
    ("retained-width", "The cutoff at $2^{144}$", None),
    ("order-twelve", "The twelve-color theorem", None),
    ("weighted-width", "Appendix A. Weighted transversals and the width integral", None),
    ("cutoff-165", "Appendix B. Excess loads and the signed cut", None),
    ("cutoff-190", "Appendix C. Auxiliary rows and repeated choices", "## 5. Three tests"),
    ("cutoff-218", "Appendix D. Sampling the edges between rows", "For Theorem 3 use"),
    ("cutoff-289", "Appendix E. Counting independent transversals", "## 5. Can the proposed"),
    ("cutoff-320", "Appendix F. Choosing ordinary rows and counting repairs", "## What further reduction"),
    ("balanced-coloring", "Appendix G. Stability, shortage and the original cut", "## 7. Three nearly"),
    ("rooted-rows", "Appendix H. Extracting cliques on all vertices", "## 3. Rooted rows"),
]


def chapter_text(stem: str, title: str, stop: str | None) -> str:
    text = (PROOF / f"{stem}.md").read_text()
    if stop:
        text = text[:text.index(stop)]
    # The two headline proofs retain their statements. The earlier calculations
    # start at their first mathematical section with the original local numbering.
    if stem in {"retained-width", "order-twelve"}:
        body = text[text.index("**Theorem.**"):]
    else:
        body = text[text.index("## 1. "):]
    body = re.sub(r"^## (\d+)\. (.+)$", lambda m: f"## {m[1]}. {m[2]} {{#{stem}-{m[1]}}}", body,
                  flags=re.MULTILINE)
    if stem == "weighted-width":
        body = "This is the width argument at exponent 146. The cutoff chapter replaces its endpoint estimate.\n\n" + body
    if stem == "cutoff-165":
        body = "Sections 1 and 2 analyze the original choice of rows. Sections 3 to 5 give the general estimates used in Appendix A.\n\n" + body
    return f"\n\n\\newpage\n\n# {title} {{#{stem}}}\n\n{body.rstrip()}\n"


def prepare_links(text: str, source: Path, target: Path, anchors: set[str]) -> str:
    def resolve(match: re.Match) -> str:
        label, dest = match.groups()
        if dest == "#formal-proof" and "formal-proof" not in anchors:
            return f"[{label}]({REPOSITORY}/blob/{RELEASE_TAG}/cutoff/proof/formal-cutoff.md)"
        if re.match(r"^(?:https?://|#)", dest):
            return match.group()
        filename, _, fragment = dest.partition("#")
        path = (source / filename).resolve()
        stem = path.stem
        if path.parent == PROOF and path.suffix == ".md" and stem in anchors:
            section = re.match(r"(\d+)-", fragment)
            candidate = f"{stem}-{section[1]}" if section else stem
            return f"[{label}](#{candidate if candidate in anchors else stem})"
        if path == ROOT / "paper.pdf" and "retained-width" in anchors:
            return f"[{label}](#retained-width)"
        # A PDF file link can open adjacent source files when the package is downloaded.
        relative = path.relative_to(ROOT)
        if not target.name.startswith("review-"):
            suffix = f"#{fragment}" if fragment else ""
            return f"[{label}]({REPOSITORY}/blob/{RELEASE_TAG}/cutoff/{relative.as_posix()}{suffix})"
        name = relative.as_posix() if target.parent == ROOT else Path(filename).name
        return f"[{label}]({name})"
    return re.sub(r"(?<!!)\[([^\[\]\n]+)\]\(([^)\s]+)\)", resolve, text)


def build(kind: str, edition: str = "github") -> None:
    target = {"paper": ROOT / "paper.pdf", "overview": ROOT / "overview.pdf",
              "twelve": PROOF / "order-twelve.pdf",
              "corollary": PROOF / "retained-width-corollary.pdf"}[kind]
    metadata = []
    if edition == "github" and kind != "corollary":
        metadata = ["-M", "author=Robert Sneiderman and OpenAI GPT-6.2 Astra",
                    "-M", f"date={24 if kind == 'twelve' else 27} November 2026"]
    elif edition == "review" and kind != "corollary":
        target = target.with_name("review-" + target.name)
    manuscript = "paper.md" if edition == "github" else "paper-review.md"
    front = (ROOT / manuscript).read_text().replace("<!-- pagebreak -->", r"\newpage")
    if kind == "corollary":
        title = "A sharper cutoff for the Erdős–Gyárfás balanced-coloring conjecture"
        front = (f"---\ntitle: {title}\nauthor: Robert Sneiderman and OpenAI GPT-6.2 Astra\n"
                 "date: 25 November 2026\n---\n\n")
        statement = (PROOF / "retained-width-corollary.md").read_text().split("\n", 1)[1]
        width = chapter_text("retained-width", "The width estimate at $2^{144}$", None)
        anchors = set(re.findall(r"\{#([\w-]+)\}", width))
        front += prepare_links(statement + width, PROOF, target, anchors)
    elif kind == "twelve":
        text = (PROOF / "order-twelve.md").read_text()
        title = "The twelve-color case of the Erdős–Gyárfás balanced-coloring conjecture"
        front = f"---\ntitle: {title}\nauthor: Robert Sneiderman\ndate: 24 November 2026\n---\n\n"
        front += prepare_links(text[text.index("**Theorem.**"):], PROOF, target, set())
        if edition == "github":
            front += ("\n\nRobert Sneiderman directed the research. OpenAI GPT-6.2 Astra, "
                      "the AI model used in Codex, contributed to proof search, calculation, "
                      "Lean proofs and drafting. Fable contributed fixed-row arguments and checks.\n")
    else:
        chapters = [chapter_text(*chapter) for chapter in CHAPTERS] if kind == "paper" else []
        if edition == "github" and kind == "paper":
            corollary = (PROOF / "retained-width-corollary.md").read_text().split("\n", 1)[1]
            guide = (PROOF / "formal-cutoff.md").read_text().split("## Theorem statement", 1)[1]
            guide = guide.split("## Verification record,", 1)[0]
            guide = guide.replace("## The signed-cut inequality",
                                  "\\newpage\n\n## The signed-cut inequality")
            chapters.append(
                "\n\n\\newpage\n\n# Appendix I. The sharper cutoff and its Lean proof {#formal-proof}\n\n"
                + corollary + "\n## The formal statement\n" + guide
                + "\n[Build instructions and verification record](formal-cutoff.md#verification-commands)\n"
            )
            chapters.append(chapter_text("third-pruning", "Appendix J. A third pruning pass at $2^{143}$", None))
        anchors = set(re.findall(r"\{#([\w-]+)\}", "\n".join(chapters)))
        front = prepare_links(front, ROOT, target, anchors)
        front = re.sub(
            r"!\[([^]]+)\]\(figures/row-collision.png\)",
            lambda match: (r"\par\medskip\noindent\begin{minipage}{\linewidth}\centering"
                           r"\includegraphics[width=.84\linewidth]{figures/row-collision.pdf}"
                           r"\par\smallskip{\small " + match[1] + r"}\end{minipage}"),
            front,
        )
        if kind == "overview":
            paper = f"{REPOSITORY}/releases/download/{RELEASE_TAG}/paper.pdf" if edition == "github" else "paper.pdf"
            front += f"\n\n[Download the complete paper]({paper})\n"
        front += "".join(prepare_links(s, PROOF, target, anchors) for s in chapters)
    with tempfile.TemporaryDirectory() as temp:
        source = Path(temp) / "manuscript.md"
        source.write_text(front)
        subprocess.run([
            "pandoc", str(source), "--from=markdown+tex_math_dollars+tex_math_single_backslash",
            "--pdf-engine=xelatex", "-V", "papersize=letter", "-V", "fontsize=11pt",
            "-V", "geometry:top=0.72in,bottom=0.75in,left=0.78in,right=0.78in",
            "-V", "linestretch=0.98", "-V", "colorlinks=true", "-V", "linkcolor=NavyBlue",
            "-V", "urlcolor=NavyBlue", "-V", "bookmarksdepth=2",
            "-V", r"header-includes=\usepackage{graphicx}\setlength{\emergencystretch}{2em}",
            *metadata, "-o", str(target),
        ], check=True, cwd=target.parent)
    if edition == "github" and kind != "corollary":
        shutil.copyfile(target, target.with_name("github-" + target.name))
        site = ROOT.parent / "site"
        if kind == "paper" and (site / "index.html").is_file():
            shutil.copyfile(target, site / "paper.pdf")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=("paper", "overview", "twelve", "corollary"))
    parser.add_argument("--edition", choices=("review", "github"), default="github")
    args = parser.parse_args()
    build(args.target, args.edition)
