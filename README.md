# Fixed-case proof claims for Erdős Problem 617

This repository contains two fixed-parameter proof claims related to
[Erdős Problem 617](https://www.erdosproblems.com/617), an edge-coloring
problem of Erdős and Gyárfás.

## Claims

- **$r=5$:** Every five-coloring of the edges of $K_{26}$ has six vertices
  whose induced $K_6$ omits at least one color. Equivalently,
  $R(6;5,4)=26$.
  [PDF](r5/erdos-617-r5.pdf) | [TeX source](r5/main.tex)

- **$r=6$:** Every six-coloring of the edges of $K_{37}$ has seven vertices
  whose induced $K_7$ omits at least one color.
  [PDF](r6/erdos-617-r6.pdf) | [TeX source](r6/main.tex)

These claims address only $r=5$ and $r=6$. They do not settle the statement
for every $r\geq3$.

## Review status

Both manuscripts are preprints posted for independent checking. Neither has
completed external mathematical review. Submission to the proof-claim forum
on Erdős Problems does not certify correctness.

The arguments presented in the manuscripts are non-computational. Small
programs were used during development to test arithmetic and finite case
splits, but no program output is used as a premise in either proof.

## AI disclosure

AI use is described in [AI_DISCLOSURE.md](AI_DISCLOSURE.md). OpenAI GPT-5.6
Sol was used extensively during proof search, drafting, and internal checking.
OpenAI GPT-5 (Codex) was used for later source review and release checks. xAI
Grok 4.5 was used to critique an earlier version of the $r=5$ manuscript.

## Corrections

Please open a GitHub issue identifying the exact page, lemma, and claimed gap.
Corrections and revised versions will be recorded in this repository.
