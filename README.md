# Fixed-case proof claims for Erdős Problem 617

This repository contains four fixed-parameter proof claims related to
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

- **$r=7$:** Every seven-coloring of the edges of $K_{50}$ has eight vertices
  whose induced $K_8$ omits at least one color.

- **$r=8$:** Every eight-coloring of the edges of $K_{65}$ has nine vertices
  whose induced $K_9$ omits at least one color.

[Combined $r=7,8$ PDF](r7-r8/erdos-617-r7-r8.pdf) |
[TeX source](r7-r8/main.tex) |
[Replay instructions](r7-r8/README.md)

These claims address only $r=5,6,7,8$. They do not settle the statement for
every $r\geq3$.

## Review status

The manuscripts are preprints posted for independent checking. None has
completed external mathematical review. Submission to the proof-claim forum
on Erdős Problems does not certify correctness.

The $r=5,6$ arguments are non-computational. Small programs were used during
development, but their output is not a premise in either proof. The $r=7,8$
arguments are computer-assisted. Their finite premises, semantic checkers,
manifests, replay commands, and proof artifacts are included under
[`r7-r8/`](r7-r8/).

## AI disclosure

AI use is described in [AI_DISCLOSURE.md](AI_DISCLOSURE.md). OpenAI GPT-5.6
Sol was used extensively during proof search, drafting, program development,
and internal checking. OpenAI GPT-5 (Codex) was used for later source review,
replay packaging, and release checks. xAI Grok 4.5 was used to critique an
earlier version of each fixed-case manuscript.

## Corrections

Please open a GitHub issue identifying the exact page, lemma, and claimed gap.
Corrections and revised versions will be recorded in this repository.
