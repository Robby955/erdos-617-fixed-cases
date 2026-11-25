# The Erdős–Gyárfás balanced-coloring conjecture

## November cutoff and twelve-color paper

**Robert Sneiderman and OpenAI GPT-6.2 Astra** · GitHub edition · 25 November 2026

Erdős and Gyárfás asked whether every edge coloring of $K_{r^2+1}$ with $r$ colors contains $r+1$ vertices missing a color. The November preprint gives an explicit cutoff of $2^{144}$ and a separate proof at twelve colors. The working corollary sharpens the cutoff to $255\cdot2^{136}$ by using the positive margins in all five width comparisons. [Corollary](cutoff/proof/retained-width-corollary.md) [Original conjecture](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf)

**[Research site](https://erdos617.vercel.app)** · **[Versioned release](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/cutoff-2026-11-25)** · **[Two-page overview](cutoff/github-overview.pdf)** · **[Full paper](cutoff/github-paper.pdf)** · **[Proof sources and verification guide](cutoff/README.md)**

The Lean proof starts with an arbitrary coloring at the improved cutoff and produces the missing-color witness. It also proves that only finitely many orders can be counterexamples. [Theorem in Lean](cutoff/proof/BalancedColoringCutoff.lean) · [Proof and independent-kernel replay instructions](cutoff/proof/formal-cutoff.md)

## July fixed-case releases

Robert Sneiderman’s July papers cover $r=5,6,7,8,9$. [Release for five through eight](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/fixed-r5-r8-2026-07-20) · [Release for nine](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/fixed-r9-2026-07-21)

- **r = 5:** Every five-coloring of the edges of K₂₆ has six vertices
  whose induced K₆ omits at least one color. Equivalently,
  R(6; 5, 4) = 26.
  [PDF](r5/erdos-617-r5.pdf) | [TeX source](r5/main.tex)

- **r = 6:** Every six-coloring of the edges of K₃₇ has seven vertices
  whose induced K₇ omits at least one color.
  [PDF](r6/erdos-617-r6.pdf) | [TeX source](r6/main.tex)

- **r = 7:** Every seven-coloring of the edges of K₅₀ has eight vertices
  whose induced K₈ omits at least one color.

- **r = 8:** Every eight-coloring of the edges of K₆₅ has nine vertices
  whose induced K₉ omits at least one color.

[Combined r = 7, 8 PDF](r7-r8/erdos-617-r7-r8.pdf) |
[TeX source](r7-r8/main.tex) |
[Replay instructions](r7-r8/README.md)

- **r = 9:** Every nine-coloring of the edges of K₈₂ has ten vertices
  whose induced K₁₀ omits at least one color.

[r = 9 PDF](r9/erdos-617-r9.pdf) |
[TeX source](r9/main.tex) |
[Replay instructions](r9/README.md)

## Review of the July manuscripts

The manuscripts are preprints posted for independent checking. None has
completed external mathematical review. Submission to the proof-claim forum
on Erdős Problems does not certify correctness.

The r = 5, 6 arguments are non-computational. Small programs were used during
development, but their output is not a premise in either proof. The r = 7, 8,
9 arguments are computer-assisted. Their finite premises, semantic checkers,
manifests, replay commands, and proof artifacts are included under
[`r7-r8/`](r7-r8/) and [`r9/`](r9/).

## AI disclosure

Robert Sneiderman directed the research. OpenAI GPT-6.2 Astra, an AI model used in Codex, contributed to the November proof search, drafting, exact checks and Lean proofs. Fable contributed fixed-row arguments and internal reviews. The July papers document their earlier model assistance separately. [Contribution statement](AI_DISCLOSURE.md)

## Corrections

Please open a GitHub issue identifying the exact page, lemma, and claimed gap.
Corrections and revised versions will be recorded in this repository.

## Consolidated draft, r = 5 to 9

`erdos-617-r5-r9-consolidated-DRAFT.pdf` combines the five fixed cases into
one manuscript. It is a DRAFT, not a submission and not a published paper.
It states no result that the four case papers in this repository do not
already state, and it has not been externally reviewed. The per-case papers
and their replay packages remain the authoritative artifacts.
