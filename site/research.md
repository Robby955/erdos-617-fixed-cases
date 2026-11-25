# Erdős Problem 617

Robert Sneiderman · 25 November 2026

Color the edges of the complete graph on `r² + 1` vertices with `r` colors. The conjecture asks for `r + 1` vertices whose induced edges miss a color, for every integer `r ≥ 3`.

## Results

| Claim | Source and status |
| --- | --- |
| Every `r ≥ 2^144` | [November paper](https://erdos617.com/paper.pdf). Theorem A. |
| Every `r ≥ 255 × 2^136` | [Sharper cutoff](https://github.com/Robby955/erdos-617-fixed-cases/releases/download/cutoff-2026-11-25-v3/corollary.pdf). Appendix I proves the sharper bound, which Lean verifies for arbitrary colorings. |
| Individual cases `3 ≤ r ≤ 12` | See the [dated history](index.html#history). The November paper includes the separate twelve-color argument. |
| Every `r ≥ 3` | Open. The range left by the manuscripts is `13 ≤ r < 255 × 2^136`. |

## Reproduce the calculations

[Download the paper, Lean sources and checkers](https://github.com/Robby955/erdos-617-fixed-cases/releases/download/cutoff-2026-11-25-v3/lean-and-paper.zip). Unzip it and change into the directory containing `lean-toolchain` and `lakefile.toml`. The ZIP contains the source and the pinned dependency manifest. Lake fetches the dependencies on the first build. Follow README.md for the environment setup.

```sh
python3 -B proof/verify_retained_width.py
lake env python3 -B proof/replay_pruning_kernels.py cutoff --lean-only
```

The Python check covers 1,280 signed-cut endpoints. It reports a reduced width margin exceeding 0.00015316. Lean uses a separate 45-cell certificate and proves positivity throughout each cell. The Lean command builds the complete cutoff proof in a fresh directory and prints the axioms of the final theorems. With `leanexport`, `leanchecker`, `lean4lean` and `nanoda_bin` on the Lake environment's PATH, remove `--lean-only` to export and replay those proofs.

[Tagged release and download checksums](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/cutoff-2026-11-25-v3) · [Lean theorem and verification record](https://github.com/Robby955/erdos-617-fixed-cases/blob/cutoff-2026-11-25-v3/cutoff/proof/formal-cutoff.md).

## Open questions and proof sources

- **Replay the cutoff in Lean.** Start at `proof/BalancedColoringCutoff.lean`. The theorem `erdos_617_of_ge_cutoff` takes any coloring of unordered pairs and produces the missing-color set. The distinct-vertex condition makes the values on diagonals irrelevant. The full proof and replay instructions are in `proof/formal-cutoff.md`.
- **Lower the cutoff.** Read `proof/retained-width-corollary.md`, `proof/retained-width.md` and `proof/verify_retained_width.py`. At `2^143` the first-band sufficient comparison has margin at most −0.17125 at an allowed boundary point. Excluding that point using the original coloring, or improving the comparison there, would address a specific obstruction. The failed inequality supplies no counterexample.
- **Close the finite range.** The first remaining order on these manuscripts is thirteen. An argument uniform in the number of remaining rows could resolve many orders at once. At each step reconstruct the claimed edges on the same global coloring. Counts on unrelated hypothetical row systems need not be compatible.

## Report a smaller cutoff

[Open a GitHub issue](https://github.com/Robby955/erdos-617-fixed-cases/issues/new?title=Proposed+cutoff) with the exact proposed cutoff, the lemma or inequality that changes, and a proof or replay command at a specific commit. Credit the people and tools that found the improvement. An issue records a proposal. The dated releases record verified bounds and preserve the earlier proofs.

Independent mathematical review of the paper is pending.
