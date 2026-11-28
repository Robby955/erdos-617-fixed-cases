# Erdős Problem 617

Robert Sneiderman · 27 November 2026

Color the edges of the complete graph on `r² + 1` vertices with `r` colors. The conjecture asks for `r + 1` vertices whose induced edges miss a color, for every integer `r ≥ 3`.

## Results

| Claim | Source and status |
| --- | --- |
| Every `r ≥ 2^143` | [Theorem A and Appendix J](https://erdos617.com/paper.pdf). The three kernels accepted the proof from an arbitrary coloring. |
| Individual cases `3 ≤ r ≤ 12` | See the [dated history](index.html#history). The November paper includes the separate twelve-color argument. |
| Every `r ≥ 3` | Open. The range left by the manuscripts is `13 ≤ r < 2^143`. |

## Reproduce the calculations

[Download the paper, Lean sources and checkers](https://github.com/Robby955/erdos-617-fixed-cases/releases/download/cutoff-2026-11-27/lean-and-paper.zip). Unzip it and change into the directory containing `lean-toolchain` and `lakefile.toml`. The ZIP contains the source and the pinned dependency manifest. Lake fetches the dependencies on the first build. Follow README.md for the environment setup.

```sh
python3 -B proof/verify_third_pruning.py
lake env python3 -B proof/replay_pruning_kernels.py cutoff-143 --lean-only
```

The rational subdivision checks 1,489 terminal boxes. The Lean command builds the complete cutoff proof in a fresh directory and prints the axioms of the final theorems. With `leanexport`, `leanchecker`, `lean4lean` and `nanoda_bin` on the Lake environment's PATH, remove `--lean-only` to export and replay those proofs.

[Tagged release and download checksums](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/cutoff-2026-11-27) · [Lean theorem and verification record](https://github.com/Robby955/erdos-617-fixed-cases/blob/cutoff-2026-11-27/cutoff/proof/third-pruning.md).

## Open questions and proof sources

- **Replay the cutoff in Lean.** The theorem `erdos_617_of_ge_two_pow_143` in `proof/ThirdPruningCutoff.lean` takes an arbitrary coloring of unordered pairs and produces a missing-color set of the required size. The release includes the three-kernel verification record.
- **Lower the cutoff.** Appendix J gives the two cases to test at a smaller scale. For a surviving independent pair, check (4). When all surviving rows are cliques, use (5)–(8) to bound their missing internal edges. Both cases must also meet the final signed-cut comparison.
- **Close the finite range.** The first remaining order on these manuscripts is thirteen. An argument uniform in the number of remaining rows could resolve many orders at once. At each step reconstruct the claimed edges on the same global coloring. Counts on unrelated hypothetical row systems need not be compatible.

## Report a smaller cutoff

[Open a GitHub issue](https://github.com/Robby955/erdos-617-fixed-cases/issues/new?title=Proposed+cutoff) with the exact proposed cutoff, the lemma or inequality that changes, and a proof or replay command at a specific commit. Credit the people and tools that found the improvement. An issue records a proposal. The dated releases record verified bounds and preserve the earlier proofs.

Independent mathematical review of the paper is pending.
