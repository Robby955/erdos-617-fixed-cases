# An explicit cutoff for the Erdős–Gyárfás balanced-coloring conjecture

**Robert Sneiderman and OpenAI GPT-6.2 Astra** · GitHub edition · 24 November 2026

Color every edge of a complete graph with $r$ colors. Erdős and Gyárfás asked whether, on $r^2+1$ vertices, some $r+1$ vertices must miss one color. This manuscript proves that they must for every $r\ge 2^{144}$, and separately for $r=12$. The sharper working corollary lowers the cutoff to $255\cdot2^{136}$. Together the fixed-case and cutoff manuscripts leave $13\le r<255\cdot2^{136}$ open. [Corollary and exact check](proof/retained-width-corollary.md)

**[Two-page overview](github-overview.pdf)** · **[Full paper](github-paper.pdf)** · **[Twelve-color paper](proof/github-order-twelve.pdf)** · **[Cite the GitHub edition](CITATION.cff)**

The review edition carries Robert Sneiderman’s byline. Both editions give the same theorems and proofs. [Review paper](paper.pdf) · [Review overview](overview.pdf) · [Twelve-color review paper](proof/order-twelve.pdf) · [Review citation](CITATION-review.cff)

### How to check the result

| Result | Mathematical argument | Verification |
|---|---|---|
| Cutoff at $2^{144}$ | The proof compares the cost of discarding vertices with the cost of discarding their destination rows. The full paper includes the earlier combinatorial estimates and the signed-cut argument. [Width argument](proof/retained-width.md) · [Earlier estimates](proof/weighted-width.md) | Exact rational checks for five width comparisons and 1,280 signed-cut endpoints. Lean constructs one threshold satisfying all three row bounds in (4), for each of the five bands. [Python](proof/verify_retained_width.py) · [Lean width theorem](proof/CommonWidth.lean) |
| Twelve colors | Six exterior vertices would each have to use a different one of five rows. One row shared by two yields thirteen vertices missing a color. The resulting edge floor is 409 against a cap of 408. [Proof source](proof/order-twelve.md) · [Local hypotheses](proof/overfull-core.md#6-a-reduction-to-local-statements-for-any-hue) | One program minimizes the excess spent, another maximizes the number of vertices a given budget can accommodate. Lean checks the missing-color witness once its row and two vertices are supplied. [First replay](proof/verify_order_twelve.py) · [Second replay](proof/replay_order_twelve.py) · [Lean](proof/OrderTwelveCollision.lean) |

From this directory, the following commands run the main exact checks with Python 3.10 or newer. The scripts use the standard library.

```sh
cd proof
python3 -B verify_retained_width.py
python3 -B verify_four_row_descent.py 12
python3 -B verify_order_twelve.py
python3 -B replay_order_twelve.py
```

The first command reports five positive width margins and a minimum signed-cut margin greater than 0.0003327. In the four-row census at twelve, every surviving quartet has weight at least four. The two final commands test 91 profiles, or 434 choices when row labels of matching weight are retained, and exclude all eleven possible stops. The proof at twelve also uses the two- and three-row lemmas in the [supporting note](proof/overfull-core.md).

To check the Lean components, run the following from the directory containing this README. The toolchain and the mathlib commit are pinned.

```sh
lake exe cache get
lake env lean proof/RowExtraction.lean
lake env lean proof/PruningOverlap.lean
lake env python3 -B proof/replay_pruning_kernels.py oversampling --lean-only
lake env lean proof/OrderTwelveCollision.lean
```

The November 25 Lean supplement starts from the original coloring at the working cutoff $255\cdot2^{136}$. It constructs the retained cliques, proves the strict exterior shortage and samples the outside vertices. On every supported sample the repaired graph has independence number at most $s-1$. Lean bounds the repair cost and proves the tested-cut inequality using the same target edges between cliques. Lean proves both oversampling estimates for those same rows. It also proves a single-row cut bound and controls the moderate senders assigned to each destination. The combined strong- and moderate-sender capacity inequality and the final numerical contradiction remain to be formalized. [Oversampling and verification](proof/oversampling.md) · [Precise cutoff statement](proof/CutoffStatement.lean)

Run `lake env python3 -B proof/replay_pruning_kernels.py sampling` for the original-coloring sampling theorem and `lake env python3 -B proof/replay_pruning_kernels.py cut` for the repair, tested cut and edge recovery. Use `loads` for the manuscript row test and `oversampling` for both sampling bounds and the moderate destinations. These commands build the source and replay the export with Lean’s kernel, Lean4Lean and Nanoda. [Replay script](proof/replay_pruning_kernels.py)

### Reading the cutoff proof

1. **Start with the coloring on page 11.** Fix a color with the fewest edges and call it the target. Among the remaining vertices choose a pivot with the most nontarget neighbors. Those neighbors form the set left for later rows. The other vertices form the current row. Every vertex in the row has at most as many nontarget neighbors as the pivot. Subtract its nontarget neighbors in the later set from both sides. Its nontarget neighbors inside the row are then bounded by its target neighbors in the later set. Sum over the row. Each internal nontarget edge is counted twice and each outgoing target edge once. Lean iterates this rule until it covers every vertex and proves the outgoing-edge inequality on each row. [Ordered raw rows](proof/OrderedRows.lean) [Appendix A, §1](proof/weighted-width.md#1-count-the-unused-part-of-the-stability-bound) · [Lean proof](proof/RowExtraction.lean) · [Füredi, equation (4)](https://arxiv.org/pdf/1501.03129#page=3)

   On four vertices, let the only nontarget edges be *ab* and *cd*. With pivot *a*, only *b* is left for later. The internal edge *cd* has two ends, and its two outgoing target edges are *cb* and *db*. This attains equality.

2. **Follow the same edges through pruning on pages 11–12, then turn to pages 3–5.** A deleted vertex in a chosen oversized row can spend its quota on outgoing target edges. Its row is too large to receive a first-stage destination charge. Lean proves that the source quotas cover every duplicated incidence. Each chosen independent pair costs at least one missing representative across the remaining lists. This gives the deficit estimate on the same cliques whose edges enter the incidence count. Reserving the heaviest rows then gives one threshold for the two individual bounds and the square-sum bound. [Counting representatives](proof/packing-lists.md) [Pruning overlap and worked example](proof/pruning-overlap.md) · [Width integral](proof/weighted-width.md#3-integrate-both-endpoints-of-the-width-test) · [Cutoff chapter](proof/retained-width.md) · [Lean width theorem](proof/CommonWidth.lean)
3. **Read the contradiction on pages 13–16.** If *h* rows were omitted, Appendix A, §4 shows that fewer than *hr* − 3*r*/20 exterior vertices have small target degree into every retained row. Section 5 uses that shortage to derive inequality (5), which requires a nonpositive value. Concavity and the exact computation give a strictly positive value throughout the allowed interval. A referee can check how the graph forces (5) before replaying its 1,280 endpoints. [Shortage and signed cut](proof/weighted-width.md#4-a-shortage-of-at-least-3r20) · [Two uses of the cut](proof/cutoff-190.md#4-recover-the-cost-of-uniquely-assigned-senders) · [Exact replay](proof/verify_retained_width.py)

### Earlier work

Erdős and Gyárfás proved the cases $r=3,4$. Sneiderman released proof manuscripts for five through eight on 20 July 2026 and for nine on 21 July. Kara credits Sneiderman's five-color proof in his verification. [Original paper](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf) · [July 20 release](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/fixed-r5-r8-2026-07-20) · [July 21 release](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/fixed-r9-2026-07-21) · [Five-color verification](https://github.com/RamazanKara/erdos-617-r5-formal-verification)

Terpstra Research released arguments at ten and eleven in August. The accompanying working notes give this project's separate proofs. [Terpstra release](https://github.com/terpstra-research/erdos-617-r10-r11/releases/tag/v0.1.1) · [Ten, Theorem 21](proof/overfull-core.md#12-order-ten) · [Eleven](proof/midpoint-row-excess.md)

Robert Sneiderman directed the research and handles correspondence. OpenAI GPT-6.2 Astra, the AI model used in Codex, contributed to proof search, calculations, Lean proofs and drafting. Fable contributed fixed-row arguments and checked earlier steps.

### Rebuilding the PDFs

With Pandoc and XeLaTeX installed, run these commands from this directory. Omit `--edition github` to build the review edition. [Shared manuscript source](paper.md)

```sh
python3 build_paper.py paper --edition github
python3 build_paper.py overview --edition github
python3 build_paper.py twelve --edition github
```
