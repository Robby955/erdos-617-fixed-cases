# An explicit cutoff for the Erdős–Gyárfás balanced-coloring conjecture

Robert Sneiderman · Preprint for independent review · 24 November 2026

Color every edge of a complete graph with $r$ colors. Erdős and Gyárfás asked whether, on $r^2+1$ vertices, some $r+1$ vertices must miss one color. This manuscript proves that they must for every $r\ge 2^{144}$, and separately for $r=12$. With the fixed cases through eleven, the only possible exceptions have $13\le r<2^{144}$.

**[Read the overview](overview.pdf)** · **[Download the full paper](paper.pdf)** · **[Read the twelve-color proof](proof/order-twelve.md)**

### How to check the result

| Result | Mathematical argument | Verification |
|---|---|---|
| Cutoff at $2^{144}$ | The proof compares the cost of discarding vertices with the cost of discarding their destination rows. The full paper includes the earlier combinatorial estimates and the signed-cut argument. [Width argument](proof/retained-width.md) · [Earlier estimates](proof/weighted-width.md) | Exact rational checks for five width comparisons and 1,280 signed-cut endpoints. A Lean theorem covers the five comparisons for all feasible real parameters. [Python](proof/verify_retained_width.py) · [Lean](proof/RetainedWidth.lean) |
| Twelve colors | Six exterior vertices would each have to use a different one of five rows. One row shared by two yields thirteen vertices missing a color. The resulting edge floor is 409 against a cap of 408. [Paper](proof/order-twelve.pdf) · [Local hypotheses](proof/overfull-core.md#6-a-reduction-to-local-statements-for-any-hue) | One program minimizes the excess spent, another maximizes the number of vertices a given budget can accommodate. Lean checks the missing-color witness once its row and two vertices are supplied. [First replay](proof/verify_order_twelve.py) · [Second replay](proof/replay_order_twelve.py) · [Lean](proof/OrderTwelveCollision.lean) |

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
lake env lean proof/RetainedWidth.lean
lake env lean proof/OrderTwelveCollision.lean
```

The main declarations are `Erdos617.RetainedWidth.width_for_every_pruning_pair` and `Erdos617.OrderTwelve.thirteen_vertex_witness`. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`. The extraction from an arbitrary coloring, the integral estimate, and the full fixed-order reduction are in the mathematical manuscript. External mathematical review of both complete arguments is pending.

### Earlier work

Erdős and Gyárfás proved the cases $r=3,4$. Sneiderman released proof manuscripts for five through eight on 20 July 2026 and for nine on 21 July. Kara credits Sneiderman's five-color proof in his verification. [Original paper](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf) · [July 20 release](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/fixed-r5-r8-2026-07-20) · [July 21 release](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/fixed-r9-2026-07-21) · [Five-color verification](https://github.com/RamazanKara/erdos-617-r5-formal-verification)

Terpstra Research released arguments at ten and eleven in August. The accompanying working notes give this project's separate proofs. [Terpstra release](https://github.com/terpstra-research/erdos-617-r10-r11/releases/tag/v0.1.1) · [Ten, Theorem 21](proof/overfull-core.md#12-order-ten) · [Eleven](proof/midpoint-row-excess.md)

The first two pages of the paper give the contribution statement, including the roles of Astra and Fable. To rebuild the PDFs, install Pandoc and XeLaTeX and run `python3 build_paper.py paper`, `python3 build_paper.py overview`, and `python3 build_paper.py twelve`. [Manuscript source](paper.md) · [Citation](CITATION.cff)
