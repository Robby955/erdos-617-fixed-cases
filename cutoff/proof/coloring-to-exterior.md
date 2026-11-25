# From an arbitrary coloring to the exterior rows

Robert Sneiderman and OpenAI GPT‑6.2 Astra · GitHub proof supplement · 25 November 2026

Fix any coloring of the edges of $K_{r^2+1}$ with $r$ colors, where $r\ge255\cdot2^{136}$. Lean now proves the common threshold of Appendix A directly from this input. The theorem either finds $r+1$ vertices missing a color or constructs the actual cliques and proves all three estimates in (4) on them. It chooses the target color, ordered rows, deletion history, representatives and threshold internally. [Theorem from the original coloring](ColoringWidth.lean) · [What the width estimates say](RowWidth.lean)

## The edge count that pays for the rows

Suppose the coloring has no missing-color witness and choose a sparsest color $J$. Write $s_i$ for the size of raw row $i$, $e_J$ for the number of target edges, $X$ for the target edges between different rows, and $\mu$ for the nontarget edges within the rows. Set $V=\sum_i(s_i-r)^2$. Counting the two ends of each edge gives

$$
2 e_J=\sum_i s_i(s_i-1)-2\mu+2X.
$$

At each pivot step the number of target edges to later rows is at least twice that row’s internal nontarget count. Each cross-row edge has one earlier endpoint, so summing gives $2\mu\le X$. Sparsity gives $2e_J\le r^3+r$. Finally $\sum_i(s_i-r)=1$, and each integer deviation $d$ satisfies $d^2\ge d$. Hence $V\ge1$ and

$$
2\mu\le X\le r^2-r+1-V.
$$

Every row of size $s_i>r$ consumes at least $(r-1)(s_i-r)$ nontarget edges, since each other color needs at least $s_i-r$ of them. This gives $\sum_i(s_i-r)_+\le r/2$. Together these counts prove the total unused allowance and the inter-row edge bound, including the variance rebate. [Original edge identity](RawEdgeIdentity.lean) · [Orientation at the pivots](PivotCross.lean) · [Three global budgets](GlobalRowBudgets.lean)

## Paying for a deletion

In the first stage delete a vertex with more than $r/4$ target neighbors in a qualifying foreign row. In the second stage delete a vertex of total live cross-row degree greater than $199r/400$. Lean constructs a finite deletion order and records a qualifying destination for every first-stage source. [Pruning construction](ConstructPruning.lean)

For a row of size $r+d$, take $z$ exterior vertices. The other colors need at least $(r-1)(d+z)$ edges in the union. If $U$ is the row’s unused allowance in edge units, there can be at most $U+(1+d)z+\binom z2$ target edges from the exterior vertices into the row. Apply this bound to the sources assigned to that destination. A qualifying row cannot support $\lfloor r/256\rfloor$ such sources. On the actual source set the same inequality charges at least $(61/250)r$ per source. This supplies the last input previously needed by the width theorem. [Exterior edge count](ExteriorRowEdges.lean) · [Destination cost](DestinationCost.lean) · [Proof from the original rows](ColoringWidth.lean)

## What happens outside the retained cliques

Let $h=s-1$ be the number of omitted rows. Call an exterior vertex low-attachment if it has at most $9r/(40s)$ target neighbors in each retained clique. These vertices have target independence number at most $h$. Indeed, $h+1$ independent exterior vertices would still leave at least $r/41$ compatible vertices per retained row. The per-row conflict count gives independent representatives across the rows, completing an independent set of size $r+1$. Lean also proves that the temporary restriction of each retained clique keeps at least $255r/256$ vertices. Each kept vertex has fewer than $7r/50$ target neighbors outside its original clique. [Counting independent representatives](CountingTransversal.lean) · [Exterior independence cap](OrdinaryRepresentatives.lean) · [Temporary restriction and the degree bound](OrdinaryTrim.lean)

The required shortage says that the number of low-attachment exterior vertices is strictly below $hr-3r/20$. If it fails, choose an auxiliary subset of size $hr+b$, taking at most $hr+1$ vertices. Thus $-3r/20\le b\le1$. Partition its target graph into $h$ pivot rows. Write $a_i$ for their sizes and $X_a$ for the number of target edges between them. [The actual induced coloring](AuxiliaryColoring.lean)

For each nontarget color on the auxiliary subset, construct its own pivot partition with $r$ rows. The two integer inequalities $(t-h)(t-h+1)\ge0$ and $(t-h)(t-h-1)\ge0$ bound each row’s pair count $t(t-1)$. Sum these inequalities and subtract the edge floors for the $r-1$ nontarget colors from the complete graph’s edge count. The target pivot estimate gives

$$
X_a+\sum_{i=1}^{h}(a_i-r)^2
\le rh(h-1)+b^2+\min\{2(h-1)b,\;2(h-r)b\}.
$$

The last term is nonpositive for either sign of $b$. With $u_i=(1-a_i/r)_+$ and the width bound on $h^2/r$, this yields

$$
\frac{X_a}{r^2}+\sum_i u_i^2\le (3/20)^2+2^{-20}.
$$

The manuscript used the larger right side $(1+1/799)(3/20)^2+3\cdot2^{-20}$ for the joint bound. Using both integer edge floors removes that loss. On these same rows the sum of the underfull vertex counts is at most $-b+X_a/(2(r-1))$. [Signed and normalized square estimates](AuxiliaryMoments.lean) · [Linear deficit estimate](AuxiliaryDeficit.lean) · [Combined alternative](ExteriorAuxiliary.lean)

## Why all the surviving auxiliary rows are cliques

Prune an auxiliary vertex whenever it has more than $43r/200$ cross-row neighbors still present. Each deletion spends fresh edges. If it deletes $zr$ vertices, at most $X_a-(43/200)zr^2$ cross edges survive. For one fixed row put $u=(1-a_i/r)_+$ and $x=X_a/r^2$. Then $x+u^2\le \xi=(3/20)^2+2^{-20}$ and $(43/200)z\le x$. Completing the square gives
$$
u+z\le \frac{\xi}{43/200}+\frac{43/200}{4}<\frac4{25}.
$$
Even if every deletion occurred in that row, at least $21r/25$ of its vertices survive. [Peeling on actual edges](AuxiliaryPeeling.lean) · [Row size after deletion](AuxiliaryRowFloor.lean)

Suppose two vertices of a surviving auxiliary row were nonadjacent. In every other row they would together exclude at most $2(43/200)r$ vertices, leaving at least $41r/100$ common nonneighbors. Each such row has at most $X_a$ conflicting pairs with the other rows. The inequality $4X_a<(2r/5)^2$ lets us choose one independent representative from each of them. Together with the two original vertices, that gives $h+1$ independent auxiliary vertices, contradicting the proved cap of $h$. All $h$ surviving rows are therefore cliques in the original target color. [Conflict pairs counted on unordered edges](SublistEdges.lean) · [Clique construction on the chosen auxiliary set](AuxiliaryCliques.lean)

The subsequent supplement proves the prescribed extensions, enlarges the cliques and sums the capacity inequalities to obtain the strict shortage. In §5 the graph derivation of the final signed inequality (5) remains open in Lean. [Strict shortage proof and verification](exterior-shortage.md) · [Final cut in the manuscript](weighted-width.md#5-the-five-width-bands-and-the-final-signed-cut)

## Replaying the proof

From the directory containing the pinned Lake environment, run

```sh
lake env python3 -B proof/replay_pruning_kernels.py coloring
lake env python3 -B proof/replay_pruning_kernels.py exterior
lake env python3 -B proof/replay_pruning_kernels.py cliques
```

The final command verifies the auxiliary clique construction and the theorem from an arbitrary coloring. The first command checks the arbitrary-coloring theorem through (4). The second checks the exterior independence cap, trim and auxiliary budgets. Each command starts from the source files, prints the axioms of the named declarations and sends one proof export to Lean’s kernel, Lean4Lean and Nanoda. Add `--lean-only` for a source compile and axiom audit. [Replay script](replay_pruning_kernels.py)

### Verification record, 25 November 2026

The three replays at local revision `58d9efc` accepted the exports below. Each named theorem uses only `propext`, `Classical.choice` and `Quot.sound`. Declaration totals include imported dependencies.

| Replay | Named theorems | Declarations | Export SHA-256 |
| --- | ---: | ---: | --- |
| `coloring` | 11 | 28,362 | `921e888d259ee2d93c3e3ed7f3af4ba43d9626ac633928b8025de959d17c07d1` |
| `exterior` | 13 | 28,480 | `7b93c38222c465ec1917845026ab047bb4f716874b68a42165fc7ca3243f6b99` |
| `cliques` | 8 | 28,556 | `b461729dbd271dda2df3c2958b544bc46492f6c1323c85adce9cd4fed70cae75` |
