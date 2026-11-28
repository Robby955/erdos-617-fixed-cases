# The cutoff theorem in Lean

For every integer $r\ge255\cdot2^{136}$, color the edges of the complete graph on $r^2+1$ vertices with $r$ colors. There are $r+1$ vertices whose induced edges miss a color. The theorem accepts an arbitrary coloring. It has no hypothesis about a packing, a sampling distribution or the outcome of a numerical test. [End-to-end proof](BalancedColoringCutoff.lean)

The 27 November extension proves the cutoff at $2^{143}$. [Third pruning pass, theorem and replay](third-pruning.md)

## Theorem statement

The theorem **erdos_617_of_ge_cutoff** expresses the conclusion using a coloring of unordered vertex pairs. The comparison only uses distinct vertices. This matches the public Formal Conjectures statement after restricting the number of colors to the proved range. **balancedColoringAt_of_ge_reduced_cutoff** uses the loop-free edge type in this project. **paper_cutoff** gives the manuscript's simpler power-of-two bound, and **finite_counterexample_orders** proves that the set of possible exceptional orders is finite. [Lean statements](BalancedColoringCutoff.lean) · [Original conjecture, p. 80](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf#page=2) · [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/6fbb54f24ccc2e64dcfaffc28c58950e377110d2/FormalConjectures/ErdosProblems/617.lean#L42-L46)

With the improved lower bound on the number of colors, the Lean theorem directly discharges the pinned Formal Conjectures statement with its original vertex type, edge coloring and conclusion.

## The signed-cut inequality

1. Assume every set of $r+1$ vertices contains all colors. The width and exterior arguments select cliques and find a shortage of more than $3r/20$ exterior vertices with low attachment. Both sampling passes hold for those same cliques. [Exterior shortage](ExteriorShortage.lean) · [Oversampling](oversampling.md)
2. At each destination, combine the strongly attached vertices with the marked, moderately attached vertices before bounding the edges into the clique. Write $v_i$ for the expected moderate count at this row. The fluctuation of the actual count has mean zero and variance at most $v_i$. Its quadratic and linear costs together leave at most $v_i^2+v_i$. The rows partition the moderate senders. The retry charge pays for each mark outside that partition, including the case of a unique strong destination. Summing proves the combined capacity inequality. [Row bound and sum](MixedSenderCapacity.lean)
3. The one-row cut controls $\sum_i v_i^2$. The second sampling pass controls the eligible mass above the shortage. Substitution forces the manuscript's signed expression (5) to be nonpositive at a specific normalized shortage $l$, provided the one-row coefficient is at most one. [Inequality from the coloring](FinalSignedCut.lean)
4. Within each width cell, the one-row coefficient is convex in $l$ and the signed expression is concave. Exactly computed endpoint comparisons make the coefficient less than one and the signed expression strictly positive throughout the interval. This rules out the $l$ supplied by the coloring. [Interpolation proof](SignedCutInterval.lean) · [Exact rational computation](CutoffCells.lean) · [Transfer to the real parameters](CertifiedWidthCell.lean)

The Lean certificate uses five bands and nine closed width intervals per band. In units of $1/128$, their boundaries are $0,64,72,80,96,112,120,124,126,128$. The proof places every selected real width in at least one interval and bounds $w(1-w)$ even when its maximum occurs at $1/2$. The 90 endpoint tests are evaluated by Lean's kernel using exact rationals. The paper's separate Python checker uses 1,280 endpoints on a finer subdivision. [Width cover and real bounds](CertifiedWidthCell.lean) · [Paper's checker](verify_retained_width.py)

## Verification commands

From the package directory containing **lean-toolchain**, install the pinned Lean toolchain through elan, then run

~~~sh
lake exe cache get
lake env python3 -B proof/replay_pruning_kernels.py cutoff --lean-only
~~~

This builds the cutoff sources in dependency order in a fresh directory and prints the axioms used by the final theorems. The project pins Lean 4.35.0 and mathlib commit **56a005855ea17e0b0958f73ec801ae140b0a1679**.

For the additional kernel replays, put **leanexport**, **leanchecker**, **lean4lean** and **nanoda_bin** on the Lake environment's path. The replay script checks the same export in all three kernels. Nanoda permits only propositional extensionality, classical choice and quotient soundness. The Python endpoint comparison can be run separately.

~~~sh
lake env python3 -B proof/replay_pruning_kernels.py cutoff
python3 -B proof/verify_retained_width.py
~~~

The formal theorem covers the large-color cutoff. The fixed-order arguments in the same package have their own verification records. Independent mathematical review of the manuscript remains pending.

## Verification record, 25 November 2026

Lean’s kernel, Lean4Lean and Nanoda accepted the same export of the ten cutoff declarations and their transitive dependencies, covering 30,816 declarations. The SHA-256 of the export is `c95492f69f8ff610a7413e040835c088c66a4a5e70f56a3b2171a45ad6735264`. Each named theorem uses only `propext`, `Classical.choice` and `Quot.sound`. All 115 modules in the cutoff replay compiled from a clean source snapshot. The five additional Lean files for earlier results compiled separately. All nine dependency revisions matched the pinned Lake manifest.
