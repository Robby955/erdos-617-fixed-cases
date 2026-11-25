# Why the row tests are valid

Fix the sparsest color and the retained cliques from the width theorem. Let $C_i$ be one retained clique, $s$ the scale, $r$ the number of colors and $\rho=9/(40s)$. The row test depends on $n_i$, the expected number of vertices whose load into $C_i$ exceeds $\rho r$, and $N_i$, the number of senders with a unique strong destination at $C_i$.

## Count both kinds of load on the original edges

First set aside vertices in the original row outside $C_i$, and first-stage sources recorded with destination $i$. Each such vertex can contribute at most one to $n_i$. For every remaining vertex, charge a positive load to at least $\rho r$ target-edge incidences into $C_i$. A direct load has its far endpoint outside every retained clique. A load through a foreign representative has its far endpoint in another retained clique. These incidences are disjoint. The unique-sender bound and the retained-clique size floor keep the expected multiplicity at each foreign endpoint at most one. [Incidence disjointness](HeavyLoadIncidence.lean) · [Multiplicity and per-row bound](HeavyLoadBound.lean)

Write $x_i=1-|C_i|/r$, $u_i=\max(|R_i|/r-1,0)$ for the original row surplus, $v_i$ for the number of first-stage sources destined for $i$ divided by $r$, and $y_i$ for unrecorded incidences at $C_i$ divided by $r^2$. The resulting bounds are

$$
n_i/r\le x_i+u_i+v_i+y_i/\rho,\qquad N_i/r\le 2x_i.
$$

The coefficient of $y_i/\rho$ is exactly one. Sum the destination counts before using a uniform upper bound. Each recorded first-stage source then enters at most once. The joint budgets give $\sum_i(x_i+u_i+v_i)\le7$, $2\sum_i x_i\le9$ and $\sum_i y_i\le Y_0$, where $Y_0=2-p_1/2-(199/400)p_2$ and $p_1,p_2$ are the two deletion rates. Since $s\ge1120$, this gives $\sum_i n_i/(sr)\le Y_0/(9/40)+7/1120$. [Retained-row budgets and total count](HeavyLoadTotals.lean)

## Substitute the manuscript's probabilities

For a width endpoint, let $A$ bound $sy_i$ and $X$ bound $sx_i$. The old, slightly larger expression for the maximum height still applies. With the paper's coefficients $a,b$, the inequality $\pi_i=(a n_i+b N_i)/r\le 1$ now follows for every retained row. Each $\pi_i$ is nonnegative. The independent row test therefore exists for every admissible sender-thinning probability. Summing gives a bound on the expected number of tested rows. The specialized signed-cut theorem also evaluates the second falling moment of the number of omitted and tested rows, including its diagonal correction. [Endpoint coefficients](HeavyLoadTests.lean) · [Expected number and signed cut](ManuscriptRowTest.lean)

The oversampling supplement now compares distinct repair edges directly at two sampling probabilities and derives both estimates with the quadratic correction. It also records the remaining combined capacity inequality. [Oversampling proof and replay](oversampling.md)

Run the exact endpoint check and kernel replay from the directory containing `lakefile.toml`.

```sh
python3 -B proof/verify_retained_width.py
lake env python3 -B proof/replay_pruning_kernels.py loads
```

On 25 November 2026 the native Lean checker, Lean4Lean and Nanoda accepted the export of nine named results and their dependencies (18,708 declarations). The axiom audit found only `propext`, `Classical.choice` and `Quot.sound`. The export’s SHA-256 was `1576ea505c3ec74e110a224145757496fe400f475ecff4df073d4221c90bb103`.
