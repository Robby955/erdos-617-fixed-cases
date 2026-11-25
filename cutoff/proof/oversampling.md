# Sampling the same coloring twice

Let $r\ge255\cdot2^{136}$. Start with an arbitrary $r$-edge-coloring on $r^2+1$ vertices. Lean either finds $r+1$ vertices missing a color or constructs retained cliques, all from this coloring, for which both oversampling estimates in Appendix A, §5 hold. The second alternative still has to be excluded to conclude the cutoff theorem. The precise implication is the last theorem in [TwoOversamplingPasses.lean](TwoOversamplingPasses.lean).

## Why a larger sample cannot cost too many repairs

Fix the random starting positions of the arcs in each row. Whether the unordered pair $\{x,y\}$ is a repair edge now depends only on the states of $x$ and $y$. This includes repairs that can arise for more than one reason. If the sampling probability rises from $p$ to $q$, where $p\le q\le k p$ and $k\ge1$, each endpoint state has at most $k$ times its old probability. Independence at distinct endpoints bounds the probability of the pair by $k^2$ times its old value. Sum its indicator once per unordered pair and average over the same arc starts. For $q\le2p$, the enlarged sample therefore has at most four times the base sample's expected number of distinct repair edges. The base bound keeps its full quadratic subtraction. [Two-coordinate comparison](PairThinning.lean) · [Repair edges from the coloring](RepairThinning.lean)

Let $s$ be the chosen scale, $\Delta$ the exterior shortage and $A$ the sum of the sender eligibility probabilities. If $A>\Delta$, increase the expected number marked from $\Delta$ to $\Delta+z$, where $z=\min(A-\Delta,\Delta/128,r/16)$. Applying the edge lower bound for every color to the enlarged sample gives expected repair cost at least $rz/2-rs^2$. Consequently $rz\le8B+2rs^2$, where $B$ bounds the actual base repair cost. The Lean theorem also permits $k=129/128$, since $z\le\Delta/128$ gives $(\Delta+z)/A\le(129/128)(\Delta/A)$. This tightens the coefficient of $B$ from $8$ to $2(129/128)^2=16641/8192$ on this step. The current width calculation still uses $8$. The width-band estimates make both artificial caps strictly too large. This leaves a bound on the full positive part of $A-\Delta$, including the case $A\le\Delta$. [Enlarged-sample floor](OversamplingFloor.lean) · [Combining the comparisons](OversamplingPass.lean) · [Removing the caps](EligibilitySurplus.lean)

## Using the actual destinations a second time

Write $\rho=9/(40s)$, $x_i=1-|C_i|/r$ and $N_i$ for the number of vertices whose unique strong destination is row $i$. The first estimate uses $\sum_iN_ix_i\le 2\kappa\rho r$. For each such vertex $y$ let $q_y$ be the fraction of its destination adjacent to it in the target color. The sender calculation pays at least $37\rho r(1-q_y)$ for that vertex. Distinct unique-destination groups are disjoint, so the first estimate bounds the sum of these actual nonneighbor fractions. Substitution gives the second weight $W_1$ and a second surplus bound, on the same rows. The parameters used by the exact checker occur explicitly in the definition of `TwoPassBounds`. [Base repair budget](OversamplingBudget.lean) · [Charging the nonneighbors](RetryDeficit.lean) · [Both passes](TwoOversamplingPasses.lean)

## The remaining capacity inequality

Assign each moderate sender in advance to a row where it has more than $\rho r$ target neighbors. If $v_i$ is the expected number marked at destination $i$ and $m$ is the expected number of all marked senders, a one-row cut of at most $\epsilon(\rho r)^2$ implies
$$
\sum_i v_i^2\le\epsilon\rho r\,m .
$$
Lean proves the one-row cut bound, the disjoint assignment and this implication. [Single-row cut](OneRowCapacity.lean) · [Assignment and square-sum bound](ModerateDestinations.lean)

The next graph inequality combines the strong assignments with the marked moderate vertices at each destination. With $D=\sum_i(r-|C_i|)$, $\sigma=\sum_i(r-|C_i|)^2$ and $L_0=D+\Delta+1-A$, its required form is
$$
rL_0+\rho r\,m\le rD+\tfrac{501}{1000}\sigma+\sum_i v_i^2+m .
$$
Apply the clique capacity to the union in each sample, bound the variance of the moderate count by its mean, and evaluate the strong-row inequality at $v_i$. The one-row cuts alone do not establish this joint inequality. After it, the formal proof must connect both sampling bounds to inequality (5) and certify positivity throughout the width intervals. [Capacity argument, §3](cutoff-289.md#3-using-the-labels-of-edges-into-a-row) · [Final signed expression](weighted-width.md#5-the-five-width-bands-and-the-final-signed-cut) · [Exact rational checker](verify_retained_width.py)

## Verification

Run from the directory containing the pinned Lake manifest.

~~~sh
lake env python3 -B proof/replay_pruning_kernels.py oversampling
python3 -B proof/verify_retained_width.py
~~~

On 25 November 2026, Lean’s kernel, Lean4Lean and Nanoda accepted the export of 21 named theorems and their dependencies (30,676 declarations). Every named theorem uses only `propext`, `Classical.choice` and `Quot.sound`. Export SHA-256 `533b7f7ae228c6ea73a7efe95ec0e7431edb127b60d7401dfe61ded1bfe4f150`. The exact rational replay passed all 1,280 signed-cut endpoints, with minimum 0.000332766 to nine decimal places. The lower bound for the reduced width margin was 0.000153163 to nine decimal places.
