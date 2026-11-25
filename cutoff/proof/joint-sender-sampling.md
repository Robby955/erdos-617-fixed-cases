# From the marked senders to the tested cut

Robert Sneiderman and OpenAI GPT‑6.2 Astra · GitHub proof supplement · 25 November 2026

Suppose an $r$-coloring of $K_{r^2+1}$ has every color on every $r+1$ vertices. At $r\ge255\cdot2^{136}$ the earlier Lean proof selects a sparsest color $J$, disjoint cliques $C_i$ of that color and a scale $s$. Write $h=s-1$ for the number of omitted rows. The exterior set $L$ consists of vertices with at most $\rho r$ neighbors of color $J$ in every retained row, where $\rho=9/(40s)$. Its shortage is $\Delta=hr-|L|>3r/20$. The following results concern those same cliques and vertices. [Entry from any coloring](ColoringSample.lean) · [The shortage](exterior-shortage.md)

## One trial per exterior vertex

Call a row strong for a sender if more than $r/2$ of its vertices are target neighbors. A sender with no strong row is eligible for an ordinary mark. A sender with a unique strong row draws a point in that row and may retry after drawing a neighbor. It becomes eligible upon drawing a nonneighbor. Senders with multiple strong rows stay unmarked. Keeping each eligible sender with probability $p$ defines a finite product law indexed by the original vertices. A sender’s mark and its own output remain one random variable. Distinct senders are sampled independently, including senders in the same row. [Trials and eligibility](ColoringSenderLaw.lean) · [Support of actual outputs](SenderSupport.lean)

Let $A$ be the total eligible mass before thinning, and $m$ the expected number of marks. At the strict shortage, $A>0$ and $p=\min(1,\Delta/A)$ gives $m=\min(A,\Delta)$. Put $W=L\cup\{\text{marked senders}\}$, $v=hr-|W|$ and $u=\Delta-m$. Then $\mathbb E v=u$ and $\mathbb E v^2\le u^2+m$. These two moment formulas also hold for every admissible thinning probability, including a trial whose mean exterior size exceeds $hr$. At the chosen thinning,
$$
0\le u\le\frac{501}{1000}\,\frac{4\beta^2w(1-w)}s\,r .
$$
[Eligibility budget](EligibleSenders.lean) · [Mark variance](SenderSampleMoments.lean) · [Moments of the actual vertex count](ColoringSample.lean)

## Repairing the sample

Two marked senders with the same strong row give one repair edge. Other repair edges prevent a representative from hitting an exterior point or a representative in another row. A second kind of repair controls how many neighbors can be lost in a row without a prescribed representative. Lay out each sender’s load above $\rho r$ as an arc on a circle of circumference $3r/4$. Scaling lengths by $40s$ puts every endpoint on a circle of exactly $30sr$ sites. Join senders whose arcs overlap in any row. Form one graph on $W$ by adding the union of these unordered pairs to the original target edges. [Representative edges](RepresentativeRepairs.lean) · [Arcs in one common sample](ArcRepairUnion.lean)

For every outcome of positive weight and every placement of the arcs, **the repaired graph has independence number at most $h$**. An independent $s$-set in it would allow its representatives to be fixed without conflict. In every remaining row, the disjoint excess arcs spend at most $3r/4$, and the $s$ baseline loads spend at most $9r/40$. The retained row floor leaves at least $r/41$ vertices, enough to choose compatible representatives in all these rows. This would give at least $r+1$ original vertices missing $J$. [Load bound from the stopping rule](LoadCap.lean) · [Completion across the rows](RepairedIndependence.lean) · [Independence of the repaired sample](SampleRepairGraph.lean)

For row $i$, let $E_i$ count in expectation the target edges from $W$ into $C_i$. Let $F_i$ count expected target incidences into $C_i$ from representatives in other rows, $n_i$ count senders with positive excess there in expectation, and $N_i$ count senders with that unique strong row. For $i<k$, write $e_{ik}$ for the number of target edges from $C_i$ to $C_k$. Set
$$
Q=\sum_i n_i(E_i+F_i)/r,\qquad T_1=\sum_i N_iE_i/r,\qquad K_E=\sum_{i<k} N_i N_k e_{ik}.
$$
If $j/r$ bounds the mass of each representative output into its row, the expected number of repairs is at most
$$
\mathcal R=\tfrac43\bigl(Q-\rho\sum_i n_i^2\bigr)+jT_1+(j/r)^2 K_E .
$$
The single-row count includes senders whose representative and mark are correlated. The between-row count uses distinct sender coordinates. Multiple justifications for the same repair yield a single unordered edge. [Expected cost on the original graph](ColoringRepairCost.lean) · [Foreign incidences on their actual cuts](ForeignRowLoads.lean)

## Testing the same edges

Fix a tested subfamily $I$. Write $H=h+|I|$, $d_i=r-|C_i|$ and $D=\sum_{i\in I}d_i$. With $U=W\cup\bigcup_{i\in I}C_i$, the target edge difference
$$
e_J(U)-e_J(W)-\sum_{i\in I}\binom{|C_i|}{2}
$$
is exactly the exterior-to-row cut plus the target edges between tested rows. On $U$, each other color has independence number at most $r$. Choose between two adjacent integer Turán bounds according to the sign of $D+v$. Together with the repaired graph’s independence bound on $W$, these give the signed cut on every supported outcome. [Edge-count identity and both signs](SignedSampleCut.lean) · [Averaging over sender trials and arc starts](ColoringSignedCut.lean)

Now test rows independently with probabilities $\pi_i$. Put $B=\sum_i\pi_i d_i$. Lean proves
$$
2\left(\sum_i\pi_i E_i+\sum_{i<k}\pi_i\pi_k e_{ik}\right)
\le 2\mathcal R+r\,\mathbb E[H(H-1)]+(B+u)^2+m-u-\sum_i(\pi_i d_i)^2 .
$$
For $\pi_i=(a n_i+bN_i)/r$ in $[0,1]$, $a\ge0$ and $b\ge j$, swapping the two endpoints of each original interrow edge pays for the foreign representative incidences as well as for the pair repairs. In the notation above the resulting inequality is
$$
2\left[(a-\tfrac43)Q+(b-j)T_1+\bigl((b/r)^2-(j/r)^2\bigr)K_E
+\tfrac43\rho\sum_i n_i^2\right]
\le r\,\mathbb E[H(H-1)]+(B+u)^2+m-u-\sum_i(\pi_i d_i)^2 .
$$
Both subtractions on the right are retained by the calculation. The statement applies to any admissible thinning, including oversampling. [Independent row tests](TestedRowMoments.lean) · [Combined tested cut](ColoringTestedCut.lean) · [Recovery on the original edges](RecoveredTest.lean)

## From the sample to the cutoff

The per-row and total heavy-load counts, the manuscript row probabilities and their expected total are now in Lean. The two kinds of load use disjoint incidences, giving coefficient one. [Proof and replay](heavy-loads.md)

The expected cost of distinct repairs at the enlarged sampling probability is now bounded directly by four times its base value. Both oversampling passes and the one-row bound for moderate senders have been formalized. The completed proof combines strong and moderate assignments at each destination and derives inequality (5) on the same coloring. [End-to-end theorem and replay](formal-cutoff.md) The rational checker gives positive values at all 1,280 endpoints. [Oversampling proofs](oversampling.md) · [Endpoint checker](verify_retained_width.py)

## Replaying the proofs

Run these commands in the package directory containing the pinned Lake environment.

```sh
lake env python3 -B proof/replay_pruning_kernels.py sampling
lake env python3 -B proof/replay_pruning_kernels.py cut
python3 -B proof/verify_retained_width.py
```

Lean's kernel, Lean4Lean and Nanoda each accepted the two exports below. The axiom reports list only `propext`, `Classical.choice` and `Quot.sound`. The declaration counts include dependencies.

| Replay | Named theorems | Export declarations | Export SHA-256 |
| --- | ---: | ---: | --- |
| `sampling` | 10 | 30,089 | `87c8aa4cd3bc52dce81b634d9d7bc38a2bc1855c423e134c62323ca10aeac1be` |
| `cut` | 14 | 18,467 | `dd27424259743855929a39b8ca4b58374a58f280b3a5d2ed203483f6cae80b8e` |

The endpoint replay reported a minimum of 0.000332766 to nine decimal places. An internal source review checked the coloring, edge orientation, both signed cases and the treatment of zero-weight outcomes. Independent mathematical review of the complete manuscript is pending.
