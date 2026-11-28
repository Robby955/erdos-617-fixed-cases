# A third pruning pass for the Erdős–Gyárfás cutoff

Robert Sneiderman and OpenAI GPT-6.2 Astra · 27 November 2026

**Theorem.** For every integer \(r\ge 2^{143}\), every \(r\)-coloring of the edges of \(K_{r^2+1}\) has \(r+1\) vertices missing a color.

Lean now proves this cutoff from the original edge coloring. The independently implemented Lean4Lean and Nanoda kernels and the Lean kernel accepted the same export. Two arithmetic replays also cover the continuous parameter ranges. Independent mathematical review of the manuscript remains open. [End-to-end theorem](ThirdPruningCutoff.lean) · [Pinned kernel replay](cutoff-143-kernels.txt)

## 1. What the first pruning pass can actually spend

Assume there is a counterexample. In its sparsest color \(J\), use the ordered raw parts and the first two pruning passes of [weighted-width.md, §§1–2](weighted-width.md). There are \(r\) parts, including any empty parts. Set \(b_i=|R_i|-r\), let \(\mu_i\) count the nontarget pairs in the part, and put \(U_i=\mu_i-(r-1)b_i\). Write \(X\) for the raw interpart target edge count. We shall use
\[
 v=\sum_i(b_i/r)^2\le s=1-X/r^2,\quad
 \sum U_i/r^2\le (1-v)/2,\quad \sum (b_i)_+/r\le1/2,
 \qquad \mu/r^2\ge1/2-s.                                      \tag{1}
\]
Here \(\mu=\sum\mu_i\). For the last bound, the raw edge identity gives \(X\le\eta+\mu\), since \(\sum b_i^2\ge1\), and sparsity gives \(\eta\le\binom r2\).

Let \(z_i\) count the first-stage sources assigned to destination \(i\), and put \(pr=\sum z_i\). The existing local star bound gives \(z_i/r\le\omega=5/1464\). On the union of the destination and its sources, each other color has a vertex cover of minimum size at least \(b_i+z_i\), hence at least that many edges. Counting the three classes of pairs gives
\[
 U_i\ge e_J(Z_i,R_i)-(1+b_i)z_i-\tbinom{z_i}2+e_J(Z_i).
\]
Each recorded star contributes more than \(r/4\) edges to its raw destination. With \(q_i=z_i/r\), we have \(\sum (b_i/r)q_i\le\omega/2\) and \(\sum q_i^2\le\omega p\). Summation yields
\[
 (1/4-\omega/2-1/(2r))p\le (1+\omega-v)/2,\qquad p<2021/1000.       \tag{2}
\]
The previous cap was \(125/61\). Both full cutoff replays below use this larger cap, so the new width argument can be reviewed without assuming the improvement (2). There is still an interior obstruction to the old width comparison, for example \(p=1.99,\ Z=0.001\). At that point its margin is below \(-0.116\) even granting the upper-endpoint rebate \(G(1)=2-2\log 2\). The point describes a relaxation of the counts. There is a reason a single destination gives little room. On one raw row of size \(r\) and \(z\) exterior vertices, use \(\lfloor r/4\rfloor\) other colors as disjoint matchings of size \(z\) inside the row, and the remaining other colors as disjoint matchings from the exterior vertices into the row. Color all remaining edges \(J\). For \(z\le (r-1)/2\), the internal matchings can run from the same \(z\) anchors to cyclic shifts of the other raw vertices, reserving one raw pivot. The external matchings use cyclic shifts on the whole row. Each exterior vertex has exactly \(\lfloor r/4\rfloor+1\) target neighbors there. Every other color has independence number exactly \(r\), and the anchors, the other raw vertices and the exterior vertices are three target cliques. This realizes equality in the local bundle inequality without specifying any coloring between different bundles.

## 2. The additional pruning pass

Let \(tr\) be the second-stage deletion count and \(\tau=199/400\). Define
\[
 Z=1-p/4-\tau t,\qquad Y_*=1-p/4+Z.
\]
Start a third pass from these same survivors. Delete a vertex while it has more than \(cr\) target neighbors in other surviving parts, where \(c=9/25\). Write \(kr\) for the number deleted, \(er^2\) for the final interpart target edge count, and
\[
 \sigma=Z-s-e-ck\ge0.                                            \tag{3}
\]
Indeed, every interpart target edge either survives or is counted at its first deleted endpoint. Subtract the per-source quotas \(1/4,\tau,c\), in units of \(r\), from the full fresh foreign degrees at deletion. The sum of the excesses is exactly \(\sigma r^2\) in edge units. Every final survivor has foreign degree at most \(cr\).

Use the five width bands in the [intermediate cutoff calculation](cutoff-descent-20261127.md). For a band with parameters \(b,\alpha,\beta\) put
\[
 W=\log\!\left(2^{(143-b)/4}/1120\right)
   -Y_*/\alpha-(p+t)/\beta
   +\min\{(391+(1464/5)p)/1120,(4333+737p)/10000\}.
\]
The original two-pass width proof already succeeds when \(W+2s/\alpha>0\): its raw incidence count starts at \(2X/r^2=2-2s\). The savings for the chosen oversized rows subtract only incidences missed beyond the original quota charges. See [the incidence proof](weighted-width.md) and [the upper-endpoint proof](retained-width.md). In the rest assume \(W+2s/\alpha\le0\).

After the third pass, again choose a maximal collection of independent pairs in distinct parts, all endpoints mutually independent. Let \(q\) be the number of pairs. The surviving lists in the other parts, after deleting the pair neighborhoods, are cliques. Write \(F\) for the number of short lists, \(n=F+q\), and \(D\) for the total fractional deficit of the ordinary cliques. A short list has size below \(\lfloor399r/400\rfloor\). The weighted transversal inequality \(q\le\sum_{\rm short}(1-m_i/\lfloor399r/400\rfloor)\) still applies, since the maximum foreign degree has decreased.

**When \(q\ge1\).** Relative to the original deficit calculation, the third pass adds \(k\) but the chosen endpoints delete at most \(2cq r\) other points, saving \(2(\tau-c)q\) in normalized deficit. The third-stage source incurs another \(ck\) in missing foreign incidences. To check overlap, assign only the quota to each deletion, counting both ends of first-stage recorded edges and only the source at the other two stages. All paid edges are fresh. A missing outgoing incidence of a chosen oversized row can overlap a payment only at an early source in that row. The payment per source is at most \(\tau r\), exactly the cap in the original overlap argument, now with third-stage sources included in the row's early deletion count. Thus the modified width margin is at least
\[
 W+\frac{2(\tau-c)q-k}{\beta}+\frac{2s+ck}{\alpha}.                \tag{4}
\]
The remaining reserve and upper-endpoint proof uses the original first-stage counts because the raw parts, qualifications and first pass are identical. The bound (4) is positive on the entire remaining domain already with \(q=1\). The arithmetic checks also give
\[
 p+t+k+\max(0,1/2-2(\tau-c))<3.53 .
\]
In fact the area estimate before paying for chosen oversized parts is
\(D+n/400\le p+t+k+\sum_{\rm chosen}(b_i/r-a_i)-2(\tau-c)q\), where \(a_i r\) counts early deletions in the part. When \(q=0\) the chosen sum is zero. These bounds preserve \(D<3.53\) and \(n\le1411\) in either branch.

**When \(q=0\).** All final parts are target cliques. Their normalized deficits \(d_i=1-|C_i|/r\) lie in \([0,1]\) and sum to \(p+t+k-1/r\). Set \(d=\max d_i\) and \(d_0=1/400\). Omitting short rows gives
\[
 D+d_0n+(d-d_0)_+\le p+t+k.
\]
If a largest-deficit part is short, use its whole deficit. If no part is short, each has at least \(\lfloor399r/400\rfloor\) points, so \((d-d_0)_+\le1/r\). The extra vertex pays for precisely this rounding case.

Every interpart edge that fails to survive loses at least the incidence at its first removed endpoint. Every recorded first-stage edge also loses its destination incidence from the definition of the retained cut. Thus the actual total retained incidence is at most \((X/r^2)+e-p/4=Y_*-(s+Z-e)\). No chosen-row correction is needed. The \(d_0n\) term covers the original width penalty \((1-2\tau-1/256)n/2\). If the third-pass width fails, we therefore have
\[
 (d-d_0)_+\le k-\beta\{W+(s+Z-e)/\alpha\}.                       \tag{5}
\]

## 3. Charge each missing internal edge

Write \(a_i\) for the fraction of early deletions in row \(i\) across all three passes. We have \(a_i=d_i+b_i/r\) and \(\sum a_i=p+t+k\). Let \(A=\sum a_i^2\). Cauchy–Schwarz gives
\[
 A\le d(p+t+k)+\sqrt{sA}.
\]
All missing internal edges either have two removed ends or one removed end. Write their counts divided by \(r^2\) as \(M,H\), respectively. Then
\[
 M\le A/2,\qquad M+H\ge1/2-s.                                   \tag{6}
\]

For an edge counted in \(H\), let \(x\) be its removed endpoint and \(w\) its surviving endpoint in the same raw part. Write \(D_x,D_w\) for their target degrees into all other final parts, divided by \(r\). Set \(L=1-d\). If \(L>0\), then
\[
                 D_x+D_w\ge L-e/L.                              \tag{7}
\]
Suppose (7) fails. Keep \(x,w\) and choose one survivor independently and uniformly from the allowed vertices in every other part. Their forbidden fractions sum to at most \(D_x+D_w\) over all these parts. In particular, for any two distinct parts, their allowed list sizes divided by \(r\) have product at least \(L(L-D_x-D_w)>e\). All lists are nonempty. There are at most \(er^2\) target edges between them, so the expected number among the chosen representatives is strictly less than one. Those representatives and \(x,w\) give \(r+1\) vertices missing \(J\). The budget here uses the sum of deletions over two *distinct* lists. Squaring a single minimum list size would give a substantially weaker bound.

The stage quota for a removed vertex is at most \(\tau\), and its final foreign neighbors were live at deletion. Its excess above \(\tau\), when positive, can therefore be charged to its fresh degree beyond quota. The sum of these positive excesses over removed vertices is at most \(\sigma r\) in normalized degree units. Each removed vertex can be the endpoint of at most \(r\) of these missing edges, since its own final part is a clique. Each survivor is the endpoint of at most \(a_i r\le(d+\sqrt{s})r\) of them. Also \(\sum_w D_w=2er\) and \(D_w\le c\). Summing (7) in two ways yields
\[
 (L-e/L-\tau)H\le\sigma+2e(d+\sqrt{s}),\qquad
 (L-e/L-\tau-c)H\le\sigma.                                      \tag{8}
\]
Equations (3), (5), (6) and (8) are inconsistent throughout the remaining domain. The numerical certificates below use (8) only on subregions where \(L>0\).

## 4. Replaying the proof

The first verifier reconstructs the five pruning polygons using rational arithmetic and encloses the logarithms by their positive series. On each portion where the old width can fail, (4) is positive by an affine vertex check. In the zero-pair branch it subdivides the edge budget \((e,k,s)\) and uses outward rational square-root bounds. Each box is empty, contradicts (5), or implies \(M+H<1/2-s\). The subdivision covers shared band boundaries. The second verifier independently derives rational linear relaxations of (5)–(8), branching on \((d,e,s)\) instead. For instance \(2(1-h)M\le d(p+t+k)+s/(4h)\) for \(0<h<1\), by Young's inequality. It uses Z3 linear real arithmetic. Both procedures cover real parameters, including equality in the edge budgets.

| Upper endpoint of \(Y_*\) | First replay, terminal boxes | Second replay, infeasible linear boxes |
|---:|---:|---:|
| 0.501 | 1 | 9 |
| 0.55 | 3 | 11 |
| 0.65 | 25 | 15 |
| 1 | 1,460 | 64 |
| 2 | Original width succeeds | 2 |

The final scale in each band is \(S=(2^{143}/2^b)^{1/4}>8(1120+2\cdot1411)\). The successful width gives the three bounds in [weighted-width.md, (4)](weighted-width.md) with selected row parameter \(1120\le j<S\), hence \(r\ge 2^b j^4\). Subsequent steps use the per-destination degree bound \(r/4\) between retained cliques, the original cap on recorded sources, the undiscounted inter-clique edges in the retained incidence, its total at most the band maximum, and \(D+1/2+p<7\), \(2D<9\). Each holds for the new cliques. The exterior shortage and signed-cut proofs now apply with the same parameters. All 1,280 signed-cut endpoints are positive, with minimum exceeding \(0.00002983\). This finishes the written argument.

From this directory run

```sh
python3 -B verify_pruning_corner.py
python3 -B verify_third_pruning.py
python3 -B replay_third_pruning.py
```

The color checker also exhausts 32,768 combinations of two three-vertex lists and their cross edges in the test behind (7). The last command uses the installed Python package `z3-solver`. The first two use the standard library. [Color and signed-cut checks](verify_pruning_corner.py) · [Rational subdivision](verify_third_pruning.py) · [Independent arithmetic implementation](replay_third_pruning.py) · [Lean endpoint estimates](ThirdPruningHoles.lean)

For review, start with the overlap in (4), the short-row floor correction in (5), and the passage from (7) to (8). The Lean proof reconstructs these estimates from the same coloring. The five width ranges have direct Lean proofs, and the final theorem invokes the signed cut on the actual selected rows. [Overlap](ThirdPruningOverlap.lean) · [Floor correction](ThirdPruningFloor.lean) · [Clique case](ThirdPruningZero.lean) · [Theorem](ThirdPruningCutoff.lean)

To rebuild the final theorem with the pinned Lean toolchain, run the following from the directory containing `lean-toolchain`.

```sh
lake exe cache get
lake env python3 -Bu proof/replay_pruning_kernels.py cutoff-143 --lean-only
```

For all three kernels, install the replay executables listed in the [proof guide](formal-cutoff.md#verification-commands) and omit `--lean-only`. The export has 31,019 declarations and uses `propext`, `Classical.choice`, and `Quot.sound`. [Kernel verification record](cutoff-143-kernels.txt)
