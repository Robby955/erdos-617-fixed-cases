# Fixed \(r=9\), order 26, degree nine, level \(m=64\)

> **SUPERSEDED DOWNSTREAM STATUS.** The scoped \(m=64\) theorem below is
> a dependency of the locally proved fixed-\(r=9\) result. Its earlier
> statements that other branches or the outer implication remained open
> are historical. See output/ERDOS_617_R9_RELEASE_HANDOFF.md.

## Verdict and scope

LOCALLY PROVED. The dependency-closed manifest verifies locally; a replay
from committed source in a clean checkout remains a release-level gate.

There is no target graph \(H\) on 26 vertices satisfying

\[
 \alpha(H)\le3,
 \qquad
 \omega(H)\le8,
 \qquad
 \delta(H)=9,
 \qquad
 e(H)\le120,
\]

for which the 16-vertex complement core defined below has 64 edges.

The proof uses exact rational inequalities, a solver-free scalar reduction,
a short human exclusion of four cover-number-three states, and a solver-free
orbit search for seven cover-number-two shells. This theorem does not handle
the order-26 degree-eight branch, either order-27 branch, or the outer
implication audit. It does not prove fixed \(r=9\) or Erdős Problem 617.

## 1. Reduction to a core-shell incidence system

Choose a degree-nine vertex \(v\), put \(A=N_H(v)\), and put

\[
 B=V(H)\setminus(A\cup\{v\}).
\]

Thus \(|A|=9\) and \(|B|=16\). Define

\[
 F=\overline{H[A]},
 \qquad
 L=\overline{H[B]},
 \qquad
 f=e(F),
 \qquad
 e(L)=64.
\tag{1}
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 q_a=|D_a|.
\tag{2}
\]

The inherited conditions are:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. \(F\) is \(K_4\)-free and \(\alpha(F)\le7\).
3. The target-edge count is
   \[
   e(H)=9+(36-f)+56+\sum_{a\in A}q_a,
   \]
   so
   \[
   \sum_{a\in A}q_a\le f+19.
   \tag{3}
   \]
4. Minimum degree at a shell vertex gives
   \[
   q_a\ge d_F(a).
   \tag{4}
   \]
5. Minimum degree at a core vertex gives
   \[
   \sum_{a\in A}\mathbf 1_{b\in D_a}
   \ge d_L(b)-6.
   \tag{5}
   \]
6. If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) is a vertex cover of
   \(L\).
7. If \(a,a',a''\) form a triangle in \(F\), then
   \[
   D_a\cup D_{a'}\cup D_{a''}=B.
   \tag{6}
   \]
8. No \(D_a\) contains an independent eight-set of \(L\).

The unique 64-edge core is

\[
 L=K_{8,8}.
\tag{7}
\]

Write its sides as \(X\cup Y\). They are the only independent eight-sets,
so

\[
 |D_a\cap X|\le7,
 \qquad
 |D_a\cap Y|\le7.
\tag{8}
\]

Every vertex of \(L\) has degree eight. Equation (5) therefore requires
two incidences in every core column, or sixteen incidences on each side.
Also, every vertex cover of \(K_{8,8}\) contains \(X\) or \(Y\).

Summing the column demands gives \(\sum_aq_a\ge32\), so (3) gives
\(f\ge13\). Summing (4) gives \(\sum_aq_a\ge2f\), so (3) also gives
\(f\le19\). Thus every possible shell lies in the exact edge range
\(13\le f\le19\).

## 2. Exact catalogs and rational duals

The shell generator enumerates every \(K_4\)-free graph on nine vertices
in the larger range \(8\le f\le19\), rejects graphs with an independent
eight-set, and rejects graphs whose minimum row slack exceeds \(19-f\).
The preceding bounds and (4), (6) show that these filters cannot reject a
candidate. Independent catalog reconstructions give one core and 7,454
shell types. Their graph6 catalog hashes are

~~~text
core_catalog_sha256=07c708c5c0652d72f0247fa67ea661904e84a8e30368669e24708bbd7cb48a29
shell_catalog_sha256=fba322c6bb7dad18d9e14c51a1b97a33abd67186e30c5c1a4eb40908ffca9c1a
~~~

For every core-shell pair, use Boolean variables

\[
 x_{ab}=\mathbf 1_{b\in D_a}.
\]

The row lower bounds, column demands, edge-cover inequalities, and
triangle-cover inequalities give a finite family of lower bounds. A
nonnegative rational combination in which every variable has coefficient
at most one and whose right side exceeds \(f+19\) excludes the pair.

The generator finds such exact rational duals for 6,892 pairs. The
independent semantic verifier rebuilds every inequality and checks every
coefficient over `Fraction`. The remaining 562-pair digest is

~~~text
uncertified_pair_sha256=96303541e4dfaf31fab4a61ebefea1390e2cc53f90b2b238e43eb5923638036e
semantic_sha256=d77700d00082ebc0370822fcf4f58393891a936cd71a0e1223873fc4f0c43a57
data_sha256=4710a3e7761bcfe319a3af94c92fb228cb98eba0ea2d2ff9753568389ea6465c
~~~

## 3. Exact scalar reduction

Write

\[
 q_a=d_F(a)+\epsilon_a,
 \qquad
 \epsilon_a\ge0.
\tag{9}
\]

The scalar verifier enumerates every integral vector satisfying

\[
 f+\sum_a\epsilon_a\le19.
\tag{10}
\]

Put

\[
 x_a=|D_a\cap X|,
 \qquad
 y_a=q_a-x_a.
\]

The necessary side conditions are

\[
 0\le x_a,y_a\le7,
 \qquad
 \sum_a x_a\ge16,
 \qquad
 \sum_a y_a\ge16,
\tag{11}
\]

\[
 x_a+x_{a'}\ge8
 \quad\hbox{or}\quad
 y_a+y_{a'}\ge8
 \qquad(aa'\in E(F)),
\tag{12}
\]

and, on every shell triangle,

\[
 x_a+x_{a'}+x_{a''}\ge8,
 \qquad
 y_a+y_{a'}+y_{a''}\ge8.
\tag{13}
\]

The exact replay checks 101,880 row-size states. It leaves 10,639 states
with pair profile

~~~text
(cover number 2, survives): 7
(cover number 3, fails):    469
(cover number 3, survives): 4
(cover number 4, fails):     78
(cover number 5, fails):      4
~~~

The classification and surviving-frontier hashes are

~~~text
classification_sha256=c3f369569d4fa8cbc19dd8043e8445dfd723f068c85922e2420c5e270354afcc
frontier_sha256=c7d527a52b042e6a900252254634b1ee573b1edf72e562312ec6e9b947b0ff92
~~~

## 4. Human exclusion of the three-hub states

The four surviving cover-number-three states are

| shell | row sizes |
|:---|:---|
| `H??Ff~}` | \((3,3,3,3,2,2,7,7,7)\) |
| `H??Fvrz` | \((3,3,3,3,3,0,7,7,7)\) |
| `H??Fvv}` | \((3,3,3,3,3,1,7,7,7)\) |
| `H??F~zz` | \((3,3,3,3,3,2,7,7,7)\) |

In every case, vertices \(6,7,8\) form the unique minimum vertex cover of
the shell, and the graph induced by them is a two-edge path. Let \(c\) be
its center and let \(u,w\) be its leaves. Four or five other shell vertices
are adjacent to all three hubs.

The exact side-count check has ten assignments. After possibly exchanging
\(X\) and \(Y\), every one has

\[
 |D_c\cap X|=1,
 \qquad
 |D_c\cap Y|=6,
 \qquad
 D_u,D_w\subseteq X,
 \qquad
 |D_u|=|D_w|=7.
\tag{14}
\]

Let \(D_c\cap X=\{x_0\}\) and put \(S=D_c\cap Y\), so \(|S|=6\).
Since \(cu,cw\in E(F)\), both corresponding row unions are vertex covers
of \(K_{8,8}\). Their \(Y\)-counts total only six, so they must cover
\(X\). Equality in their \(X\)-counts gives

\[
 D_u=D_w=X\setminus\{x_0\}.
\tag{15}
\]

Let \(a\) be adjacent to all three hubs. The edge \(ac\) cannot cover
\(X\), so it covers \(Y\); the edges \(au,aw\) cannot cover \(Y\), so
they cover \(X\). Since \(|D_a|=3\), equality forces

\[
 D_a=(Y\setminus S)\cup\{x_0\}.
\tag{16}
\]

Thus every vertex of \(S\) has exactly one incidence among the hubs and
the four or five all-hub rows, namely its incidence in \(D_c\). Equation
(5) requires a second incidence for each of these six vertices. The total
row capacity outside the hubs and all-hub rows is respectively

\[
 4,0,1,2
\]

in the four states. Every value is less than six, a contradiction.

The solver-free verifier enumerates the ten side assignments, checks the
unique-cover and path structure, and replays this capacity contradiction.
Its receipt is

~~~text
receipt_sha256=35a6958c0aca067069497558ea0e09ee90ae00e5bb1903c73c6960cfe402241e
~~~

## 5. Solver-free two-hub orbit exhaustion

The remaining seven shells have two-vertex edge covers and contain 10,635
row-size states. The automorphism subgroup preserving the two core sides is

\[
 S_8\times S_8.
\]

For an ordered pair of hub rows, record on each side the four-bin
membership histogram

\[
 (00,01,10,11).
\]

These two histograms are complete orbit invariants under the displayed
subgroup. The verifier independently compares the formula profile with all
21,904 direct representatives and transports sample representatives across
the adjacent-transposition generators.

For each hub-pair orbit, the verifier constructs the exact domain of every
remaining row. It applies the shell-edge cover conditions, triangle unions,
row sizes, side caps, and the two-incidence column demand. Residual column
demands are solved by a finite dynamic program. If one domain effect is
contained in another, the smaller effect is discarded because replacing it
by the larger effect preserves every local condition and cannot reduce a
lower-bound column count.

The replay gives

~~~text
q_states=10635 orbit_UNSAT=10635 orbit_SAT=0
pair_q_state_profile={699: 1, 1233: 2, 1746: 2, 1989: 2}
orbit_representatives=3883026
candidate_orbits=498326
demand_states=299684034
demand_transitions=299609210
classification_sha256=cd3805257b22201ab5bc0752ad4a691f48c3f13181cffbee0621b48e5b024820
orbit_receipt_sha256=310705ec896fd69e29f337e259b225873b736c9c223bb95e0bb78835bccfe7bc
~~~

Every two-hub state is impossible. Section 4 excludes the four three-hub
states. Together with Sections 2 and 3, this excludes all 7,454 core-shell
pairs and proves the local theorem.

## 6. Replay

The canonical replay commands are:

```sh
python3 research/erdos-617-r6/verify_r9_p93_order26_m64_duals.py \
  --geng /private/tmp/nauty289-build/geng \
  --certificates research/erdos-617-r6/r9_p93_order26_m64_duals.jsonl

python3 research/erdos-617-r6/r9_p93_order26_m64_scalar_side_verifier.py \
  --geng /private/tmp/nauty289-build/geng

python3 research/erdos-617-r6/r9_p93_order26_m64_tau3_verifier.py

python3 research/erdos-617-r6/r9_p93_order26_m64_p1_orbit_verifier.py \
  --self-test

python3 research/erdos-617-r6/r9_p93_order26_m64_p1_orbit_verifier.py \
  --geng /private/tmp/nauty289-build/geng --workers 8
```

The independent Boolean reconstruction and corruption tests are package
audits. The mathematical proof above is solver-free. The pinned CaDiCaL
audit returned 101,880 UNSAT, zero SAT, and zero UNKNOWN with
classification SHA-256
`e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331`.

## 7. Exact nonclaims

1. This theorem excludes only \(m=64\) in the order-26 degree-nine branch.
2. Downstream theorem packages, not this scoped theorem alone, exclude the
   order-26 degree-eight and order-27 branches.
3. Downstream theorem packages, not this scoped theorem alone, complete the
   outer implication chain and fixed \(r=9\).
4. It does not prove Erdős Problem 617 for arbitrary \(r\).
