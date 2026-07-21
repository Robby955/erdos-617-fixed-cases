# Fixed \(r=9\), order \(26\), degree-nine level \(m=59\)

> **SUPERSEDED DOWNSTREAM STATUS.** The scoped \(m=59\) theorem below
> remains valid. Its statements about later open branches reflect the date
> of this checkpoint. Fixed \(r=9\) is now locally proved; see
> output/ERDOS_617_R9_RELEASE_HANDOFF.md.

## Status

The core level \(m=59\) in the order-26 degree-nine branch is locally
proved impossible. The proof combines a uniform core lemma, 1,235 exact
rational duals, and a solver-free exhaustive check of 11,943 row-size
states. A separate Z3 search/encoding audit agrees on every state.

Together with the preceding endpoint work, this proves the degree-nine
core levels \(m=56,57,58,59\). It does not exclude the degree-eight
branch or the degree-nine levels \(m=60,\ldots,64\). It does not prove
\(P_3(26)\ge121\), fixed \(r=9\), or Erdős Problem 617.

## 1. Setup

Let \(H\) be a target-color graph on 26 vertices inherited from a
hypothetical balanced nine-coloring. Suppose

\[
 \alpha(H)\le3,
 \qquad
 \omega(H)\le8,
 \qquad
 e(H)\le120,
 \qquad
 \delta(H)=9.
\]

Fix a degree-nine vertex \(v\), put \(A=N_H(v)\), and put

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
 m=e(L)=59.
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 x_{ab}=\mathbf 1_{b\in D_a},
 \qquad
 c=\sum_{a\in A}|D_a|.
\]

The inherited conditions used below are:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. Every induced subgraph \(L[Z]\) with \(|Z|\ge10\) has at least
   \(8p_9(|Z|)\) edges, where
   \[
   p_9(9q+s)=(9-s)\binom q2+s\binom{q+1}2.
   \]
3. \(F\) is \(K_4\)-free, \(\alpha(F)\le7\), and \(f\ge8\).
4. The global target-edge ledger gives
   \[
   c\le f+m-45=f+14. \tag{1}
   \]
5. Minimum degree in \(H\) gives
   \[
   |D_a|\ge d_F(a), \tag{2}
   \]
   and
   \[
   \sum_{a\in A}x_{ab}\ge d_L(b)-6. \tag{3}
   \]
6. If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) is a vertex cover of
   \(L\). Equivalently, for every \(bb'\in E(L)\),
   \[
   x_{ab}+x_{ab'}+x_{a'b}+x_{a'b'}\ge1. \tag{4}
   \]
7. If \(T\) is a triangle of \(F\), then for every \(b\in B\),
   \[
   \sum_{a\in T}x_{ab}\ge1. \tag{5}
   \]

Condition (5) follows because a missed triangle together with \(b\)
would be an independent four-set in \(H\).

## 2. Uniform structure and the \(p=1\) exclusion

### Lemma 2.1

The graph \(L\) is bipartite with two sides of order eight. It is
\(K_{8,8}\) with exactly five cross-edges removed. Its only independent
eight-sets are its two bipartition classes.

### Proof

Suppose \(L\) is nonbipartite, and take a shortest odd cycle \(C\) of
length \(\ell\ge5\). It is chordless. Every vertex outside \(C\) has at
most two neighbors on \(C\): three neighbors split \(C\) into three
paths, triangle-freeness makes each path have length at least two, and
an odd path together with the outside vertex gives a shorter odd cycle.
Mantel's theorem outside \(C\) now gives

\[
 e(L)
 \le
 \ell+2(16-\ell)
 +\left\lfloor\frac{(16-\ell)^2}{4}\right\rfloor
 \le57,
\]

contrary to \(e(L)=59\). Thus \(L\) is bipartite. Its sides are
independent, so \(\alpha(L)\le8\) forces an \(8+8\) bipartition.

The five missing edges determine \(L=K_{8,8}-Q\), where \(|Q|=5\).
An independent eight-set using \(p\) vertices from one side and \(8-p\)
from the other would require all \(p(8-p)\ge7\) cross pairs to lie in
\(Q\). Hence the two sides are the only independent eight-sets.
\(\square\)

### Lemma 2.2

No row \(D_a\) contains either bipartition class of \(L\).

### Proof

A bipartition class \(C\) is independent in \(L\), hence a clique of
order eight in \(H[B]\). If \(C\subseteq D_a\), then \(a\) is adjacent
in \(H\) to every vertex of \(C\), and \(C\cup\{a\}\) is a target
\(K_9\). This contradicts \(\omega(H)\le8\). \(\square\)

Lemma 2.2 is the \(p=1\) target-clique condition used by the finite
verifier.

## 3. Exact catalogs and scalar row states

The semantic verifier generates every unlabelled triangle-free graph
\(L\) on 16 vertices with 59 edges and maximum degree at most eight. It
then checks \(\alpha(L)\le8\) and every inherited induced-subgraph lower
bound. Exactly 20 core types remain. Their graph6 catalog has SHA-256

~~~text
9aee919b0e777b970e07c8cd770c72477821a0abdbb5efbddaca689c9cefd8d5
~~~

For a shell \(F\), write

\[
 |D_a|=d_F(a)+\epsilon_a,
 \qquad \epsilon_a\ge0.
\]

Summing (2) and applying (1) gives

\[
 f+\sum_a\epsilon_a\le14. \tag{6}
\]

Each shell edge also gives

\[
 d_F(a)+d_F(a')+\epsilon_a+\epsilon_{a'}\ge8, \tag{7}
\]

because \(D_a\cup D_{a'}\) covers \(L\), whose cover number is eight.

The verifier generates every unlabelled \(K_4\)-free graph \(F\) on
nine vertices with \(8\le f\le14\), checks \(\alpha(F)\le7\), and
retains precisely the shells admitting a nonnegative integral slack
vector satisfying (6) and (7). Exactly 85 shell types remain. Their
graph6 catalog has SHA-256

~~~text
5dba2d8d90c013e226770536a65d5c36ac2167d05a88d8ec24c1a51249fb0a5b
~~~

Thus the level has exactly

\[
 20\cdot85=1700
\]

core-shell pairs.

## 4. The 1,235 rational-dual exclusions

Consider the nonnegative real relaxation formed by (2), (3), (4), and
(5), with objective

\[
 \min\sum_{a\in A,b\in B}x_{ab}. \tag{8}
\]

For 1,235 of the 1,700 pairs, the certificate file supplies nonnegative
rational weights on selected inequalities. The coefficient of each
variable in the weighted sum is at most one, while the weighted right
side is strictly greater than \(f+14\). Summing the inequalities proves

\[
 \sum_{a,b}x_{ab}>f+14,
\]

contrary to (1).

The proof-facing verifier reconstructs both catalogs and every weighted
inequality, reduces each fraction exactly, and checks every strict
comparison. It does not call an optimizer or a SAT solver. Floating-point
linear optimization appears only in the separate candidate generator.

The exact receipt is:

~~~text
cores=20 shells=85 pairs=1700
strict_duals_verified=1235 uncertified_pairs=465
dual_semantic_sha256=0c62f8085a539f43c12d23a28aa1320426814eaba5c9c415d19d3a006f84809b
status=PASS
~~~

## 5. Solver-free exhaustion of the 465-pair remainder

For each remaining pair put

\[
 q_a=|D_a|=d_F(a)+\epsilon_a.
\]

The verifier enumerates every integer vector \(q\) satisfying (6) and
(7). Pair-weighted over the 465 pairs, there are exactly 11,943 states.

Every shell in the remainder has a two-vertex edge cover \(\{h,g\}\).
After fixing the rows \(D_h,D_g\), the other seven shell vertices are
independent in \(F\). For each low vertex \(u\), the verifier enumerates
every \(q_u\)-subset \(D_u\subseteq B\) satisfying all cover conditions
with its incident hubs. If \(hgu\) is a triangle, it also imposes

\[
 D_h\cup D_g\cup D_u=B. \tag{9}
\]

Every enumerated row obeys Lemma 2.2. An exact memoized dynamic program
then checks all sixteen column demands in (3). There are no omitted
low-to-low shell constraints because the two hubs meet every shell edge.
Once the hubs are fixed, the only joint conditions left among the low
rows are the column demands. The recursion tries every row in every
nonempty domain and memoizes only failed residual-demand states.

The full solver-free receipt is:

~~~text
cores=20 shells=85 pairs=1700
strict_duals_semantically_verified=1235 uncertified_pairs=465
dual_semantic_sha256=0c62f8085a539f43c12d23a28aa1320426814eaba5c9c415d19d3a006f84809b
two_hub_remainder_pairs=465
q_states=11943 p1_UNSAT=11943 p1_SAT=0
pair_q_state_profile={1: 51, 2: 24, 4: 26, 10: 153, 11: 26, 12: 14, 19: 53, 20: 3, 21: 7, 36: 14, 46: 2, 55: 58, 56: 7, 65: 4, 66: 1, 100: 6, 103: 1, 220: 12, 230: 2, 235: 1}
hub_pairs_examined=251251840
demand_states_examined=11190852
classification_sha256=688ba89fcb69a6ca76cc8607dd4aaba4cebd4850367d2b9946919648a55067c8
status=PASS
~~~

There is therefore no incidence family \((D_a)_{a\in A}\) satisfying
the inherited conditions for any of the remaining 465 pairs. Together
with Section 4, this excludes all 1,700 pairs and proves that \(m=59\)
is impossible.

## 6. Separate audit and replay

The separate incidence audit regenerates the graph catalogs through the
proof-facing catalog module. It then reconstructs the dual-pair complement,
row-size states, Boolean incidence constraints, and \(p=1\) condition
without importing the solver-free search. It asks Z3 about every one of
the 11,943 states and obtains:

~~~text
cores=20 shells=85 remaining_pairs=465
q_states=11943 z3_UNSAT=11943 z3_SAT=0 z3_UNKNOWN=0
classification_sha256=688ba89fcb69a6ca76cc8607dd4aaba4cebd4850367d2b9946919648a55067c8
status=PASS
~~~

Both implementations serialize

\[
 (\mathit{core\ index},\mathit{shell\ index},q,
   \mathit{satisfiable})
\]

in the same canonical order and obtain the same classification digest.
Z3 is an audit, not a premise of the proof.

Run the proof-facing checks with:

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_order26_m59_duals.py \
  --geng /private/tmp/nauty289-build/geng \
  --certificates \
    research/erdos-617-r6/r9_p93_order26_m59_duals.jsonl

python3 research/erdos-617-r6/r9_p93_order26_m59_p1_qstate_verifier.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m59_duals.jsonl \
  --workers 10

python3 research/erdos-617-r6/r9_p93_order26_m59_p1_qstate_z3_audit.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m59_duals.jsonl \
  --workers 10
~~~

The retained replay used Python 3.13.13, NetworkX 3.4.2, Z3 4.16.0, and
nauty 2.8.9. The `geng` executable had SHA-256

~~~text
3ca950af2145c546f9f586cf960eaf98f88fc3920564338f8306b6f58d018af5
~~~

The proof depends on the completeness of the nauty `geng` unlabelled
graph catalogs. It does not depend on floating-point feasibility or the
Z3 result.

## 7. Exact nonclaims

1. The order-26 degree-eight family is not excluded here.
2. The order-26 degree-nine levels \(m=60,\ldots,64\) are not excluded.
3. This theorem does not prove \(P_3(26)\ge121\).
4. This theorem does not prove fixed \(r=9\).
5. This theorem does not prove Erdős Problem 617.
