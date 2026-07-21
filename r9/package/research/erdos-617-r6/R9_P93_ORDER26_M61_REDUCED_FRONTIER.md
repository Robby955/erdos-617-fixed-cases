# Fixed \(r=9\), order \(26\), degree-nine level \(m=61\)

## Status

The core level \(m=61\) in the order-26 degree-nine branch is locally
proved impossible. The proof combines 1,461 exact rational duals, a
solver-free scalar exclusion for 30 of the remaining 111 pairs, and a
solver-free set-system exhaustion of 8,531 row-size states for the other
81 pairs. A separate Z3 audit reconstructs the Boolean incidence problem.

This result does not exclude the degree-eight branch or the degree-nine
levels \(m=62,63,64\). It does not prove \(P_3(26)\ge121\), fixed \(r=9\),
or Erdős Problem 617.

## 1. Setup

Let \(H\) be a target-color graph on 26 vertices inherited from a
hypothetical balanced nine-coloring, with

\[
 \alpha(H)\le3,\qquad
 \omega(H)\le8,\qquad
 e(H)\le120,\qquad
 \delta(H)=9.
\]

Fix a degree-nine vertex \(v\), put \(A=N_H(v)\), and put
\(B=V(H)\setminus(A\cup\{v\})\). Thus \(|A|=9\) and \(|B|=16\). Define

\[
 F=\overline{H[A]},\qquad
 L=\overline{H[B]},\qquad
 f=e(F),\qquad
 m=e(L)=61.
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad x_{ab}=\mathbf 1_{b\in D_a}.
\]

The inherited conditions used below are:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. The inherited core-density inequalities hold on every subset of \(B\).
3. \(F\) is \(K_4\)-free and \(\alpha(F)\le7\).
4. The target-edge ledger gives
   \[
   \sum_{a\in A}|D_a|\le f+16. \tag{1}
   \]
5. Minimum degree gives
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
7. If \(T\) is a triangle of \(F\), then
   \[
   \sum_{a\in T}x_{ab}\ge1
   \qquad\text{for every }b\in B. \tag{5}
   \]

## 2. Core structure and the \(p=1\) condition

The graph \(L\) is bipartite. Indeed, the shortest-odd-cycle argument from
the preceding levels gives at most 57 edges for a nonbipartite
triangle-free graph on 16 vertices with maximum degree eight. Since
\(e(L)=61\), the graph is bipartite. Its two sides each have order eight,
because either side is independent and \(\alpha(L)\le8\). Therefore

\[
 L=K_{8,8}-Q,\qquad |Q|=3.
\]

Write the bipartition as \(X\cup Y\). The only independent eight-sets of
\(L\) are \(X\) and \(Y\). A mixed independent eight-set with \(p\)
vertices in one side would require at least
\(p(8-p)\ge7\) missing cross-edges, while \(|Q|=3\).

For every \(a\in A\),

\[
 X\nsubseteq D_a
 \qquad\text{and}\qquad
 Y\nsubseteq D_a. \tag{6}
\]

Each side is an eight-clique in \(H[B]\). Containment of one side in
\(D_a\) would create a target \(K_9\). Condition (6) is the \(p=1\)
side cap.

The exact core catalog contains four isomorphism types. Their two side
demand sums from (3) have profile

\[
 (13,13)\text{ for three types},
 \qquad (13,14)\text{ for one type}. \tag{7}
\]

## 3. Exact catalogs and rational duals

Write

\[
 |D_a|=d_F(a)+\epsilon_a,
 \qquad \epsilon_a\ge0.
\]

Conditions (1) and (2) give

\[
 f+\sum_a\epsilon_a\le16. \tag{8}
\]

The semantic verifier rebuilds every unlabelled core and shell satisfying
the inherited conditions. It obtains

\[
 4\text{ cores},\qquad
 393\text{ shells},\qquad
 1572\text{ core-shell pairs}.
\]

For 1,461 pairs, the certificate file gives nonnegative rational weights
on selected inequalities (2) through (5). In each certificate, every
variable has total coefficient at most one and the weighted right side is
strictly greater than \(f+16\). This contradicts (1).

The proof-facing verifier reconstructs every catalog entry and inequality,
checks every rational coefficient exactly, and pins the certificate data,
semantic result, and 111-pair complement:

~~~text
strict_duals_verified=1461 uncertified_pairs=111
semantic_sha256=352e48c3a2ff6dece7dc864f2d42a3ddb7ca3fa6a457f9e8063f9e43ba4b797a
uncertified_pair_sha256=0001c726de2073aced1bdeb9b95a5cb48b8387ce0012ab41479c9404c51d7ff2
data_sha256=116a0e795c163d6538644baeb874255345e9ced63aec1b81733af4b0c9a8c37e
status=PASS
~~~

## 4. Scalar side-count exclusion

For each shell vertex \(a\), put

\[
 q_a=|D_a|,
 \qquad x_a=|D_a\cap X|,
 \qquad y_a=|D_a\cap Y|.
\]

Then

\[
 x_a+y_a=q_a,
 \qquad x_a\le7,
 \qquad y_a\le7, \tag{9}
\]

where the last two inequalities are (6). Summing the column demands (3)
over each core side gives the lower bounds in (7).

There is one more exact consequence. Suppose \(aa'\in E(F)\) and
\(q_a+q_{a'}\le11\). The set \(D_a\cup D_{a'}\) covers \(L\), so its
complement is independent in \(L\) and has at least five vertices. If the
cover contained neither \(X\) nor \(Y\), that complement would meet both
sides. If its two side sizes are \(u,w\ge1\), then all \(uw\) cross-pairs
would belong to \(Q\). But \(u+w\ge5\) gives \(uw\ge4>|Q|\). Hence

\[
 x_a+x_{a'}\ge8
 \quad\text{or}\quad
 y_a+y_{a'}\ge8. \tag{10}
\]

If \(a,a',a''\) form a triangle of \(F\), condition (5) gives

\[
 x_a+x_{a'}+x_{a''}\ge8,
 \qquad
 y_a+y_{a'}+y_{a''}\ge8. \tag{11}
\]

The scalar verifier enumerates every row-size vector allowed by (8) and
the row-pair cover lower bounds, then every integer side split allowed by
(7), (9), (10), and (11). It uses only integer arithmetic. Its receipt is:

~~~text
complement_pairs=111
distinct_shells=42
pair_profile={(2, False): 1, (2, True): 81,
              (3, False): 25, (4, False): 4}
raw_q_states=29155 scalar_feasible_q_states=8531
classification_sha256=27acae752308a480d1729104709677943a514d40ec233ce44e48c7a44e5cedd2
status=PASS
~~~

The first coordinate in the pair profile is the shell vertex-cover number.
The Boolean coordinate records whether any scalar state survives. Thus the
scalar theorem excludes 30 pairs outright. The 81 surviving pairs all have
a two-vertex shell edge cover.

## 5. Solver-free exhaustion of the 81 survivors

The set-system verifier reconstructs all 82 complementary pairs whose
shell has a two-vertex edge cover. It includes the one pair already rejected
by the scalar theorem, which contributes zero surviving states. After the
scalar filter, exactly 8,531 states remain across the other 81 pairs.

For a shell edge cover \(\{h,g\}\), the other seven shell vertices are
independent in \(F\). After fixing \(D_h,D_g\), each low row is assigned
its exact finite domain of \(q_a\)-sets satisfying:

1. both side caps (6);
2. every incident row-pair cover condition (4);
3. every completed shell-triangle condition (5).

An exact memoized dynamic program tries every domain choice needed to meet
the sixteen column demands (3). The two hubs meet every shell edge, so no
low-low cover condition is omitted. Every shell triangle contains both
hubs, so no triangle condition is omitted.

The pinned production receipt is:

~~~text
two_hub_pairs=82 scalar_feasible_states=8531
q_states=8531 p1_UNSAT=8531 p1_SAT=0
pair_q_state_profile={0: 1, 3: 1, 10: 4, 36: 4, 37: 2, 43: 3,
                      52: 12, 54: 2, 55: 22, 128: 2, 155: 3,
                      193: 4, 206: 6, 208: 2, 216: 6, 219: 2,
                      220: 6}
hub_pairs_examined=1663514400
demand_states_examined=936689030
classification_sha256=30fb0bb76a200e956904e908acf36475c3b5e66fd4afed85922f165eb94758b8
status=PASS
~~~

Sections 3 through 5 exclude all 1,572 core-shell pairs.

## 6. Independent Z3 audit

A separate Z3 program rebuilds the Boolean incidence problem for all 111
pairs in the exact-dual complement. It imposes exact row sizes, row-pair
covers, triangle columns, column demands, and both side caps. It does not
import the scalar-side filter or the solver-free dynamic program.

Z3 classifies all 29,155 raw states as UNSAT. The final pinned replay
receipt is:

~~~text
cores=4 shells=393 complement_pairs=111
q_states=29155 z3_UNSAT=29155 z3_SAT=0 z3_UNKNOWN=0
classification_sha256=9b11d394ea1bd1f5cad5cc6c37ca721dfea9b3a561f23e0eaabe27b9091aec65
status=PASS
~~~

Z3 is a separate encoding and search audit, not the proof premise for the
exclusion.

## 7. Replay

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_order26_m61_duals.py \
  --geng /private/tmp/nauty289-build/geng \
  --certificates research/erdos-617-r6/r9_p93_order26_m61_duals.jsonl

python3 research/erdos-617-r6/r9_p93_order26_m61_scalar_side_verifier.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m61_duals.jsonl

python3 research/erdos-617-r6/r9_p93_order26_m61_p1_qstate_verifier.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m61_duals.jsonl \
  --workers 10

python3 research/erdos-617-r6/r9_p93_order26_m61_p1_qstate_z3_audit.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m61_duals.jsonl \
  --workers 10
~~~

## 8. Exact nonclaims

1. This theorem excludes only the order-26, degree-nine core level \(m=61\).
2. It does not exclude \(m=62,63,64\) or the degree-eight branch.
3. It does not prove \(P_3(26)\ge121\), fixed \(r=9\), or Erdős Problem 617.
4. It is a local computer-assisted result pending external review.
