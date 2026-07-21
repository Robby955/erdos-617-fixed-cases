# Fixed \(r=9\), order \(26\), degree-nine level \(m=62\)

## Status

The core level \(m=62\) in the order-26 degree-nine branch is locally
proved impossible. The proof combines 2,142 exact rational duals, a
solver-free scalar exclusion for 117 of the remaining 152 core-shell pairs,
and a symmetry-quotiented solver-free exhaustion of 11,706 row-size states
for the other 35 pairs. A separate Z3 program reconstructs and excludes all
38,342 raw Boolean states.

This result does not exclude the degree-eight branch or the degree-nine
levels \(m=63,64\). It does not prove \(P_3(26)\ge121\), fixed \(r=9\), or
Erdős Problem 617.

## 1. Setup

Let \(H\) be a target-color graph on 26 vertices inherited from a
hypothetical balanced nine-coloring, with

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
\(B=V(H)\setminus(A\cup\{v\})\). Thus \(|A|=9\) and \(|B|=16\). Define

\[
 F=\overline{H[A]},
 \qquad
 L=\overline{H[B]},
 \qquad
 f=e(F),
 \qquad
 e(L)=62.
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 q_a=|D_a|.
\]

The inherited conditions used below are:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. For every \(S\subseteq B\) of order at least ten, the inherited
   core-density inequality is
   \[
   e_L(S)\ge8p_9(|S|),
   \qquad
   p_9(t)=(9-b)\binom a2+b\binom{a+1}{2}
   \quad(t=9a+b,\ 0\le b<9). \tag{0}
   \]
   Indeed, \(L[S]\) is the edge-disjoint union of the other eight color
   graphs, and each has independence number at most nine. The
   complementary Turán bound supplies at least \(p_9(|S|)\) edges in each.
3. \(F\) is \(K_4\)-free and \(\alpha(F)\le7\).
4. The target-edge ledger gives
   \[
   \sum_{a\in A}|D_a|\le f+17. \tag{1}
   \]
5. Minimum degree gives
   \[
   |D_a|\ge d_F(a), \tag{2}
   \]
   and
   \[
   \sum_{a\in A}\mathbf 1_{b\in D_a}\ge d_L(b)-6
   \qquad(b\in B). \tag{3}
   \]
6. If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) is a vertex cover of
   \(L\).
7. If \(a,a',a''\) form a triangle of \(F\), then
   \[
   D_a\cup D_{a'}\cup D_{a''}=B. \tag{4}
   \]
8. Neither bipartition side of \(L\) is contained in a single \(D_a\),
   since that side is an eight-clique in \(H[B]\) and would form a target
   \(K_9\) with \(a\).

Summing (3) over \(B\) gives

\[
 \sum_{a\in A}|D_a|
 \ge 2e(L)-6|B|=28.
\]

Together with (1), this implies \(f\ge11\), so levels \(f\le7\) are
impossible. The semantic shell generator starts at \(f=8\), so it
deliberately checks a conservative superset; levels \(f=8,9,10\) are
rejected by the incidence inequalities rather than omitted from the search.

## 2. Exact core structure

The uniform core lemma gives

\[
 L=K_{8,8}-Q,
 \qquad
 |Q|=2.
\tag{5}
\]

There are two isomorphism types: the edges of \(Q\) are either disjoint or
share one endpoint. Write the bipartition as \(X\cup Y\).

The only independent eight-sets of \(L\) are \(X\) and \(Y\). A mixed
independent eight-set with \(p\) vertices in one side would require at least

\[
 p(8-p)\ge7>|Q|
\]

missing cross-edges. Consequently,

\[
 |D_a\cap X|\le7,
 \qquad
 |D_a\cap Y|\le7.
\tag{6}
\]

Both core types have side-demand sums

\[
 \sum_{b\in X}(d_L(b)-6)
 =\sum_{b\in Y}(d_L(b)-6)=14.
\tag{7}
\]

The uniform small-cover lemma says that every vertex cover of \(L\) of
order at most 12 contains all of \(X\) or all of \(Y\).

## 3. Exact catalogs and rational duals

Write

\[
 q_a=d_F(a)+\epsilon_a,
 \qquad
 \epsilon_a\ge0.
\]

Equations (1) and (2) give

\[
 f+\sum_a\epsilon_a\le17.
\tag{8}
\]

The semantic verifier reconstructs every unlabelled core and shell that
satisfies the inherited conditions. It obtains

\[
 2\text{ cores},
 \qquad
 1{,}147\text{ shells},
 \qquad
 2{,}294\text{ core-shell pairs}.
\]

For 2,142 pairs, the certificate file gives nonnegative rational weights on
selected inequalities (2)--(4) and the row-pair cover inequalities. In each
certificate, every incidence variable has total coefficient at most one and
the weighted right side is strictly greater than \(f+17\). This contradicts
(1).

The verifier rebuilds every catalog entry and named inequality, checks every
rational coefficient exactly, and pins the certificate data, semantic
result, and 152-pair complement:

~~~text
cores=2 shells=1147 pairs=2294
strict_duals_verified=2142 uncertified_pairs=152
semantic_sha256=e6e3487f1ea47e8fb254de021102e6139cbb297c92d1fd739137d8c41454ad45
uncertified_pair_sha256=f5a0febbfb028eb99aa4201df31232ec46ded7f1c4299011d753d29b031532fb
data_sha256=d80b2e95446ca6771c6c64591c43addc256e49c4bf099e8e09e7c648ad013796
status=PASS
~~~

## 4. Scalar side-count exclusion

Put

\[
 x_a=|D_a\cap X|,
 \qquad
 y_a=|D_a\cap Y|.
\]

Then

\[
 x_a+y_a=q_a,
 \qquad
 x_a\le7,
 \qquad
 y_a\le7.
\tag{9}
\]

If \(aa'\in E(F)\) and \(q_a+q_{a'}\le12\), then
\(D_a\cup D_{a'}\) is a cover of order at most 12. The core lemma gives

\[
 x_a+x_{a'}\ge8
 \quad\hbox{or}\quad
 y_a+y_{a'}\ge8.
\tag{10}
\]

For every triangle \(a,a',a''\) of \(F\), equation (4) gives

\[
 x_a+x_{a'}+x_{a''}\ge8,
 \qquad
 y_a+y_{a'}+y_{a''}\ge8.
\tag{11}
\]

The scalar verifier enumerates every row-size vector allowed by (8), then
every integer side split allowed by (7) and (9)--(11). It uses only integer
arithmetic. Its pinned receipt is:

~~~text
complement_pairs=152
distinct_shells=89
pair_profile={(2, True): 35, (3, False): 107, (4, False): 10}
raw_q_states=38342 scalar_feasible_q_states=11706
classification_sha256=95c95dd18f15be8887e0d302ae5173cae87a7891d48faaf5754de16bf37c876c
status=PASS
~~~

Thus the scalar theorem excludes 117 pairs. The 35 survivors all have a
two-vertex cover of the shell edges.

## 5. Solver-free orbit exhaustion

For each surviving shell, choose its two hub vertices. The other seven
shell vertices form an independent set, so fixing the two hub rows leaves
only unary row domains, the completed triangle constraints, and the sixteen
column demands.

The two core types have explicit side-preserving automorphism subgroups:

\[
 S_6\times S_6\times S_2
 \quad\hbox{and}\quad
 S_7\times S_2\times S_6.
\tag{12}
\]

For the disjoint-edge core, an ordered hub-row pair is classified by its
four membership counts on each six-vertex regular class and the unordered
pair of endpoint-code pairs on the two missing edges. For the shared-endpoint
core, it is classified by the exceptional center code and four membership
counts on classes of orders seven, two, and six. These signatures are
complete orbit invariants for the subgroups in (12).

Every subgroup element preserves row sizes, both side caps, core covers,
row unions, and the column-demand vector. Feasibility is therefore constant
on each ordered hub-pair orbit. The verifier takes one explicit
representative per orbit, constructs the exact finite domain of every low
row, and uses a memoized dynamic program to meet the column demands. Its
pinned receipt is:

~~~text
two_hub_pairs=35 scalar_feasible_states=11706
q_states=11706 p1_UNSAT=11706 p1_SAT=0
pair_q_state_profile={55: 2, 121: 1, 128: 1, 155: 2, 192: 2,
                      193: 2, 206: 4, 216: 4, 220: 4, 456: 2,
                      477: 3, 640: 4, 699: 4}
orbit_representatives=164021520
candidate_orbits=5073750
demand_states=108285865
demand_transitions=107883823
classification_sha256=16d6bc92eb29c884f33da831a5f6aac24aad03dcee44eb51755681efdbdcd408
orbit_receipt_sha256=cc53bf5ec3d04d68a5a0962eeb2e19bc8f9f4b5e78a6379a9c140b702cffb441
status=PASS
~~~

The retained self-test compares the analytic orbit count with direct
representative generation for all 450 ordered row-size pairs across both
cores. It directly checks 1,237,252 representatives, all subgroup
generators, and sampled transports of covers and signatures:

~~~text
direct_profile_size_comparisons=450 representatives_checked=1237252
self_test_receipt_sha256=b4a5736b62f0f497b89a29ddb43758d9cf217b2157b39725c0ad7a65f4c4b61a
status=PASS
~~~

Sections 3 through 5 exclude all 2,294 core-shell pairs.

## 6. Independent Z3 audit

A separate Z3 program rebuilds the Boolean incidence problem for all 152
pairs in the exact-dual complement. It imposes exact row sizes, row-pair
covers, triangle columns, column demands, and both side caps. It does not
import the scalar-side filter or the solver-free orbit dynamic program.

Z3 classifies all 38,342 raw states as UNSAT. Its pinned receipt is:

~~~text
cores=2 shells=1147 complement_pairs=152
q_states=38342 z3_UNSAT=38342 z3_SAT=0 z3_UNKNOWN=0
classification_sha256=4cc50b307cff16d76f896f639b57b24dcfe8c0f5b9069f0d3442b9649a808274
status=PASS
~~~

Z3 is an independent encoding and search audit, not the proof premise.

## 7. Corruption and replay tests

The package tests reject a changed byte, truncation, a removed record, a
duplicate pair, bad header fields, an unknown graph, a malformed rational
weight, coefficient overload, and a changed scalar-classification digest.
All twelve tests pass.

The complete replay commands are:

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_order26_m62_duals.py \
  --geng /private/tmp/nauty289-build/geng \
  --certificates research/erdos-617-r6/r9_p93_order26_m62_duals.jsonl

python3 research/erdos-617-r6/r9_p93_order26_m62_scalar_side_verifier.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m62_duals.jsonl

python3 research/erdos-617-r6/r9_p93_order26_m62_p1_orbit_verifier.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m62_duals.jsonl \
  --workers 15

python3 research/erdos-617-r6/r9_p93_order26_m62_p1_qstate_z3_audit.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m62_duals.jsonl \
  --workers 10

python3 -m pytest -q \
  research/erdos-617-r6/test_r9_p93_order26_m62_package.py
~~~

The orbit self-test can be replayed separately with

~~~sh
python3 research/erdos-617-r6/r9_p93_order26_m62_p1_orbit_verifier.py \
  --self-test
~~~

The dependency-closed package manifest is

~~~text
research/erdos-617-r6/artifacts/r9-order26-m62/manifest.json
~~~

It pins every canonical source and data file, all direct and transitive
imported dependencies, the `geng` binary, tool versions, and the saved
replay receipts. The retained generator reproduces the dual JSONL byte for
byte.

## 8. Exact nonclaims

1. This theorem excludes only the order-26, degree-nine core level \(m=62\).
2. It does not exclude \(m=63,64\) or the degree-eight branch.
3. It does not prove \(P_3(26)\ge121\), fixed \(r=9\), or Erdős Problem 617.
4. It is a local computer-assisted result pending external review.
