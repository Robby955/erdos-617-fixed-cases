# Fixed \(r=9\), order \(26\), degree-nine level \(m=63\)

## Status

**LOCALLY PROVED.** There is no order-26, degree-nine target graph under
\(e(H)\le120\) whose 16-vertex complement core has 63 edges.

The exact-dual, scalar, and solver-free orbit components below have passed
their production replays. Two independent Boolean reconstructions reject
all 44,504 raw states with zero SAT and zero UNKNOWN. The second run used
the source that pins its complete pair profile and classification digest.

This result concerns one level of one minimum-degree branch. It does not
exclude the level \(m=64\), the degree-eight branch, either order-27 branch,
fixed \(r=9\), or Erdős Problem 617.

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
 e(L)=63.
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 q_a=|D_a|.
\]

The inherited conditions used below are:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. For every \(S\subseteq B\) of order at least ten,
   \[
   e_L(S)\ge8p_9(|S|),
   \qquad
   p_9(t)=(9-b)\binom a2+b\binom{a+1}{2}
   \quad(t=9a+b,\ 0\le b<9). \tag{1}
   \]
   The other eight colors each have independence number at most nine on
   \(S\), so the complementary Turán bound supplies at least
   \(p_9(|S|)\) edges in each color.
3. \(F\) is \(K_4\)-free and \(\alpha(F)\le7\).
4. The target-edge ledger gives
   \[
   \sum_{a\in A}|D_a|\le f+18. \tag{2}
   \]
5. Minimum degree gives
   \[
   |D_a|\ge d_F(a), \tag{3}
   \]
   and
   \[
   \sum_{a\in A}\mathbf 1_{b\in D_a}\ge d_L(b)-6
   \qquad(b\in B). \tag{4}
   \]
6. If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) is a vertex cover of
   \(L\).
7. If \(a,a',a''\) form a triangle of \(F\), then
   \[
   D_a\cup D_{a'}\cup D_{a''}=B. \tag{5}
   \]
8. No \(D_a\) contains an independent eight-set of \(L\), since such a
   set is an eight-clique in \(H[B]\) and would form a target \(K_9\)
   with \(a\).

Summing (4) over \(B\) gives

\[
 \sum_{a\in A}|D_a|
 \ge 2e(L)-6|B|=30. \tag{6}
\]

Write \(q_a=d_F(a)+\epsilon_a\), where \(\epsilon_a\ge0\). Equations
(2) and (3) give

\[
 f+\sum_a\epsilon_a\le18. \tag{7}
\]

Since \(\sum_a q_a=2f+\sum_a\epsilon_a\), equations (6) and (7) imply
\(f\ge12\). This reduces the raw 3,026-shell catalog to the 2,245 exact
shells with \(12\le f\le18\).

## 2. Core structure and the cover-13 lemma

The uniform core theorem gives

\[
 L=K_{8,8}-xy, \tag{8}
\]

where \(xy\) is one cross-edge. Write the bipartition as \(X\cup Y\).
The only independent eight-sets are \(X\) and \(Y\). Consequently,

\[
 |D_a\cap X|\le7,
 \qquad
 |D_a\cap Y|\le7. \tag{9}
\]

The column demands on both sides are

\[
 \sum_{b\in X}(d_L(b)-6)
 =
 \sum_{b\in Y}(d_L(b)-6)
 =15. \tag{10}
\]

The small-cover threshold improves from twelve at \(m=62\) to thirteen.
Indeed, suppose a vertex cover \(C\) contains neither side. Choose
\(x'\in X\setminus C\) and \(y'\in Y\setminus C\). The pair \(x'y'\)
must be the unique deleted edge \(xy\). Every other vertex of \(X\cup Y\)
then belongs to \(C\), so \(|C|\ge14\). Hence every cover of order at most
thirteen contains \(X\) or \(Y\).

The scalar verifier also checks all \(2^{16}\) core subsets. It finds 438
vertex covers through order thirteen, every one containing a complete side,
and minimum mixed-cover order fourteen.

## 3. Exact catalogs and rational duals

The generator and semantic verifier separately reconstruct the unique core
and all 2,245 exact shells. Their catalog hashes are

~~~text
core_catalog_sha256=20302c025a85684c659534cc704508b0311c33282dc8d0b19b683fa033855044
shell_catalog_sha256=f5e13567a0a977da594eacdaa8b945ba416f13ad507121bb90b91c8f100c43b7
~~~

For 1,911 core-shell pairs, the retained certificate gives nonnegative
rational weights on selected instances of (3), (4), the row-pair cover
conditions, and (5). Every incidence variable has total coefficient at
most one, while the weighted right side is strictly greater than \(f+18\).
This contradicts (2).

The semantic verifier rebuilds every catalog entry and every named
inequality, then checks all rational arithmetic exactly. Its receipt is:

~~~text
cores=1 shells=2245 pairs=2245
core_structure=K8,8-minus-1 demand_profile={(15, 15): 1}
strict_duals_verified=1911 uncertified_pairs=334
semantic_sha256=877eca5a4a64b1a1484f1036faeb3dbfdc5033c8b6f39b4af8593af86a025acf
uncertified_pair_sha256=f0e775bc61c40d56c54e221f6f47d216939671c6ac2d65c62eace6fa480ebd2b
data_sha256=57ef4123b3053689f0dd72aa256bf2975c069aa0d0785e2269e74c513ae52a2f
status=PASS
~~~

The retained generator reproduces the certificate file byte for byte.

## 4. Scalar side-count reduction

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
 y_a\le7. \tag{11}
\]

If \(aa'\in E(F)\) and \(q_a+q_{a'}\le13\), the cover-13 lemma gives

\[
 x_a+x_{a'}\ge8
 \quad\hbox{or}\quad
 y_a+y_{a'}\ge8. \tag{12}
\]

For every triangle \(a,a',a''\) of \(F\), equation (5) gives

\[
 x_a+x_{a'}+x_{a''}\ge8,
 \qquad
 y_a+y_{a'}+y_{a''}\ge8. \tag{13}
\]

The scalar verifier enumerates all row-size vectors allowed by (7), then
all integer side splits allowed by (10)--(13). It uses exact integer
arithmetic. The stronger threshold thirteen removes four states that pass
the old threshold twelve. Its receipt is:

~~~text
complement_pairs=334
cover13_core_profile={(438, 14): 1}
pair_profile={(2, True): 13, (3, False): 308, (4, False): 13}
cover13_removed_states=4
raw_q_states=44504 scalar_feasible_q_states=10715
classification_sha256=675f090f8a175d22e327186c69f578dbeda7fba113ec0e644465a0a4f1260b20
status=PASS
~~~

Thus 321 of the 334 complement pairs are excluded. Each of the thirteen
surviving shells has a two-vertex cover of its edges.

## 5. Solver-free orbit exhaustion

For each surviving shell, choose two vertices that cover all shell edges.
The other seven shell vertices form an independent set. Fixing the two hub
rows leaves unary low-row domains, the completed triangle conditions, and
the sixteen column demands.

In (8), the automorphisms that fix the two missing-edge endpoints form

\[
 S_7\times S_7. \tag{14}
\]

An ordered hub-row pair is classified by its two membership codes on the
fixed endpoints and its four-bin membership histogram on each regular
seven-vertex class. These data are complete orbit invariants for (14).
The self-test directly constructs all 201,601 ordered row-pair orbits,
compares all 225 row-size cells with the analytic profile, and runs 95,592
transport checks.

For one representative of every relevant orbit, the verifier constructs
the exact domain of each low row and uses a memoized finite-state recurrence
to meet all column demands. Its production receipt is:

~~~text
two_hub_pairs=13 scalar_feasible_states=10715
q_states=10715 orbit_UNSAT=10715 orbit_SAT=0
pair_q_state_profile={220: 1, 449: 1, 456: 1, 477: 2,
                      640: 2, 699: 2, 1233: 2, 1746: 2}
orbit_representatives=40203600
candidate_orbits=2658674
demand_states=363118868
demand_transitions=362801242
classification_sha256=05b98ab8efd125a447a92e1e5d63b0531430dd3a715449c363c0f87cfb7660e0
orbit_receipt_sha256=16ce28c3f5ca0e2c1930aa9def97adcefbdac65339420cd0295209a092be7a35
status=PASS
~~~

Together, Sections 3 through 5 exclude all 2,245 exact core-shell pairs,
conditional on the checked finite-state implementation.

## 6. Independent Boolean reconstruction

The independent Boolean program rebuilds all 334 pairs outside the exact-dual
set and all 44,504 raw row-size states. It imports neither the scalar filter
nor the orbit search. The first complete run returned

~~~text
cores=1 shells=2245 complement_pairs=334
chunks=598 chunk_size=128
q_states=44504 z3_UNSAT=44504 z3_SAT=0 z3_UNKNOWN=0
classification_sha256=81e6fdb89bde8d4b1663fee7cca85cd4bbf3e8091ec1746ec045d8faa2357f2f
status=PASS
exit_code=0 wall_seconds=5115
~~~

The first run used source SHA-256
`46cb9507cbdf168e2498a37f95eb9009989b3f66be304c333a225864aa6de346`
with the profile and digest temporarily unpinned. Those values are now
pinned in source SHA-256
`01bbafc947100044964b044564e5da6be018d97daad8ab9adcfcccf8d84c36cd`.
The pinned replay returned

~~~text
cores=1 shells=2245 complement_pairs=334
chunks=2980 chunk_size=16
q_states=44504 z3_UNSAT=44504 z3_SAT=0 z3_UNKNOWN=0
classification_sha256=81e6fdb89bde8d4b1663fee7cca85cd4bbf3e8091ec1746ec045d8faa2357f2f
status=PASS
exit_code=0 wall_seconds=4273.96
~~~

Z3 is an encoding and search audit, not the solver-free proof premise.

## 7. Replay and exact nonclaims

The retained generator has reproduced the dual JSONL byte for byte:

~~~text
replay_lines=1912 replay_bytes=942286
replay_sha256=57ef4123b3053689f0dd72aa256bf2975c069aa0d0785e2269e74c513ae52a2f
canonical_sha256=57ef4123b3053689f0dd72aa256bf2975c069aa0d0785e2269e74c513ae52a2f
cmp_status=PASS
~~~

The generator writes its output and prints its receipt only after it has
processed all 2,245 pairs. A short foreground wait therefore produces no
progress output and no partial file; this is expected behavior, not a failed
replay.

The dependency-closed manifest and receipts are under
`artifacts/r9-order26-m63/`. The retained generator replay is byte-identical
to the canonical exact-dual data. The semantic, scalar, orbit self-test,
corruption, static, and pinned Boolean checks all pass on the final sources.

1. The level \(m=63\) is locally proved by this package.
2. This work does not exclude \(m=64\) or the degree-eight branch.
3. It does not prove \(P_3(26)\ge121\), fixed \(r=9\), or Erdős Problem
   617.
4. No exploratory SAT output is used as a proof premise.
