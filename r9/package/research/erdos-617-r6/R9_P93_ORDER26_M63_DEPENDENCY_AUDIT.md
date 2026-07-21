# Dependency audit for fixed \(r=9\), order 26, level \(m=63\)

## Verdict

**PASS.** The human implication chain and solver-free package passed two
line audits. Two complete Boolean reconstructions passed. The second used
the source that pins the full pair profile and classification digest.

## 1. Scope checked

The candidate theorem excludes only an order-26 target graph \(H\) with

\[
 \alpha(H)\le3,
 \quad
 \omega(H)\le8,
 \quad
 e(H)\le120,
 \quad
 \delta(H)=9,
\]

when a degree-nine witness has a 16-vertex complement core with 63 edges.
No step addresses the level \(m=64\), the degree-eight branch, either
order-27 branch, or the outer recurrence.

## 2. Human implication chain

The following deductions were checked directly.

1. The degree-nine witness splits the other 25 vertices into a nine-vertex
   neighborhood \(A\) and a 16-vertex nonneighborhood \(B\).
2. For \(F=\overline{H[A]}\), an \(F\)-clique of order four is an
   independent four-set of \(H\). An independent eight-set of \(F\),
   together with the witness, is a target \(K_9\). Hence \(F\) is
   \(K_4\)-free and \(\alpha(F)\le7\).
3. For \(L=\overline{H[B]}\), an \(L\)-triangle together with the witness
   is an independent four-set of \(H\). An independent nine-set of \(L\)
   is a target \(K_9\). If a vertex of the triangle-free graph \(L\) had
   nine neighbors, those neighbors would be an independent nine-set of
   \(L\). Hence \(L\) is triangle-free, \(\alpha(L)\le8\), and
   \(\Delta(L)\le8\).
4. The target-edge count is
   \[
   e(H)=9+(36-f)+(120-63)+\sum_aq_a,
   \]
   so \(e(H)\le120\) gives \(\sum_aq_a\le f+18\).
5. Minimum degree at \(a\in A\) gives \(q_a\ge d_F(a)\). Minimum degree
   at \(b\in B\) gives column demand \(d_L(b)-6\).
6. If \(aa'\in E(F)\), failure of \(D_a\cup D_{a'}\) to cover an edge
   of \(L\) produces an independent four-set of \(H\). If three vertices
   form a triangle of \(F\), failure of their rows to cover one core
   vertex has the same consequence.
7. Summing the column demands gives total incidence at least 30. Combining
   this with \(q_a=d_F(a)+\epsilon_a\) and
   \(f+\sum_a\epsilon_a\le18\) gives \(f\ge12\).
8. The proved uniform core lemma at 63 edges gives
   \(L=K_{8,8}\) minus one edge. Its only independent eight-sets are the
   two sides. No incidence row may contain a whole side.
9. A core cover that omits one vertex from each side must omit the unique
   missing-edge endpoints and contain the other fourteen vertices. Thus a
   cover of order at most thirteen contains a complete side.

No inequality in this chain uses the conclusion of the finite search.

## 3. Finite partition

The package partitions its exact finite family as follows:

\[
 2245=1911+334,
\]

where exact rational duals exclude the first 1,911 pairs. The scalar theorem
then partitions the complement as

\[
 334=321+13.
\]

The 321 scalar exclusions are necessary-condition failures. The remaining
thirteen pairs contain 10,715 exact row-size states, all rejected by the
solver-free orbit search. There is no overlap or omitted pair between these
three stages; the catalog and complement hashes pin the partitions.

## 4. Exact-dual semantics

For each certified pair, every selected inequality is a valid lower bound
on a sum of incidence variables. Every rational weight is positive, and the
semantic verifier checks that each variable receives total coefficient at
most one. The weighted lower bound is strictly larger than the global
incidence budget \(f+18\). All comparisons use `Fraction`, not floating
point. Floating-point optimization proposes a support only; it is not a
proof premise.

The generator and proof-facing verifier use separate catalog and
certificate paths. The generator reproduces the retained JSONL byte for
byte.

## 5. Scalar and cover-13 semantics

The scalar verifier enumerates every nonnegative slack vector within the
global budget and every induced row-size vector satisfying the elementary
pair-cover lower bound. It then enumerates every integer split

\[
 q_a=x_a+y_a,
 \qquad
 0\le x_a,y_a\le7.
\]

The side-demand, cover-13 disjunction, and triangle conditions are necessary
for an incidence realization. Rejecting a scalar state is therefore sound;
accepting one is not treated as a realization.

The cover-13 lemma is checked both by the human argument and by exhaustive
enumeration of all 65,536 core subsets. A deliberate second incident missing
edge creates a mixed 13-cover and is rejected by the corruption test.

## 6. Orbit quotient and finite recurrence

The unique core has a side-preserving subgroup \(S_7\times S_7\) fixing the
two missing-edge endpoints. For an ordered hub-row pair, endpoint membership
codes and the two four-bin regular-class histograms classify its orbit.
Permuting vertices inside one histogram bin carries any pair with that
signature to any other, so the signature is complete.

Every subgroup element preserves row sizes, both forbidden full sides, core
edges, column demands, and row unions. Feasibility is constant on an orbit.
The self-test checks the analytic and direct counts in every one of the 225
ordered size cells and checks sampled transports under every adjacent
transposition generator.

After the two hub rows are fixed, the seven low shell vertices have no shell
edges among them. Their local restrictions are therefore unary, except for
the already completed hub-hub-low triangle condition. The recurrence keeps
the remaining sixteen lower-bound demands. Within one low-row domain, an
effect contained in another effect can be deleted: replacing it by the
larger effect preserves every local condition and cannot reduce any unmet
demand. Thus the antichain reduction preserves both existence and
nonexistence.

## 7. Completed gates

The final gate returned:

~~~text
source_sha256=01bbafc947100044964b044564e5da6be018d97daad8ab9adcfcccf8d84c36cd
q_states=44504 z3_UNSAT=44504 z3_SAT=0 z3_UNKNOWN=0
classification_sha256=81e6fdb89bde8d4b1663fee7cca85cd4bbf3e8091ec1746ec045d8faa2357f2f
exit_code=0 wall_seconds=4273.96
status=PASS
~~~

All source hashes, imported dependencies, tool versions, and replay
receipts are pinned in the manifest. The retained generator reproduces the
exact-dual JSONL byte for byte. The semantic dual verifier, scalar verifier,
orbit self-test, 18 corruption tests, Python compilation, Ruff, and strict
Mypy all pass on the final sources.

The first complete Boolean run used the unpinned source and returned 44,504
UNSAT, zero SAT, and zero UNKNOWN, with classification SHA-256
`81e6fdb89bde8d4b1663fee7cca85cd4bbf3e8091ec1746ec045d8faa2357f2f`.
A second read-only mathematical audit repeated the deductions in Section 2,
the cover-13 implication, the scalar necessity argument, and the two-hub
reduction. It found no new defect. This is a local audit, not external
mathematical review.

This audit proves only the stated \(m=63\) subbranch. Fixed \(r=9\) and
Erdős Problem 617 remain open.
