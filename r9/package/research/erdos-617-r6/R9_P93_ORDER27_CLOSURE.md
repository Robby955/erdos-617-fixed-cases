# Fixed \(r=9\), closure of the 27-vertex three-layer terminal

> **SUPERSEDED DOWNSTREAM STATUS.** The terminal theorem below remains
> valid. Its statements that the outer implication and fixed case remained
> open are historical. Fixed \(r=9\) is now locally proved; see
> output/ERDOS_617_R9_RELEASE_HANDOFF.md.

## Verdict and scope

PROVED LOCALLY; COMPUTER-ASSISTED. In a hypothetical nine-coloring of
\(K_{82}\) in which every ten vertices see every color, no induced target
graph \(H\) on 27 vertices can satisfy

\[
 \alpha(H)\le3,
 \qquad
 \omega(H)\le8.
\tag{1}
\]

Equivalently, the fixed-parameter terminal family denoted \(P_3(27)\) is
empty. The degree-nine branch is excluded by a short human argument using
the full-color 11-set cap. The degree-ten branch is excluded by a
50-instance LRAT package after a human reduction from 332 core types.

This theorem closes the 27-vertex terminal dependency. It is not, by itself,
the complete fixed-\(r=9\) proof. The downstream full-color bridge and outer
recursion complete that fixed case locally. Erdős Problem 617 remains open.

## 1. Degree split

Let \(H\) satisfy (1). The full-color induced-density inequality gives

\[
 e(H)\le D_9(27)=135.
\tag{2}
\]

Every vertex of \(H\) has degree at least nine. If a vertex had degree at
most eight, its nonneighbors would contain at least 18 vertices. Their
induced target graph would have independence number at most two and clique
number at most eight, contrary to the colored terminal-core theorem.

Equation (2) gives average degree at most ten. Hence

\[
 \delta(H)\in\{9,10\}.
\tag{3}
\]

## 2. The degree-nine branch

Suppose \(\delta(H)=9\), choose a degree-nine vertex \(v\), and put

\[
 A=N_H(v),
 \qquad
 B=V(H)\setminus(A\cup\{v\}).
\]

Thus \(|A|=9\) and \(|B|=17\). Write

\[
 F=\overline{H[A]},
 \qquad
 L=\overline{H[B]}.
\]

The checked 17-vertex core catalogue gives a vertex \(z\in B\) such that
\(L-z\) is bipartite with two parts of order eight and \(d_L(z)\le5\).
The graph \(F\) has an edge \(cu\). The set
\(N_H(c)\cap B\cup N_H(u)\cap B\) covers every edge of \(L\), while the
full-color cap

\[
 D_9(11)=39
\]

bounds its intersections with both bipartition sides. The two possible
roles of \(z\) then force more missing cross-pairs than \(L\) has. This is
the common 17-core two-row exclusion in
`R9_P93_ORDER26_D8_TWO_ROW_EXCLUSION.md`.

Therefore the degree-nine branch is empty.

## 3. The degree-ten branch

Suppose \(\delta(H)=10\). Equations (2)-(3) force

\[
 e(H)=135
 \qquad\hbox{and}\qquad
 H\text{ is 10-regular}.
\tag{4}
\]

Choose any vertex \(v\). Put

\[
 A=N_H(v),
 \qquad
 B=V(H)\setminus(A\cup\{v\}),
 \qquad
 F=\overline{H[A]},
 \qquad
 L=\overline{H[B]}.
\tag{5}
\]

Then \(|A|=10\), \(|B|=16\), and \(L\) is one of 332 checked
nonisomorphic core types. For \(b\in B\), let

\[
 C_b=\{a\in A:ab\in E(H)\}.
\]

Exact regularity gives

\[
 |C_b|=d_L(b)-5.
\tag{6}
\]

The shell-complement graph \(F\) has independence number at most seven, so
\(\tau(F)\ge3\). If \(bb'\in E(L)\), then \(C_b\cup C_{b'}\) covers
\(F\); otherwise an uncovered edge of \(F\), together with \(b,b'\),
would be an independent four-set in \(H\). Consequently

\[
 d_L(b)+d_L(b')\ge13
 \qquad\text{for every }bb'\in E(L).
\tag{7}
\]

The independent core reconstruction finds 332 valid types. Condition (7)
rejects 282 and leaves exactly 50. Their index digest is

~~~text
e9c743eef1f89309733e1a4eaecd74fb6af862a55dd457dfee8b2604bf30037f
~~~

For each survivor, a deterministic CNF encodes a relaxation of (1), (4),
and (5). It includes exact degree and edge counts, all independent-four
splits, all mixed target \(K_9\) splits, the inherited 11-set cap, and the
local deletion inequalities. Omitting further colored constraints makes
the formula weaker than the true configuration, so UNSAT is a sound
exclusion.

The four generated shards contain exactly the 50 survivor indices. An
independent verifier reconstructs all 332 cores, recomputes the survivor
set, rebuilds every CNF without importing the generator, compares clause
multisets, checks the unary totalizer semantics, and replays every LRAT
proof. Its aggregate receipt is

~~~text
r9 P3 d10 certificate semantic audit: PASS
packages_verified=4
cases_reconstructed=332
cnfs_verified=50
clauses_verified=9100515
totalizer_merges_verified=79574
totalizer_shapes_verified=83
totalizer_states_verified=108839
lrat_proofs_replayed=50
~~~

Thus the degree-ten branch is empty.

## 4. Conclusion

The two cases in (3) are impossible. Therefore no \(H\) satisfying (1)
exists, proving the 27-vertex terminal closure.

## 5. Replay and artifacts

The proof sources are

* `R9_P93_ORDER26_D8_TWO_ROW_EXCLUSION.md`;
* `verify_r9_p93_order26_d8_two_row.py`;
* `R9_P93_D10_CORE_DEGREE_SUM_REDUCTION.md`;
* `verify_r9_p93_d10_core_degree_sum.py`;
* `r9_p93_d10_certificate_generator.py`;
* `verify_r9_p93_d10_certificate.py`.

The local replay-complete shards are stored under
`output/erdos-617-artifacts/r9-p93-order27-d10-20260721/`. Their manifest
SHA-256 values, in residue order zero through three, are

~~~text
f332adb9327c02b2b9964a1d781baae75d27371a83995dc3c1f7393b35c09cba
0df642bb21e52310ec19f479d5ec62fe179a0b075738643bb165baeef7dcda40
7427d8c307411374f332056bdd3638ff26c9d70c6c1283458d87f6313fd1bc2f
e1cc2b4b6f2643d16bc3ba64d50e7e1e9cf73d7043a19f632571bf328c158d1d
~~~

Run

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_d10_certificate.py \
  --geng /private/tmp/nauty289-build/geng \
  --package output/erdos-617-artifacts/r9-p93-order27-d10-20260721/erdos-617-r9-p93-d10-reduced-shard-0-of-4-20260721 \
  --package output/erdos-617-artifacts/r9-p93-order27-d10-20260721/erdos-617-r9-p93-d10-reduced-shard-1-of-4-20260721 \
  --package output/erdos-617-artifacts/r9-p93-order27-d10-20260721/erdos-617-r9-p93-d10-reduced-shard-2-of-4-20260721 \
  --package output/erdos-617-artifacts/r9-p93-order27-d10-20260721/erdos-617-r9-p93-d10-reduced-shard-3-of-4-20260721 \
  --lrat-check /private/tmp/drat-trim-erdos617/lrat-check \
  --require-degree-sum-survivors \
  --require-lrat
~~~

The theorem and replay have not received external mathematical review.
