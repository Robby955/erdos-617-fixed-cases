# Erdős Problem 617: current fixed-\(r=9\) checkpoint

Date: 21 July 2026

## Verdict

**LOCALLY PROVED; PUBLIC PACKAGE VERIFIED; EXTERNAL REVIEW PENDING.**

The current implication chain proves:

> Every nine-coloring of the edges of \(K_{82}\) contains ten vertices
> whose induced edges omit at least one color.

The result is computer-assisted. Its human outer bridge, independent
arithmetic replay, order-27 certificate replay, and corruption suite pass.
The independent CaDiCaL audit of the order-26 \(m=64\) subbranch also
passes all 101,880 raw states with zero SAT and zero UNKNOWN. The
solver-free proof of that subbranch remains the proof premise.

The theorem commits, dependency manifest, full \(m=64\) clean-checkout
replay, order-27 replay, corruption suites, and public release layout pass.
The final 12-page PDF compiles without missing references, undefined
citations, or overfull boxes, and every rendered page has passed visual
inspection. Do not describe the fixed case as externally reviewed. Erdős
Problem 617 for arbitrary \(r\) remains open.

## 1. Exact theorem chain

Assume a nine-coloring of \(K_{82}\) in which every ten vertices see every
color. Choose a least color graph \(G\). The common reduction gives

\[
 e(G)\le369,
 \qquad
 2\le\delta(G)\le8.
\]

The terminal packages prove

\[
 P_3(26)\ge121
 \qquad\text{and}\qquad
 P_3(27)=\varnothing.
\tag{1}
\]

The new full-color bridge proves

\[
 P_4(37)\ge192.
\tag{2}
\]

Inputs (1)-(2) propagate along the degree-eight diagonal as

\[
\begin{array}{c|ccccc}
(a,n)&(4,37)&(5,46)&(6,55)&(7,64)&(8,73)\\ \hline
B_9(a,n)&192&227&264&301&338.
\end{array}
\]

Against the five outer upper bounds, the packing-order margins are

\[
 5,4,3,2,3.
\]

The other 40 outer cells were already strict or empty. Thus five target
copies of \(K_9\) are forced in the nonneighbor graph of a degree-eight
vertex, contradicting the proved \(r-4\)-block theorem.

## 2. The new 37-vertex lemma

Let \(H\) have order 37, independence number at most four, and no target
\(K_9\). If \(e(H)\le191\), the empty \(P_3(27)\) terminal forces
\(\delta(H)\ge10\), while averaging gives a degree-ten vertex \(v\).

For its ten-vertex neighborhood \(A\), let

\[
 M=45-e(H[A])
\]

be the number of missing target edges. The full-color 11-set cap gives
\(M\ge16\). Minimum degree then forces at least \(2M\) target incidences
from \(A\) into the 26 nonneighbors \(B\). The first input in (1) gives
\(e(H[B])\ge121\). Therefore

\[
 e(H)\ge10+(45-M)+121+2M=176+M\ge192,
\]

a contradiction. This is the human bridge that repairs the prior outer
recursion wall.

## 3. Terminal proof status

### Order 26

Under \(e(H)\le120\), the possible minimum degrees are eight and nine.

* Degree eight is excluded by the common 17-core two-row theorem.
* Degree nine splits into core levels \(m=56,\ldots,64\). Levels 56 through
  63 are banked. Level 64 has a solver-free proof and passed its dual,
  scalar, shell, orbit, and corruption checks. An independently encoded
  incremental CaDiCaL reconstruction returned 101,880 UNSAT, zero SAT,
  and zero UNKNOWN with classification hash
  `e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331`.

These branches give \(P_3(26)\ge121\).

### Order 27

Under the full-color cap \(e(H)\le135\), the possible minimum degrees are
nine and ten.

* Degree nine is excluded by the same common 17-core theorem.
* Degree ten is 10-regular. A human degree-sum lemma removes 282 of 332
  core types. Four LRAT shards exclude the remaining 50.

The independent aggregate replay returned

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

The same replay passed from the stable copied package, and five deliberate
artifact corruptions were rejected.

## 4. Canonical theorem files

* `research/erdos-617-r6/R9_P93_ORDER26_D8_TWO_ROW_EXCLUSION.md`
* `research/erdos-617-r6/R9_P93_ORDER26_M64_REDUCED_FRONTIER.md`
* `research/erdos-617-r6/R9_P93_ORDER27_CLOSURE.md`
* `research/erdos-617-r6/R9_D8_FULL_COLOR_BRIDGE.md`
* `research/erdos-617-r6/R9_FIXED_OUTER_AUDIT_20260721.md`

The primary new verifiers are

* `verify_r9_p93_order26_d8_two_row.py`;
* `verify_r9_p93_d10_core_degree_sum.py`;
* `verify_r9_p93_d10_certificate.py`;
* `test_r9_p93_d10_certificate_corruptions.py`;
* `verify_r9_d8_full_color_bridge.py`.

## 5. Exact remaining gates

1. Replay the lightweight outer chain from the final release commit.
2. Build and checksum the four order-27 release-asset archives.
3. Assemble and verify the public repository layout from committed source.
4. Freeze and visually inspect the final fixed-\(r=9\) PDF.
5. Seek external mathematical review while circulating the proof claim.
6. Obtain Rob's approval before any push, release, or submission.

No public post, push, email, or Erdős Problems submission has been made from
this checkpoint.
