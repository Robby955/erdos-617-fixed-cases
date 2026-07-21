# Fixed \(r=9\), order-27 degree-ten core reduction

> **SUPERSEDED DOWNSTREAM STATUS.** This scoped reduction is a dependency
> of the locally proved fixed-\(r=9\) theorem. See
> output/ERDOS_617_R9_RELEASE_HANDOFF.md for the complete chain.

## Verdict and scope

PROVED REDUCTION. Of the 332 core graphs in the 10-regular order-27
endpoint, 282 violate a necessary edge degree-sum inequality. Exactly 50
core types remain.

This theorem does not exclude those 50 cores, prove the order-27 terminal
family empty, prove fixed \(r=9\), or settle Erdős Problem 617.

## 1. Exact incidence identities

Let \(H\) be a target-color graph on 27 vertices with

\[
 \alpha(H)\le3,\qquad \omega(H)\le8,\qquad
 \delta(H)=10,\qquad e(H)=135.
\]

The degree and edge count force \(H\) to be 10-regular. Choose a vertex
\(v\), put

\[
 A=N_H(v),\qquad B=V(H)\setminus(A\cup\{v\}),
\]

and define

\[
 F=\overline{H[A]},\qquad L=\overline{H[B]}.
\]

Thus \(|A|=10\) and \(|B|=16\). For \(b\in B\), let

\[
 C_b=N_H(b)\cap A.
\]

The target degree of \(b\) inside \(B\) is \(15-d_L(b)\). Regularity gives

\[
 |C_b|=10-(15-d_L(b))=d_L(b)-5.
\tag{1}
\]

## 2. The symmetric cover inequality

The set \(F\) has no independent eight-set. Otherwise \(v\), together
with those eight vertices of \(A\), would form a target \(K_9\). Therefore

\[
 \alpha(F)\le7,qquad \tau(F)=10-\alpha(F)\ge3.
\tag{2}
\]

Fix an edge \(bb'\in E(L)\). The set \(C_b\cup C_{b'}\) is a vertex cover
of \(F\). If an edge \(aa'\in E(F)\) avoided this union, then
\(a,a',b,b'\) would be an independent four-set in \(H\): the two within-part
pairs are complement edges, and the four cross-pairs are absent by the
definition of the columns.

Equations (1)-(2) now give

\[
 3\le |C_b\cup C_{b'}|
 \le |C_b|+|C_{b'}|
 =d_L(b)+d_L(b')-10.
\]

Hence every core edge satisfies

\[
 \boxed{d_L(b)+d_L(b')\ge13.}
\tag{3}
\]

## 3. Exact finite reduction

The verifier reconstructs the complete 332-core catalogue from

~~~text
geng -q -t -d5 -D8 16 56:64
~~~

and independently checks the inherited independence and subset-density
conditions. It then applies (3) directly. The minimum edge degree-sum
profile on the full catalogue is

~~~text
10: 19
11: 102
12: 161
13: 38
14: 10
15: 1
16: 1
~~~

The 50 survivors have edge-level profile

~~~text
56: 8
57: 8
58: 10
59: 9
60: 7
61: 4
62: 2
63: 1
64: 1
~~~

The pinned receipts are

~~~text
catalog_sha256=24a2b9d62d8c7612280188c93be9164e7306ae0c83db12a3872c061bde303510
survivor_sha256=6d573529569ecc950e4e9e98c89d9ae3c95273089bba8d3cd63b1d83e862f508
classification_sha256=f6aa267f6cc54dccc04bbfe66068788cc6f75ea528a04b8d63bdb1b9d5795c2a
~~~

The cases with minimum sum 13 have an additional exact consequence: for
an equality edge \(bb'\), the columns \(C_b,C_{b'}\) are disjoint and their
union is a three-vertex cover of \(F\). This equality structure is the next
active reduction for the 38 boundary cores.

## 4. Replay

Run

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_d10_core_degree_sum.py \
  --geng /private/tmp/nauty289-build/geng
~~~

The verifier uses no SAT solver or floating-point calculation. Catalogue
completeness depends on nauty `geng`.
