# Fixed \(r=9\), order 26, degree-eight shell classification

> **SUPERSEDED DOWNSTREAM STATUS.** This scoped reduction is a dependency
> of the locally proved fixed-\(r=9\) theorem. See
> output/ERDOS_617_R9_RELEASE_HANDOFF.md for the complete chain.

## Verdict and scope

PROVED REDUCTION. In the order-26, minimum-degree-eight branch under
\(e(H)\le120\), every compatible eight-vertex shell is

\[
 K_{1,f}\mathbin{\dot\cup}(7-f)K_1
 \qquad(1\le f\le7).
\]

Thus the two 17-vertex core levels \(m=64,65\), which contain fourteen
core types in total, reduce to at most 98 fixed core-shell systems.
The companion theorem
`R9_P93_ORDER26_D8_TWO_ROW_EXCLUSION.md` now excludes all 98 systems by
a common two-row argument. In fact, that argument needs only one shell
edge, so this classification is no longer a dependency of the exclusion.

This theorem does not exclude those systems, prove \(P_3(26)\ge121\),
prove fixed \(r=9\), or settle Erdős Problem 617.

## 1. Incidence reduction

Let \(H\) be a graph on 26 vertices with

\[
 \alpha(H)\le3,\qquad
 \omega(H)\le8,\qquad
 \delta(H)=8,\qquad
 e(H)\le120.
\]

Choose a degree-eight vertex \(v\), put \(A=N_H(v)\), and put
\(B=V(H)\setminus(A\cup\{v\})\). Thus \(|A|=8\) and \(|B|=17\).
Define

\[
 F=\overline{H[A]},\qquad
 L=\overline{H[B]},\qquad
 f=e(F),\qquad
 m=e(L).
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 q_a=|D_a|.
\]

The core reduction gives \(m\in\{64,65\}\). The target-edge ledger is

\[
 e(H)=8+(28-f)+(136-m)+\sum_aq_a,
\]

and hence

\[
 \sum_aq_a\le f+m-52.
\tag{1}
\]

Minimum degree at a shell vertex gives

\[
 q_a\ge d_F(a).
\tag{2}
\]

The graph \(F\) is \(K_4\)-free. It is nonempty, because an empty \(F\)
would make \(A\cup\{v\}\) a target \(K_9\).

The graph \(L\) is triangle-free and satisfies \(\alpha(L)\le8\).
Therefore every vertex cover of \(L\) has order at least

\[
 |B|-\alpha(L)\ge9.
\tag{3}
\]

If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) covers every edge of \(L\);
otherwise two uncovered core endpoints together with \(a,a'\) form an
independent four-set of \(H\). Equations (2)-(3) give

\[
 q_a+q_{a'}\ge9.
\tag{4}
\]

If \(a,a',a''\) form a triangle of \(F\), then their three rows cover all
of \(B\). Thus

\[
 q_a+q_{a'}+q_{a''}\ge17.
\tag{5}
\]

Write

\[
 q_a=d_F(a)+\epsilon_a,\qquad \epsilon_a\ge0.
\]

Since \(\sum_ad_F(a)=2f\), equation (1) becomes

\[
 f+\sum_a\epsilon_a\le m-52\in\{12,13\}.
\tag{6}
\]

In particular, (2) and (1) give \(1\le f\le13\).

## 2. Exact finite lemma

The verifier enumerates every unlabelled \(K_4\)-free graph on eight
vertices with \(1\le f\le13\). There are 4,355 such graphs, with edge
profile

~~~text
1:1, 2:2, 3:5, 4:11, 5:24, 6:55, 7:113,
8:214, 9:381, 10:606, 11:849, 12:1033, 13:1061.
~~~

For every graph and each offset in \(\{12,13\}\), it enumerates every
nonnegative integral vector \((\epsilon_a)_{a\in A}\) allowed by (6).
It then checks (4) on every shell edge and (5) on every shell triangle.
This is a direct exhaustive check, with no SAT solver or floating-point
calculation.

The offset-twelve run checks 1,095,993 slack states and leaves 5,986
states. The offset-thirteen run checks 2,378,044 slack states and leaves
15,221 states. At both offsets, the only surviving graph types are

~~~text
G???C?  G???E?  G???F?  G???F_  G???Fo  G???Fw  G???F{
~~~

with respective edge counts \(1,\ldots,7\). These are exactly

\[
 K_{1,f}\mathbin{\dot\cup}(7-f)K_1
 \qquad(1\le f\le7).
\]

The pinned receipts are

~~~text
catalog_sha256=067d049a8474ad85a7ecc2780530ca00180ebc7765d0e5a5f943a0dc5fa56e45
offset_12_classification_sha256=16cf23274b905f0d6ec6595efd70999671ec41afd850d06ecc16e4d8a3bea3cc
offset_12_frontier_sha256=2c19b1abb5225632aa57f143f030122481129abab245c9e1d9b301a47f88cfa4
offset_13_classification_sha256=ae4e194a43f9d66f278e7b5fc6d4bd3bce0d1cef81d17f9a85ecf1fea379048f
offset_13_frontier_sha256=b3f6c8093c887aa5d9ed6d64b04b3a4afb6ceb647ecce92cb72ea23f6f5c3f59
~~~

## 3. Resulting finite frontier

For every surviving shell, the seven noncenter shell vertices form a
target clique. The remaining incidence problem has eight rows on a fixed
17-vertex core, or 136 primary Boolean incidences. There are ten core
types at \(m=64\) and four at \(m=65\), so the complete first frontier
has at most

\[
 7(10+4)=98
\]

fixed core-shell pairs.

An independent core-catalog replay starts from all 36 triangle-free
17-vertex graphs in the two edge levels and retains exactly these fourteen
after the inherited independence and subset-density tests. Every retained
core has a minimum-degree vertex whose deletion leaves a bipartite
\(8+8\) graph. The reduced 16-vertex edge profile is

~~~text
59:1, 60:5, 61:4, 62:3, 63:1.
~~~

This links the new frontier to the near-\(K_{8,8}\) structures already
used in the degree-nine branch. The core catalog receipts are

~~~text
core_catalog_sha256=707a0cdf6eb73ff43902ce86bf36d491050363506534d74a2cad02737f1a5829
core_classification_sha256=4a7c7abe0a5c6eea65d98792d33d3d122511964b568d9cf70e168fbb4743ac45
~~~

A direct finite encoding would have to impose exact row sizes, core-edge
cover conditions, forbidden target \(K_9\) sets, and inherited local
full-color caps. The companion exclusion theorem makes that larger encoding
unnecessary: one shell edge, its core-cover condition, and two order-eleven
caps already contradict every catalogued core.

## 4. Replay

Run

~~~sh
python3 research/erdos-617-r6/r9_p93_order26_d8_shell_classifier.py \
  --geng /private/tmp/nauty289-build/geng

python3 research/erdos-617-r6/r9_p93_order26_d8_core_catalog.py \
  --geng /private/tmp/nauty289-build/geng
~~~

The graph catalog and all finite classifications are hash-pinned. Catalog
completeness depends on nauty geng; the slack enumeration is implemented
directly in Python.
