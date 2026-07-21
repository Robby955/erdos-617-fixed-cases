# Fixed \(r=9\), common 17-core two-row exclusion

> **SUPERSEDED DOWNSTREAM STATUS.** This scoped theorem is a dependency
> of the locally proved fixed-\(r=9\) theorem. See
> output/ERDOS_617_R9_RELEASE_HANDOFF.md for the complete chain.

## Verdict and scope

PROVED, conditional only on the separately checked 17-vertex core catalogue.
The argument excludes both of the following families:

- the order-26, minimum-degree-eight branch under \(e(H)\le120\);
- the order-27, minimum-degree-nine branch under \(e(H)\le135\).

No shell classification is needed.

Together with the banked order-26 degree-nine levels \(m=56,\ldots,64\),
this closes the order-26 analysis under the edge cap \(e(H)\le120\). The
separately banked degree-ten package closes order 27. This scoped theorem
does not by itself prove fixed \(r=9\); the complete downstream implication
chain is recorded in output/ERDOS_617_R9_RELEASE_HANDOFF.md.

## 1. Setup

Let \(H\) be a target-color graph in either of the two branches above.
Thus \((|V(H)|,\delta(H))\) is \((26,8)\) or \((27,9)\), and

\[
 \alpha(H)\le3,\qquad \omega(H)\le8.
\]

Choose a minimum-degree vertex \(v\). Put \(A=N_H(v)\) and
\(B=V(H)\setminus(A\cup\{v\})\). In both branches \(|B|=17\). Write

\[
 F=\overline{H[A]},\qquad L=\overline{H[B]}.
\]

The graph \(F\) is nonempty. In the order-26 branch, an empty \(F\) would
make \(\{v\}\cup A\) a target \(K_9\). In the order-27 branch, it would
make \(A\) contain a target \(K_9\). Choose any edge \(cu\in E(F)\). For
\(a\in A\), put

\[
 D_a=N_H(a)\cap B.
\]

The core catalogue proves that \(e(L)\in\{64,65\}\), and that there is a
vertex \(z\in B\) such that \(L-z\) is bipartite with parts \(X,Y\) of
order eight and

\[
 d_L(z)\le5.
\tag{1}
\]

Set

\[
 p=|N_L(z)\cap X|,\qquad q=|N_L(z)\cap Y|,
 \qquad d=p+q.
\]

Since \(L\) is triangle-free, both \(X\) and \(Y\) are independent.
The bound \(\alpha(L)\le8\) gives \(p,q\ge1\): if, for example, \(p=0\),
then \(X\cup\{z\}\) is an independent nine-set.

Let \(h\) be the number of missing edges between \(X\) and \(Y\). Then

\[
 h=64-e(L-z)=64-e(L)+d\le d.
\tag{2}
\]

Triangle-freeness also says that every pair in
\((N_L(z)\cap X)\times(N_L(z)\cap Y)\) is missing. Thus at least \(pq\) of
the \(h\) missing cross-pairs form this rectangle.

## 2. The two full-color caps

Put \(S=D_c\cup D_u\). The set \(S\) is a vertex cover of \(L\). Indeed,
if \(bb'\in E(L)\) had both endpoints outside \(S\), then all six pairs
among \(c,u,b,b'\) would be nonedges of \(H\), contrary to
\(\alpha(H)\le3\).

The inherited full-color inequality on eleven vertices is

\[
 e_H(W)\le D_9(11)=39.
\tag{3}
\]

Apply (3) to \(\{c,u\}\cup X\cup\{z\}\). The pair \(cu\) is a nonedge of
\(H\), while \(H[X\cup\{z\}]\) has \(36-p\) edges. Hence

\[
 \sum_{a\in\{c,u\}}|D_a\cap(X\cup\{z\})|\le p+3.
\tag{4}
\]

The analogous set using \(Y\) gives

\[
 \sum_{a\in\{c,u\}}|D_a\cap(Y\cup\{z\})|\le q+3.
\tag{5}
\]

Only (1), (2), the vertex-cover property, and (4)-(5) are needed below.
The remaining shell rows, their exact sizes, and the larger finite formulas
play no role.

## 3. Abstract exclusion

Write

\[
 a=|S\cap X|,\qquad b=|S\cap Y|,
 \qquad s=\mathbf 1_{z\in S}.
\]

Equations (4)-(5) imply

\[
 a+s\le p+3,qquad b+s\le q+3.
\tag{6}
\]

Let \(T=B\setminus S\). Since \(S\) is a vertex cover, \(T\) is
independent in \(L\).

First suppose \(s=1\). Then

\[
 |T\cap X|=8-a\ge6-p,qquad
 |T\cap Y|=8-b\ge6-q.
\]

Every cross-pair between these two sets must be one of the \(h\) missing
edges. Therefore

\[
 h\ge(6-p)(6-q).
\tag{7}
\]

But \(p,q\ge1\) and \(p+q=d\le5\), so

\[
 (6-p)(6-q)-d
 =36-7d+pq
 \ge35-6d>0.
\]

This contradicts (2).

Now suppose \(s=0\), so \(z\in T\). Independence of \(T\) gives

\[
 T\cap X\subseteq X\setminus N_L(z),qquad
 T\cap Y\subseteq Y\setminus N_L(z).
\]

Equation (6) gives

\[
 |T\cap X|\ge5-p,qquad |T\cap Y|\ge5-q.
\]

The missing cross-pairs between these two sets are disjoint from the
\(pq\) missing pairs in the neighborhood rectangle. Hence

\[
 h\ge pq+(5-p)(5-q).
\tag{8}
\]

Since \(p,q\ge1\) and \(d\le5\), we have \(pq\ge d-1\), and therefore

\[
 pq+(5-p)(5-q)-d
 =25-6d+2pq
 \ge23-4d>0.
\]

Again this contradicts (2). Both choices of \(s\) are impossible.

## 4. Consequence

Every eligible shell in either branch has an edge \(cu\), and every
classified core has a witness \((z,X,Y)\) satisfying (1). The preceding
argument excludes all fourteen cores for every possible shell. No SAT or
LRAT payload is needed. The only finite dependency is the fourteen-core
catalogue.

## 5. Replay

Run

~~~sh
python3 research/erdos-617-r6/r9_p93_order26_d8_core_catalog.py \
  --geng /private/tmp/nauty289-build/geng

python3 research/erdos-617-r6/verify_r9_p93_order26_d8_two_row.py \
  --geng /private/tmp/nauty289-build/geng
~~~

The last command reconstructs the core catalogue independently, checks a
valid \((z,X,Y)\) witness for every core, checks the neighborhood rectangle,
replays both arithmetic contradictions, and exhausts 2,228,224 possible
cover masks across the accepted witnesses.
