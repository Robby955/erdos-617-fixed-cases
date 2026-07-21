# Dependency audit for the fixed \(r=9\) common 17-core theorem

> **SUPERSEDED DOWNSTREAM STATUS.** This scoped audit is a dependency of
> the locally proved fixed-\(r=9\) theorem. See
> output/ERDOS_617_R9_RELEASE_HANDOFF.md for the complete chain.

## Verdict

PASS LOCALLY. The exclusion uses one finite core catalogue and one human
counting lemma. It closes the order-26 degree-eight branch and the order-27
degree-nine branch. The shell catalogue and the larger 98-system SAT search
are redundant. This scoped audit is not, by itself, the complete fixed-
\(r=9\) proof.

## 1. Input from a hypothetical coloring

The relevant terminal reductions supply a target-color graph \(H\) with

\[
 \alpha(H)\le3,\quad \omega(H)\le8,\quad
 (|V(H)|,\delta(H))\in\{(26,8),(27,9)\},
\]

and the inherited subset cap

\[
 e_H(W)\le D_9(|W|)
\]

for every induced set \(W\). At order eleven this is

\[
 D_9(11)=\binom{11}{2}-8P_9(11)=55-16=39.
\]

The proof uses the cap only on two named eleven-sets.

## 2. Shell input

Choose a minimum-degree vertex \(v\), set \(A=N_H(v)\), and let
\(F=\overline{H[A]}\). The proof needs only one edge \(cu\in E(F)\).

If \(|A|=8\), then \(F=\varnothing\) would make \(\{v\}\cup A\) a target
\(K_9\). If \(|A|=9\), it would make \(A\) a target \(K_9\). Hence the
edge \(cu\) exists in both branches without finite shell enumeration.

## 3. Core dependency

Let \(B=V(H)\setminus(A\cup\{v\})\) and
\(L=\overline{H[B]}\). Both branches have \(|B|=17\) and the same core
conditions. The core classifier starts from all 36 unlabelled
triangle-free graphs on 17 vertices at levels 64 and 65. The inherited
independence and subset-density checks retain 14 graphs.

For every retained core, the semantic verifier finds a vertex \(z\) such
that \(L-z\) has bipartition \(X,Y\), with \(|X|=|Y|=8\), and
\(d_L(z)\le5\). It also checks both neighborhood sides are nonempty, the
triangle-free missing rectangle, and the exact cross-edge ledger.

Receipts:

~~~text
core_catalog_sha256=707a0cdf6eb73ff43902ce86bf36d491050363506534d74a2cad02737f1a5829
two_row_witness_sha256=7b0d00a101125f19cb722f1c07d17ff547b7bc42eafc466bc39fe6b6854a26ac
two_row_arithmetic_sha256=e14703c21b0e040c986831e3dacc74c3ff0a0588dd02ae47540454457afb1ae0
~~~

## 4. Human implication chain

For \(a\in A\), let \(D_a=N_H(a)\cap B\), and put
\(S=D_c\cup D_u\).

1. If an edge of \(L\) avoids \(S\), its endpoints together with \(c,u\)
   form an independent four-set in \(H\). Thus \(S\) covers \(L\).

2. Write \(p=|N_L(z)\cap X|\) and \(q=|N_L(z)\cap Y|\). Since
   \(\alpha(L)\le8\), both are positive. Put \(d=p+q\le5\).

3. If \(h\) is the number of missing \(X\)-\(Y\) edges, then
   \(h=64-e(L)+d\le d\).

4. The order-eleven cap on \(\{c,u\}\cup X\cup\{z\}\) gives total
   incidence at most \(p+3\). The analogous \(Y\)-set gives at most
   \(q+3\).

5. If \(z\in S\), the independent complement \(B\setminus S\) contains
   at least \(6-p\) vertices of \(X\) and \(6-q\) vertices of \(Y\).
   This forces more than \(h\) missing cross-edges.

6. If \(z\notin S\), the independent complement avoids both parts of
   \(N_L(z)\). Its forced missing rectangle is disjoint from the
   \(pq\)-edge neighborhood rectangle, again forcing more than \(h\)
   missing cross-edges.

The exact positive gaps at the worst value \(h=d\) are replayed for all ten
ordered pairs \((p,q)\) with \(p,q\ge1\) and \(p+q\le5\).
As a separate semantic check, the verifier examines every one of the
\(2^{17}\) candidate cover masks for each of the 17 accepted core witnesses.
All 2,228,224 masks are rejected by the vertex-cover and two-cap conditions.

## 5. Boundary and corruption checks

The abstract lemma is intentionally limited to \(d\le5\). At \(d=6\),
the pair \((p,q)=(1,5)\) no longer gives either counting contradiction.
The verifier rejects this boundary, a zero neighborhood side, and a
corrupted value \(h>d\). It runs 13 arithmetic and corruption checks in
total.

An exploratory fixed-system sweep independently returned UNSAT on all 98
core-shell pairs. Its 98 `cuts.json` files have aggregate checksum

~~~text
518717e36635fe8f647247b5301b654eab5c11638b8edceaed005f1a2661ed4d
~~~

This sweep is corroborating evidence only. The theorem does not import its
formulas, models, or solver result.

## 6. Exact conclusion and nonclaims

The theorem excludes every order-26, minimum-degree-eight graph under
\(e(H)\le120\), and every order-27, minimum-degree-nine graph under
\(e(H)\le135\). The separately audited \(m=64\) package is banked. The
order-26 degree-nine branch and this theorem together prove the complete
order-26 lower bound \(P_3(26)\ge121\). Downstream packages close the
order-27 degree-ten branch and the outer implication.

Still open universally: the synchronization and normalized-descent entry
theorem for Erdős Problem 617.
