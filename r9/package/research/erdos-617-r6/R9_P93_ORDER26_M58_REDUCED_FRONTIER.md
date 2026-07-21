# Fixed \(r=9\), order \(26\), degree-nine level \(m=58\)

> **SUPERSEDED DOWNSTREAM STATUS.** The scoped \(m=58\) theorem below
> remains valid. Its statements about later open branches reflect the date
> of this checkpoint. Fixed \(r=9\) is now locally proved; see
> output/ERDOS_617_R9_RELEASE_HANDOFF.md.

## Status

The core level \(m=58\) in the order-26 degree-nine branch is locally
proved impossible.  The proof combines a uniform core lemma, 1,858 exact
rational duals, a solver-free exhaustive check of 5,056 row-size states,
and a short target-\(K_9\) contradiction for the 75 surviving states.

This result does not exclude the degree-eight branch or the degree-nine
levels \(m=59,\ldots,64\).  It does not prove \(P_3(26)\ge121\), fixed
\(r=9\), or Erdős Problem 617.

## 1. Setup

Let \(H\) be a target-color graph on 26 vertices inherited from a
hypothetical balanced nine-coloring.  Suppose

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

\[
 B=V(H)\setminus(A\cup\{v\}).
\]

Thus \(|A|=9\) and \(|B|=16\).  Define

\[
 F=\overline{H[A]},
 \qquad
 L=\overline{H[B]},
 \qquad
 f=e(F),
 \qquad
 m=e(L)=58.
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 x_{ab}=\mathbf 1_{b\in D_a},
 \qquad
 c=\sum_{a\in A}|D_a|.
\]

The inherited conditions used below are:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. Every induced subgraph \(L[Z]\) with \(|Z|\ge10\) has at least
   \(8p_9(|Z|)\) edges, where
   \[
   p_9(9q+s)=(9-s)\binom q2+s\binom{q+1}2.
   \]
3. \(F\) is \(K_4\)-free, \(\alpha(F)\le7\), and \(f\ge8\).
4. The global target-edge ledger gives
   \[
   c\le f+m-45=f+13. \tag{1}
   \]
5. Minimum degree in \(H\) gives
   \[
   |D_a|\ge d_F(a), \tag{2}
   \]
   and
   \[
   \sum_{a\in A}x_{ab}\ge d_L(b)-6. \tag{3}
   \]
6. If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) is a vertex cover of
   \(L\).  Equivalently, for every \(bb'\in E(L)\),
   \[
   x_{ab}+x_{ab'}+x_{a'b}+x_{a'b'}\ge1. \tag{4}
   \]
7. If \(T\) is a triangle of \(F\), then for every \(b\in B\),
   \[
   \sum_{a\in T}x_{ab}\ge1. \tag{5}
   \]

Condition (5) follows because a missed triangle together with \(b\)
would be an independent four-set in \(H\).

## 2. Uniform structure of the 16-vertex core

### Lemma 2.1

The graph \(L\) is bipartite with two sides of order eight.  It is
\(K_{8,8}\) with exactly six cross-edges removed.  Its only independent
eight-sets, and therefore its only minimum vertex covers, are its two
bipartition classes.

### Proof

Suppose \(L\) is nonbipartite, and take a shortest odd cycle \(C\) of
length \(\ell\ge5\).  The cycle is chordless.  Every vertex outside
\(C\) has at most two neighbors on \(C\).  Indeed, three such neighbors
split \(C\) into three paths.  Triangle-freeness makes each path have
length at least two, and one path has odd length.  That path together
with the outside vertex gives a shorter odd cycle.

The graph induced outside \(C\) is triangle-free, so Mantel's theorem
gives

\[
 e(L)
 \le
 \ell+2(16-\ell)
 +\left\lfloor\frac{(16-\ell)^2}{4}\right\rfloor.
\]

For odd \(\ell\ge5\), the right side is at most 57, with equality only
at \(\ell=5\).  This contradicts \(e(L)=58\).  Thus \(L\) is
bipartite.

Each bipartition class is independent.  Since \(\alpha(L)\le8\), both
classes have order eight.  Hence \(L\) is obtained from \(K_{8,8}\) by
removing \(64-58=6\) edges.

If an independent eight-set used \(p\) vertices from one side and
\(8-p\) from the other, where \(1\le p\le7\), all \(p(8-p)\) cross
pairs would have to be among the six removed edges.  But

\[
 p(8-p)\ge7.
\]

Therefore only the two sides are independent eight-sets.  Their
complements are the two minimum vertex covers. \(\square\)

## 3. Exact core and shell catalogs

The semantic verifier independently generates every unlabelled
triangle-free 16-vertex graph with 58 edges and checks all inherited
core conditions.  Exactly 50 core types remain.

For a shell \(F\), write

\[
 |D_a|=d_F(a)+\epsilon_a,
 \qquad \epsilon_a\ge0.
\]

Summing (2), using \(\sum_a d_F(a)=2f\), and applying (1) gives

\[
 f+\sum_a\epsilon_a\le13. \tag{6}
\]

Since every vertex cover of \(L\) has order at least eight, each edge
\(aa'\in E(F)\) also gives

\[
 d_F(a)+d_F(a')+\epsilon_a+\epsilon_{a'}\ge8. \tag{7}
\]

The verifier generates every unlabelled \(K_4\)-free graph \(F\) on
nine vertices with \(\alpha(F)\le7\), and checks (6) and (7) over all
nonnegative integer slack vectors.  Exactly 55 shell types remain.
Thus there are exactly

\[
 50\cdot55=2750
\]

core-shell pairs at level \(m=58\).

## 4. The 1,858 rational-dual exclusions

Consider the nonnegative real relaxation consisting of (2), (3), (4),
and (5).  Its objective is

\[
 \min\sum_{a\in A,b\in B}x_{ab}. \tag{8}
\]

For 1,858 of the 2,750 pairs, the certificate file supplies a
nonnegative rational weight for selected inequalities such that:

1. the total coefficient of every variable \(x_{ab}\) is at most one;
2. the weighted sum of the right sides is strictly greater than \(f+13\).

Summing those inequalities proves

\[
 \sum_{a,b}x_{ab}>f+13,
\]

contrary to (1).  The proof-facing verifier reconstructs every catalog
entry and every weighted inequality, reduces all fractions exactly, and
checks all 1,858 strict comparisons.  It does not call an LP or SAT
solver.  Floating-point optimization is used only by the separate
generator to discover candidate weights.

The exact receipt is:

~~~text
cores=50 shells=55 pairs=2750
strict_duals_verified=1858 uncertified_pairs=892
dual_semantic_sha256=f6d87a372bcea968bfa048746cadbb653a40a9b8512256d044d9906fd85828ce
status=PASS
~~~

The q-state verifier repeats this semantic dual check before it constructs
the 892-pair remainder.  Its digest serializes, for every certified pair,
the exact rational margin and the size of the dual support.  Thus the
remainder cannot be changed by replacing a valid pair name with unchecked
weights.

## 5. Solver-free exhaustion of the remaining 892 pairs

For every remaining pair, put

\[
 q_a=|D_a|=d_F(a)+\epsilon_a.
\]

The verifier enumerates every integer vector \(q\) satisfying (6) and
(7).  Pair-weighted over the 892 pairs, there are exactly 5,056 such
states.

Every shell occurring in this remainder has a two-vertex edge cover
\(\{h,g\}\).  After fixing the two hub rows \(D_h,D_g\), the other
seven shell vertices are independent in \(F\).  For each such vertex
\(u\), the verifier enumerates every \(q_u\)-subset \(D_u\subseteq B\)
that satisfies the cover condition with each incident hub.  If
\(hgu\) is a shell triangle, it also imposes

\[
 D_h\cup D_g\cup D_u=B. \tag{9}
\]

Finally, an exact memoized dynamic program checks the sixteen column
demands (3).  This is an exhaustive finite set search.  It does not call
an LP or SAT solver.

There are no omitted interactions between the seven low rows.  The chosen
hubs meet every shell edge, so those seven vertices are independent in
\(F\).  After the two hub rows are fixed, each low-row domain contains
exactly the subsets satisfying all of its incident cover conditions and,
when applicable, its unique hub-hub-low triangle condition.  The only
remaining joint constraints are the sixteen lower column demands.  The
dynamic program recursively tries every member of every nonempty domain,
memoizes only failed residual-demand states, and stops early only after all
column demands have already been met; arbitrary choices from the remaining
nonempty domains then complete the rows.

The full accounting is:

~~~text
remaining_pairs=892
strict_duals_semantically_verified=1858 uncertified_pairs=892
dual_semantic_sha256=f6d87a372bcea968bfa048746cadbb653a40a9b8512256d044d9906fd85828ce
q_states=5056 cover_UNSAT=4981 cover_SAT=75
cover_UNSAT_pairs=849 cover_SAT_pairs=43
boundary_q_states=274 boundary_cover_UNSAT=199 boundary_cover_SAT=75
forcing_triangle_cover_SAT=75
hub_pairs_examined=56537597
demand_states_examined=5310986
status=PASS
~~~

The line involving 274 states applies only to the 43-pair boundary.  It
does not replace the 892-pair exhaustion.  The exact decomposition is

\[
 892=849+43,
\]

followed, only inside the 43 pairs, by

\[
 274=199+75.
\]

## 6. Human exclusion of the final 75 states

Every one of the 75 feasible row-size states has a triangle \(\{h,g,u\}\) in
\(F\) such that

\[
 q_h=8,
 \qquad
 q_g+q_u=8. \tag{10}
\]

Since \(gu\in E(F)\), the set \(D_g\cup D_u\) is a vertex cover of
\(L\).  Its order is at most eight by (10), while \(\tau(L)=8\).
Therefore it is an eight-vertex minimum cover.  Lemma 2.1 shows that

\[
 D_g\cup D_u=C
\]

for one bipartition class \(C\) of \(L\).

The triangle condition (5) gives

\[
 D_h\cup D_g\cup D_u=B.
\]

Thus \(B\setminus C\subseteq D_h\).  Both sets have order eight by
(10), so

\[
 D_h=B\setminus C. \tag{11}
\]

The set \(B\setminus C\) is independent in \(L\), hence it is a clique
of order eight in \(H[B]\).  Equation (11) says that \(h\) is joined in
\(H\) to every vertex of that clique.  Consequently

\[
 \{h\}\cup(B\setminus C)
\]

is a target \(K_9\), contrary to \(\omega(H)\le8\).  This excludes all
75 final states and completes the \(m=58\) proof.

## 7. Verification

Run:

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_order26_m58_duals.py \
  --geng /private/tmp/nauty289-build/geng \
  --certificates \
    research/erdos-617-r6/r9_p93_order26_m58_duals.jsonl

python3 research/erdos-617-r6/verify_r9_p93_order26_m58_qstates.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m58_duals.jsonl \
  --workers 10

python3 research/erdos-617-r6/audit_r9_p93_order26_m58_qstates_z3.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m58_duals.jsonl \
  --workers 10
~~~

The retained local replay used Python 3.13.13, NetworkX 3.4.2, and Z3
4.16.0.  The `geng` executable had SHA-256

~~~text
3ca950af2145c546f9f586cf960eaf98f88fc3920564338f8306b6f58d018af5
~~~

These versions identify the checked run.  The mathematical search does not
depend on Z3, and an equivalent complete `geng` catalog can be checked by the
same production verifier.

The production verifier and the independent Z3 audit classify every one
of the 5,056 row-size states identically.  Both serialize the sorted
triples

\[
 (\mathit{pair\_index},\mathit{row\_sizes},\mathit{satisfiable})
\]

and obtain the SHA-256 fingerprint

~~~text
0dff9f3a707e730c3a31e880de7ce32a38404e7b7a92ba4355ec7c97a04d6938
~~~

The Z3 run is an independent semantic audit of the state classification,
not a proof certificate.  The proof itself is the solver-free exhaustive
finite search described in Section 5, together with the exact rational
duals and the argument in Section 6.

The generator for the rational candidates is:

~~~sh
python3 research/erdos-617-r6/r9_p93_order26_m58_dual_generator.py \
  --geng /private/tmp/nauty289-build/geng \
  --output research/erdos-617-r6/r9_p93_order26_m58_duals.jsonl
~~~

The proof depends on the completeness of the nauty `geng` unlabelled
graph catalogs.  It does not depend on exploratory SAT output, an
unchecked UNSAT claim, floating-point feasibility, DRAT, or LRAT.

## 8. Exact nonclaims

1. The order-26 degree-eight family is not excluded here.
2. The order-26 degree-nine levels \(m=59,\ldots,64\) are not excluded.
3. This theorem does not prove \(P_3(26)\ge121\).
4. This theorem does not prove fixed \(r=9\).
5. This theorem does not prove Erdős Problem 617.
