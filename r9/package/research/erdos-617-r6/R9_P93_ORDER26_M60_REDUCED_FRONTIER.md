# Fixed \(r=9\), order \(26\), degree-nine level \(m=60\)

## Status

The core level \(m=60\) in the order-26 degree-nine branch is locally
proved impossible. The proof combines 1,290 exact rational duals, a
solver-free exhaustion of 23,157 row-size states for 220 pairs, and a
direct argument for ten copies of one exceptional shell.

This result does not exclude the degree-eight branch or the degree-nine
levels \(m=61,\ldots,64\). It does not prove \(P_3(26)\ge121\), fixed
\(r=9\), or Erdős Problem 617.

## 1. Setup

Let \(H\) be a target-color graph on 26 vertices from a hypothetical
balanced nine-coloring, with

\[
 \alpha(H)\le3,\qquad
 \omega(H)\le8,\qquad
 e(H)\le120,\qquad
 \delta(H)=9.
\]

Fix a degree-nine vertex \(v\), put \(A=N_H(v)\), and put
\(B=V(H)\setminus(A\cup\{v\})\). Thus \(|A|=9\) and \(|B|=16\). Define

\[
 F=\overline{H[A]},\qquad
 L=\overline{H[B]},\qquad
 f=e(F),\qquad
 m=e(L)=60.
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 x_{ab}=\mathbf 1_{b\in D_a}.
\]

The inherited conditions used below are:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. The inherited core-density inequalities hold on every subset of \(B\).
3. \(F\) is \(K_4\)-free and \(\alpha(F)\le7\).
4. The target-edge ledger gives
   \[
   \sum_{a\in A}|D_a|\le f+15. \tag{1}
   \]
5. Minimum degree gives
   \[
   |D_a|\ge d_F(a), \tag{2}
   \]
   and
   \[
   \sum_{a\in A}x_{ab}\ge d_L(b)-6. \tag{3}
   \]
6. If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) is a vertex cover of
   \(L\). Equivalently, for every \(bb'\in E(L)\),
   \[
   x_{ab}+x_{ab'}+x_{a'b}+x_{a'b'}\ge1. \tag{4}
   \]
7. If \(T\) is a triangle of \(F\), then
   \[
   \sum_{a\in T}x_{ab}\ge1
   \qquad\text{for every }b\in B. \tag{5}
   \]

## 2. Core structure and the \(p=1\) condition

The uniform core lemma gives

\[
 L=K_{8,8}-Q,\qquad |Q|=4,
\]

with bipartition sides \(X,Y\), both of order eight. The only independent
eight-sets of \(L\) are \(X\) and \(Y\).

For every \(a\in A\),

\[
 X\nsubseteq D_a
 \qquad\text{and}\qquad
 Y\nsubseteq D_a. \tag{6}
\]

Indeed, each side is an eight-vertex clique in \(H[B]\). If one side were
contained in \(D_a\), that side together with \(a\) would be a target
\(K_9\), contrary to \(\omega(H)\le8\). This is the \(p=1\) side cap.

## 3. Exact catalogs and rational duals

The semantic verifier rebuilds every unlabelled core and shell satisfying
the inherited conditions. It obtains:

\[
 10\text{ cores},\qquad
 152\text{ shells},\qquad
 1520\text{ core-shell pairs}.
\]

Writing

\[
 |D_a|=d_F(a)+\epsilon_a,\qquad \epsilon_a\ge0,
\]

conditions (1) and (2) give

\[
 f+\sum_a\epsilon_a\le15. \tag{7}
\]

For 1,290 pairs, the certificate file gives nonnegative rational weights
on selected inequalities (2) through (5). In each certificate, every
variable has total coefficient at most one and the weighted right side is
strictly greater than \(f+15\). This contradicts (1).

The proof-facing verifier reconstructs every catalog entry and inequality,
checks every rational coefficient exactly, and pins the certificate data,
semantic result, and 230-pair complement:

~~~text
strict_duals_verified=1290 uncertified_pairs=230
semantic_sha256=b2d58b705277226d36ebc951d886e869e70fa7cf52669edc8d25d8b1041ccf3c
uncertified_pair_sha256=f54b16c3087a849b7084193ce522a45e2f90ae6e24be168a968e83cfbeb6f5e7
data_sha256=9470c5b7ea9b0951f99dccdf6ff03dccd420b1620de4dedb5ad9dc8252ea4953
~~~

## 4. Solver-free exhaustion of 220 pairs

Of the 230 remaining pairs, 220 have a shell with a two-vertex edge cover
\(\{h,g\}\). Put \(q_a=|D_a|\). The verifier enumerates every integer row
vector allowed by (7) and the row-pair cover lower bounds. Pair-weighted,
there are exactly 23,157 states.

After \(D_h,D_g\) are fixed, the other seven shell vertices are independent
in \(F\). Each low row is assigned its exact finite domain of \(q_a\)-sets
that obey:

1. the two side caps (6);
2. every incident row-pair cover condition (4);
3. every completed hub-hub-low triangle condition (5).

An exact memoized dynamic program tries every domain choice needed to meet
the sixteen column demands (3). The chosen hubs meet every shell edge, so
there are no omitted low-low cover conditions. Every shell triangle is
hub-hub-low, so there are no omitted triangle conditions.

The pair-granular receipt is:

~~~text
two_hub_remainder_pairs=220
q_states=23157 p1_UNSAT=23157 p1_SAT=0
hub_pairs_examined=953822464
demand_states_examined=146962422
classification_sha256=1454b3bb20347bad1cf4e064c0414151c863caa7b4695c168f8f34cc3548fa21
status=PASS
~~~

## 5. The exceptional shell

The other ten pairs all use shell graph6 H??Fvrw. This shell is
\(K_{5,3}\) plus one isolated vertex. It has \(f=15\), so (7) leaves no
slack. The five vertices on one side have row size three, the three on the
other side have row size five, and the isolated row has size zero.

For every shell edge \(ab\), the set \(D_a\cup D_b\) covers \(L\) and has
order at most \(3+5=8\). Since \(\tau(L)=8\), it is a minimum cover and
must equal \(X\) or \(Y\). Label the edge by that side.

Two incident edges must receive the same label. Otherwise their common
row, which has positive size, would be contained in
\(X\cap Y=\varnothing\). The line graph of \(K_{5,3}\) is connected, so
all fifteen edges have one label, say \(X\). Every nonisolated row is then
contained in \(X\), while the isolated row is empty. Hence every vertex of
\(Y\) has zero shell-to-core incidence.

This contradicts (3). More quantitatively, the four deleted core edges
have total deleted degree four on each side, so

\[
 \sum_{b\in Y}\max(0,d_L(b)-6)
 \ge 16-4=12.
\]

The exceptional-shell checker verifies the graph structure, unique row
state, connected line graph, unique minimum covers, deleted-degree sums,
and positive side-demand profiles. The propagation paragraph above is the
human mathematical implication from those checked premises.

## 6. Independent Z3 audit

A separate self-contained Z3 program rebuilds the Boolean incidence model
without importing the dynamic program. It imposes exact row sizes,
row-pair covers, triangle columns, column demands, and both \(p=1\) side
caps. It classifies all 23,157 states as UNSAT and obtains the same
classification SHA-256.

Z3 is a separate encoding and search audit. It is not the proof premise for
the UNSAT states.

## 7. Replay

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_order26_m60_duals.py \
  --geng /private/tmp/nauty289-build/geng \
  --certificates research/erdos-617-r6/r9_p93_order26_m60_duals.jsonl

python3 research/erdos-617-r6/r9_p93_order26_m60_p1_qstate_verifier.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m60_duals.jsonl \
  --workers 10

python3 research/erdos-617-r6/r9_p93_order26_m60_p1_qstate_z3_audit.py \
  --geng /private/tmp/nauty289-build/geng \
  --duals research/erdos-617-r6/r9_p93_order26_m60_duals.jsonl \
  --workers 10
~~~

## 8. Exact nonclaims

1. This theorem excludes only the order-26, degree-nine core level \(m=60\).
2. It does not exclude \(m=61,\ldots,64\) or the degree-eight branch.
3. It does not prove \(P_3(26)\ge121\), fixed \(r=9\), or Erdős Problem 617.
4. It is a local computer-assisted result pending external review.
