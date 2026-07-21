# The fixed \(r=9\) degree-eight neighborhood-defect wall

## Historical status

**SUPERSEDED AS A FIXED-\(r=9\) STATUS NOTE.** The current dependency graph
is output/ERDOS_617_R9_RELEASE_HANDOFF.md.

This wall remains a correct limitation of the neighborhood-defect charge by
itself. The fixed row is now closed by `R9_D8_FULL_COLOR_BRIDGE.md`, which
uses the empty order-27 terminal and the full-color 11-set cap at order 37.

## Verdict and original scope

PROVED REFINEMENT; OUTER BRIDGE OPEN. Missing edges in the neighborhood
of the degree-eight outer vertex give an additional exact edge charge.
The charge closes every cell with neighborhood defect \(q\ge j+2\), but
leaves exactly twenty pairs

\[
 (j,q),\qquad 0\le j\le4,\qquad 0\le q\le j+1.
\tag{1}
\]

Explicit partial-coloring witnesses show that the target \(K_9\) at
\(q=0\), the relevant local ten-set conditions, the peeled target
blocks, and the minimum-degree cross-incidence bound can coexist in all
twenty cells.

The witnesses are not complete outer graphs or complete colorings. They
do not satisfy or test the unresolved residual-core conditions. This note
does not prove fixed \(r=9\) or Erdős Problem 617.

## 1. Exact neighborhood-defect charge

The following lemma is stated for a general degree because the proof has
no special feature at degree eight.

**Lemma 1 (neighborhood-defect charge).** Let \(F\) be a graph, let \(v\)
be a minimum-degree vertex of degree \(d\), and put

\[
 N=N_F(v),\qquad
 U=V(F)\setminus(N\cup\{v\}).
\tag{2}
\]

Define

\[
 q=\binom d2-e_F(N),\qquad
 X=e_F(N,U).
\tag{3}
\]

Then

\[
 \boxed{X\ge2q.}
\tag{4}
\]

If \(e(F)\le M\), and \(R_j\) is obtained from \(U\) after deleting
\(j\) disjoint copies of \(K_r\), then

\[
 e_F(R_j)
 \le
 M-d-\binom d2-j\binom r2-(X-q).
\tag{5}
\]

In particular,

\[
 e_F(R_j)
 \le
 M-d-\binom d2-j\binom r2-q.
\tag{6}
\]

**Proof.** Every vertex of \(N\) has degree at least \(d\). Summing its
degree contributions from \(v\), \(N\), and \(U\) gives

\[
 d+2e_F(N)+X\ge d^2.
\tag{7}
\]

Since \(e_F(N)=\binom d2-q\), equation (7) is exactly \(X\ge2q\).

Deleting \(v\cup N\) removes

\[
 d+e_F(N)+X
 =d+\binom d2+(X-q)
\tag{8}
\]

edges before any edges incident with the peeled blocks are counted.
Each peeled \(K_r\) removes at least its \(\binom r2\) internal edges.
This proves (5), and (4) gives (6). \(\square\)

The exact improvement over the canonical charge is \(X-q\), not merely
\(q\). The weaker \(q\)-improvement is the best consequence of minimum
degree alone.

## 2. The five fixed-\(r=9\) cells

For fixed \(r=9\), the least-color edge budget is

\[
 M_9=369.
\tag{9}
\]

In the outer row \(d=8\), after \(j\) peeled target copies of \(K_9\),
the residual parameters and canonical upper bound are

\[
 a=8-j,\qquad
 m=73-9j,\qquad
 E_j=333-36j.
\tag{10}
\]

The existing order-26 recursion gives

\[
\begin{array}{c|ccccc}
j&0&1&2&3&4\\ \hline
B_9(a,m)&332&295&258&221&184\\
E_j&333&297&261&225&189\\
B_9(a,m)-E_j&-1&-2&-3&-4&-5.
\end{array}
\tag{11}
\]

Lemma 1 changes the exact margin to

\[
 B_9(a,m)-\bigl(E_j-(X-q)\bigr)
 =X-q-j-1.
\tag{12}
\]

Using only \(X\ge2q\), the certified margin is at least

\[
 q-j-1.
\tag{13}
\]

Thus every \(q\ge j+2\) cell is strict. The survivors are:

\[
\begin{array}{c|c|c|c|c}
j&(a,m)&B_9(a,m)&E_j&\text{surviving }q\\ \hline
0&(8,73)&332&333&0,1\\
1&(7,64)&295&297&0,1,2\\
2&(6,55)&258&261&0,1,2,3\\
3&(5,46)&221&225&0,1,2,3,4\\
4&(4,37)&184&189&0,1,2,3,4,5
\end{array}
\tag{14}
\]

Their number is

\[
 2+3+4+5+6=20.
\tag{15}
\]

Retaining \(X\) narrows them further. A nonstrict cell must satisfy

\[
 \boxed{2q\le X\le q+j+1.}
\tag{16}
\]

There are fifty-five integer triples \((j,q,X)\) satisfying (1) and
(16). The lower endpoint \(X=2q\) is realizable by all twenty shell
witnesses below.

## 3. Why the \(q=0\) clique does not add a packing step

When \(q=0\), the set

\[
 B=\{v\}\cup N
\tag{17}
\]

is a target \(K_9\). This does not count as another block in the
nonneighbor packing. The representative-selection argument already uses
\(v\), which is target-anticomplete to \(U\). Since \(B\) is a clique,
it cannot supply a second target-independent representative together
with \(v\).

After \(j\) blocks have been removed from \(U\), the residual order and
independence parameter therefore remain \(73-9j\) and \(8-j\). The
external clique \(B\) does not change either value in (10).

## 4. Scoped shell-relaxation witnesses

Fix one of the twenty pairs in (1). Take an eight-vertex set \(N\) and
delete \(q\) edges from its target clique. Call the missing-edge graph
\(M\). For every incidence of a vertex \(x\) with an edge of \(M\),
choose a distinct reservoir vertex \(w_{x,e}\) in the residual and add
the target edge \(xw_{x,e}\).

The smallest residual has order \(37\), while \(2q\le10\), so these
vertices can always be chosen outside the \(j\) peeled blocks. The
construction has

\[
 X=2q.
\tag{18}
\]

If \(d_M(x)\) is the missing degree of \(x\), then its target degree
among the displayed vertices is

\[
 1+(7-d_M(x))+d_M(x)=8.
\tag{19}
\]

The vertex \(v\) also has target degree eight. Thus the displayed degree
inequalities for \(v\) and the vertices of \(N\) are attained with
equality. No degree condition is imposed on the reservoir vertices.

The target graph on \(B=\{v\}\cup N\) has \(36-q\) edges. Every reservoir
vertex is incident with at most one displayed target edge into \(B\), and
the peeled blocks have none. Thus every displayed set \(B\cup\{u\}\)
has either

\[
 36-q\quad\hbox{or}\quad37-q
\tag{20}
\]

target edges, within the fixed-\(r=9\) ten-set cap \(37\).

The eight non-target colors can be assigned consistently on all displayed
ten-sets:

1. On a star from \(B\) to a reservoir vertex, color the eight non-target
   edges bijectively when one edge is target. If all nine edges are
   non-target, use every non-target color and repeat one.
2. Between \(B\) and a peeled target \(K_9\), label both sides by
   \(\mathbb Z/9\mathbb Z\). Color the edge with difference
   \(t\in\{1,\ldots,8\}\) by color \(t\), and give difference zero color
   one. Every row and every column sees all eight colors.
3. Use the same cyclic assignment between two peeled blocks. From a
   peeled block to any reservoir vertex, use all eight colors on the nine
   incident edges.
4. Give the \(q\) missing edges inside \(N\) arbitrary non-target colors.
   They can only add colors to a set \(B\cup\{u\}\).

Consequently every displayed set consisting of \(B\) and one outside
vertex sees all nine colors. Every displayed set consisting of one peeled
target \(K_9\) and one outside vertex also sees all nine colors. The target
edge count in each such set is at most \(37\).

These witnesses prove a limitation, not feasibility of the outer cells.
Edges within the reservoir are left unspecified, and the witnesses do
not impose the residual independence bound, residual clique bound,
recursive edge floor, or all ten-set conditions. They show only that the
the \(q=0\) neighborhood \(K_9\), the local block-plus-one conditions,
and the exact cross-incidence charge do not by themselves remove any of
the twenty surviving pairs.

## 5. Replay and nonclaims

Run

~~~sh
python3 research/erdos-617-r6/verify_r9_outer_d8_neighborhood_defect.py
~~~

The verifier checks the five margins, all twenty \((j,q)\) cells, all
fifty-five \((j,q,X)\) triples, and a concrete partial coloring for every
surviving cell. It audits the target degrees, exact defect, exact cross
charge, ten-set target caps, all-color row and column conditions, and two
deliberate corruptions.

This note does not close any residual core, prove the outer implication,
prove fixed \(r=9\), or solve Erdős Problem 617.
