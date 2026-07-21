# Fixed \(r=9\), order \(26\), degree-nine endpoint levels

## Status

The core levels \(m=56\) and \(m=57\) in the degree-nine branch are
locally proved impossible by a finite, solver-free argument.  The proof
uses exhaustive unlabelled graph generation, explicit integer dual
inequalities, a minimum-cover reduction, and direct semantic verification.

This result does not exclude the levels \(m=58,\ldots,64\).  It does not
prove \(P_3(26)\ge121\), fixed \(r=9\), or Erdős Problem 617.

## 1. Setup

Let \(H\) be one target-color class inherited from a hypothetical
balanced nine-coloring, restricted to an induced set of \(26\) vertices.
Suppose that

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
 m=e(L).
\]

For \(a\in A\), let

\[
 D_a=\{b\in B:ab\in E(H)\},
 \qquad
 c=\sum_{a\in A}|D_a|.
\]

For \(n=9q+a\), where \(0\le a<9\), define

\[
 p_9(n)=(9-a)\binom q2+a\binom{q+1}2,
 \qquad
 D_9(n)=\binom n2-8p_9(n).
\]

In particular, \(D_9(10)=37\) and \(D_9(11)=39\).  The inherited
constraints give:

1. \(L\) is triangle-free, \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
2. Every induced subgraph \(L[Z]\) with \(|Z|\ge10\) has at least
   \(8p_9(|Z|)\) edges.
3. \(F\) is \(K_4\)-free and \(\alpha(F)\le7\).
4. The full-color ten-set bound on \(\{v\}\cup A\) gives \(f\ge8\).
5. Minimum degree in \(H\) gives \(|D_a|\ge d_F(a)\).
6. The global target-edge ledger gives
   \[
     c\le f+m-45.
   \]
7. If \(aa'\in E(F)\), then \(D_a\cup D_{a'}\) is a vertex cover of
   \(L\).  Since \(\tau(L)\ge8\),
   \[
     |D_a|+|D_{a'}|\ge8.
   \]

Write

\[
 |D_a|=d_F(a)+\epsilon_a,
 \qquad \epsilon_a\ge0.
\]

As \(\sum_a d_F(a)=2f\), the global ledger becomes

\[
 f+\sum_a\epsilon_a\le m-45. \tag{1}
\]

For every edge \(aa'\in E(F)\), the cover inequality becomes

\[
 d_F(a)+d_F(a')+\epsilon_a+\epsilon_{a'}\ge8. \tag{2}
\]

## 2. Exact endpoint shell catalogs

At \(m=56\), (1) gives \(f\le11\).  At \(m=57\), it gives \(f\le12\).
The verifier generates every unlabelled \(K_4\)-free graph on nine vertices
with \(8\le f\le12\), rejects \(\alpha(F)\ge8\), and checks every
nonnegative slack vector allowed by (1) against (2).

There are \(11{,}088\) raw graphs.  Exactly two shell types remain at
\(m=56\), and exactly sixteen remain at \(m=57\).

## 3. Column-transversal duals

For \(b\in B\), put

\[
 S_b=\{a\in A:b\in D_a\}.
\]

Every \(S_b\) meets every triangle of \(F\), since a missed triangle
together with \(b\) would be an independent four-set in \(H\).  The
full-color bound \(D_9(11)=39\) on \(\{v\}\cup A\cup\{b\}\) also gives

\[
|S_b|\le f-6. \tag{3}
\]

Minimum degree at \(b\) gives the second column inequality

\[
 |S_b|\ge d_L(b)-6, \tag{4}
\]

because
\[
 d_H(b)=15-d_L(b)+|S_b|\ge9.
\]

For each excluded shell, the verifier supplies an integer \(q\ge0\) and a
vertex set \(W\subseteq A\) such that every set \(S\) satisfying the
triangle and size conditions obeys

\[
 q+|S\cap W|\le|S|. \tag{5}
\]

It checks (5) directly over all \(512\) subsets of \(A\).  Summing (5)
over the sixteen columns and using \(|D_a|\ge d_F(a)\) gives

\[
 c\ge16q+\sum_{a\in W}d_F(a). \tag{6}
\]

The certified lower bounds and the global upper bounds are:

| \(m\) | graph6 \(F\) | lower bound from (6) | \(f+m-45\) |
|---:|:---|---:|---:|
| 56 | `H???Fbp` | 24 | 20 |
| 56 | `H???Frx` | 24 | 22 |
| 57 | `H???CB\|` | 21 | 20 |
| 57 | `H???EBx` | 21 | 20 |
| 57 | `H???EB\|` | 22 | 21 |
| 57 | `H???FBp` | 23 | 20 |
| 57 | `H???FBx` | 22 | 21 |
| 57 | `H???FB\|` | 23 | 22 |
| 57 | `H???Fbp` | 24 | 21 |
| 57 | `H???Fbx` | 23 | 22 |
| 57 | `H???Fb\|` | 24 | 23 |
| 57 | `H???Frx` | 24 | 23 |
| 57 | `H???Fr\|` | 25 | 24 |
| 57 | `H??EEBB` | 22 | 20 |
| 57 | `H?BEENE` | 32 | 24 |

This excludes both \(m=56\) shells and thirteen of the sixteen \(m=57\)
shells.

## 4. The three surviving shells at \(m=57\)

The three remaining graph6 strings are

\[
 \texttt{H???Fbo},
 \qquad
 \texttt{H???Frw},
 \qquad
 \texttt{H???Fz\{},
\]

and they are \(K_{2,k}\) plus \(7-k\) isolated vertices for
\(k=4,5,6\), respectively.  Let \(p,q\) be the two hubs, let
\(u_1,\ldots,u_k\) be the leaves, and let \(z\) be the total size of the
isolated rows.  Write

\[
 |D_p|+|D_q|=2k+x,
 \qquad
 \sum_{i=1}^k|D_{u_i}|=2k+y.
\]

The global bound is

\[
 x+y+z\le12-2k. \tag{7}
\]

Every hub-leaf edge of \(F\) gives an eight-vertex-cover inequality.
Summing the \(2k\) inequalities gives

\[
 kx+2y\ge2k(6-k). \tag{8}
\]

For \(k=4,5,6\), (7) and (8) force

\[
 x=12-2k,
 \qquad
 y=z=0.
\]

It follows that both hub rows have size six, every leaf row has size two,
and every isolated row is empty.  Each hub row is disjoint from each leaf
row, and their union is an eight-vertex minimum cover of \(L\).

## 5. Minimum-cover classification

For a minimum cover \(C\) of \(L\), an admissible hub row and leaf row have
the form

\[
 P=C\setminus J,
 \qquad
 |P|=6,
 \qquad
 |J|=2.
\]

The verifier reconstructs all \(120\) valid unlabelled \(m=57\) cores and
all such pairs.  Their minimum-cover profiles are:

| core type | number of cores | ordered compatible hub pairs per core |
|:---|---:|---:|
| two disjoint covers | 113 | 56 |
| one cover | 3 | 28 |
| two covers meeting in seven vertices | 3 | 91 |
| three-cover star case | 1 | 119 |

For the first \(113\) cores, the two covers are the bipartition classes.
A common leaf pair forces both hub rows to come from one class.  All row
support then lies in that class, leaving the opposite class with column
count zero.  The degrees on the opposite class sum to \(57>8\cdot6\), so
one of those columns requires a positive count.  This is a contradiction.

For the seven exceptional cores, the verifier checks every compatible
ordered hub pair.  It unions all possible common leaf pairs, which is at
least the support of any actual choice of \(k\) leaf rows.  In every case,
this maximal support misses a vertex of \(L\)-degree at least seven.  The
column lower bound at that vertex is positive, again a contradiction.
The seven exceptional cores account for \(476\) ordered hub pairs.  Across
all \(120\) cores, the support check covers \(6{,}804\) ordered hub pairs.
A separate residual-demand dynamic-program check in the same verifier
confirms that no choice of \(k\) leaf rows meets all column demands for any
\(k=4,5,6\).

## 6. Verification

Run:

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_order26_m56_m57_shells.py \
  --geng /private/tmp/nauty289-build/geng

python3 research/erdos-617-r6/verify_r9_p93_order26_m57_k2k.py \
  --geng /private/tmp/nauty289-build/geng
~~~

The current receipts are:

~~~text
raw_shells_checked=11088
level_56_shells=2 dual_excluded=2
level_57_shells=16 dual_excluded=13
status=PASS

cores_verified=120
generic_bipartite_cores=113
exceptional_cores=7
support_pairs_checked=6804
exception_profile={'seven_edge_star': 1,
                   'seven_intersection': 3,
                   'unique_cover': 3}
k=4 feasible=0 excluded=120
k=5 feasible=0 excluded=120
k=6 feasible=0 excluded=120
status=PASS
~~~

Both sources pass `py_compile`, Ruff, and mypy.  An independent line audit
replayed both programs and checked the catalog reduction, dual summation,
forced equality, minimum-cover parameterization, and support obstruction.

## 7. Exact scope

The proved local statement is:

> No target graph \(H\) satisfying the setup above can have
> \(e(L)\in\{56,57\}\).

Catalog completeness relies on the standard exhaustive generation claim
of nauty `geng`.  No SAT answer, floating-point optimization, or unverified
solver trace is used in the proof.

The levels \(m=58,\ldots,64\) remain outside this theorem.  The entire
degree-nine branch, \(P_3(26)\ge121\), fixed \(r=9\), and Erdős Problem 617
remain open.
