# A colored core ladder for Erdős Problem 617

## Scope

This note records a consequence of color coexistence which is absent from
the one-color stability problem. It excludes every triangle-free terminal
core of order at least \(2r\), gives an exact recursive exclusion ladder for
higher independence layers, and proves that the nonneighbor graph at a
degree-at-most-\(r-1\) vertex cannot contain \(r-4\) disjoint copies of
\(K_r\).

The note does not prove that a low-degree nonneighbor graph contains those
\(r-4\) blocks. That block-production statement remains open outside the
conditional shell treated in UNIFORM_EXCEPTION_SHELL_OBSTRUCTION.md.

Let the edges of \(K_{r^2+1}\) be colored with colors
\(0,\ldots,r-1\), and suppose that every \((r+1)\)-set sees every color.
Write \(G_i\) for the graph formed by color \(i\). Then

\[
 \alpha(G_i)\le r,
 \qquad
 e(G_i[S])\le\binom r2+1\quad(|S|=r+1)
 \qquad(0\le i<r).
\tag{1}
\]

For \(n=ar+b\), where \(0\le b<r\), put

\[
 p_r(n)=(r-b)\binom a2+b\binom{a+1}2
       =r\binom a2+ab.
\tag{2}
\]

This is the minimum number of edges in an \(n\)-vertex graph with
independence number at most \(r\).

## 1. The induced-density inequality

**Lemma 1 (colored induced density).** For every color \(i\) and every
vertex set \(W\) of order \(n\),

\[
 e\bigl(\overline{G_i[W]}\bigr)\ge (r-1)p_r(n),
\tag{3}
\]

or equivalently

\[
 e(G_i[W])\le
 D_r(n):=\binom n2-(r-1)p_r(n).
\tag{4}
\]

If equality holds, then for every \(j\ne i\), the graph \(G_j[W]\) is
the disjoint union of \(b\) copies of \(K_{a+1}\) and \(r-b\) copies of
\(K_a\).

**Proof.** By (1), each \(G_j[W]\), \(j\ne i\), has independence number
at most \(r\). Turán's theorem applied to its complement gives
\(e(G_j[W])\ge p_r(n)\), with the stated equality case. The graphs
\(G_j[W]\), \(j\ne i\), partition the edges of
\(\overline{G_i[W]}\). Summing proves (3) and (4). \(\square\)

The first values used below are

\[
 p_r(2r)=r,\qquad p_r(2r+1)=r+2,
\tag{5}
\]

and hence

\[
 D_r(2r)=r^2,\qquad D_r(2r+1)=r^2+2.
\tag{6}
\]

At a vertex \(v\) of color-\(i\) degree \(d\le r-1\), let

\[
 N=N_{G_i}(v),\qquad
 U=V\setminus(N\cup\{v\}).
\]

The corresponding exact values are

\[
\begin{array}{c|c|c}
 W& p_r(|W|)&D_r(|W|)\\ \hline
 N&0&\binom d2\\[2mm]
 N\cup U&\dfrac{r^2(r-1)}2&r^2(r-1)\\[3mm]
 U&\dfrac{(r-1)(r^2-2d)}2&
 r^2(r-1)-2rd+\dfrac{d(d+3)}2.
\end{array}
\tag{7}
\]

The bounds in (7) do not by themselves exclude any branch
\(2\le d\le r-1\). Their use is on smaller dense residuals.

Lemma 1 is a consequence of the full coloring, not a new hypothesis. It
is stronger than the one-color package consisting of (1) for one graph
and the local edge cap. The one-color package does not require the
complement edges to split into \(r-1\) further graphs, each with
independence number at most \(r\).

There is a strict strengthening when one color has small independence
number.

**Lemma 1A (nonpartite colored density).** Suppose \(2\le s<r\),
\(|W|=sr+t\), and \(t\ge1\). If \(\alpha(G_i[W])\le s\), then

\[
 e\bigl(\overline{G_i[W]}\bigr)
 \ge (r-1)\left(p_r(|W|)+\left\lfloor\frac{|W|}{r}\right\rfloor-1\right).
\tag{4a}
\]

In particular, when \(1\le t<r\), the improvement over (3) is
\((r-1)(s-1)\).

**Proof.** The graph \(G_i[W]\) is not \(r\)-colorable, since each color
class in a proper coloring would have order at most \(s\), while
\(|W|>rs\). For every \(j\ne i\), the graph
\(G_i[W]\) is a subgraph of \(\overline{G_j[W]}\). Hence
\(\overline{G_j[W]}\) is not \(r\)-partite. It is also
\(K_{r+1}\)-free because \(\alpha(G_j)\le r\). Kang and Pikhurko give

\[
 e(G_j[W])\ge
 p_r(|W|)+\left\lfloor\frac{|W|}{r}\right\rfloor-1.
\]

Summing this over the \(r-1\) choices of \(j\) proves (4a). \(\square\)

The final minus one cannot be dropped from this argument. Equality in
Kang and Pikhurko's bound is attained by their extremal family. Equality
in (4a) would require every other color complement on \(W\) to be one of
those equality graphs. Their simultaneous coexistence is not ruled out by
the numerical theorem alone.

## 2. The triangle-free terminal layer

**Theorem 2 (colored terminal core).** Let \(r\ge6\). There is no vertex
set \(W\) of order at least \(2r\) for which

\[
 \alpha(G_i[W])\le2,
 \qquad
 \omega(G_i[W])\le r-1.
\tag{8}
\]

**Proof.** Put \(H=G_i[W]\), \(L=\overline H\), and \(n=|W|\). The first
condition in (8) says that \(L\) is triangle-free. The second says that
\(\alpha(L)\le r-1\). Every neighborhood in \(L\) is independent, so

\[
 \Delta(L)\le r-1,
 \qquad
 e(L)\le\frac{n(r-1)}2.
\tag{9}
\]

Lemma 1 gives the opposite bound

\[
 e(L)\ge(r-1)p_r(n).
\tag{10}
\]

At \(n=2r\), the two bounds force equality. Thus \(L\) is
\((r-1)\)-regular. Since

\[
 r-1>\frac{2(2r)}5
 \qquad(r\ge6),
\]

the Andrásfai-Erdős-Sós theorem makes \(L\) bipartite. One side of its
bipartition has order at least \(r\), contrary to
\(\alpha(L)\le r-1\).

For \(n>2r\), one has \(p_r(n)>n/2\). This follows from
\(p_r(2r)=r\) and

\[
 p_r(m+1)-p_r(m)=\left\lfloor\frac mr\right\rfloor\ge2
 \qquad(m\ge2r).
\]

Equations (9) and (10) then contradict one another. \(\square\)

In the equality calculation at \(n=2r\), every other color on \(W\)
would have to be a perfect matching. The union of those \(r-1\) perfect
matchings is the impossible \((r-1)\)-regular graph \(L\).

Theorem 2 removes every odd-cycle residual of order \(2r+1\), including
all weighted \(C_5\)-blow-up examples. No classification of the blow-up
weights is needed.

## 3. The exact recursive ladder

For fixed \(r\ge6\), define thresholds \(T_s=T_s(r)\) as follows. Put

\[
 T_2=0.
\tag{11}
\]

Suppose \(T_{s-1}\) is defined. Set

\[
 A_s=(s+1)r-2s-T_{s-1}+1,
 \qquad
 \widehat B_s=rs(s+T_{s-1}-2)-2(r-1)(s-1).
\tag{12}
\]

If \(A_s>0\) and

\[
 T_s:=\max\left\{1,
 \left\lfloor\frac{\widehat B_s}{A_s}\right\rfloor+1\right\}<r,
\tag{13}
\]

retain this value. Otherwise the present recursion stops.

**Theorem 3 (exact colored core ladder).** Whenever \(T_s(r)\) is
defined, there is no vertex set \(W\) with

\[
 |W|\ge sr+T_s,
 \qquad
 \alpha(G_i[W])\le s,
 \qquad
 \omega(G_i[W])\le r-1.
\tag{14}
\]

**Proof.** The case \(s=2\) is Theorem 2. Suppose the assertion is known
at \(s-1\), and put \(H=G_i[W]\), \(L=\overline H\). The graph \(L\) is
\(K_{s+1}\)-free and has independence number at most \(r-1\). For every
vertex \(x\), the graph \(L[N_L(x)]\) is \(K_s\)-free and still has
independence number at most \(r-1\). The induction hypothesis gives

\[
 \Delta(L)\le (s-1)r+T_{s-1}-1=:\Delta_s.
\tag{15}
\]

For \(n=sr+t\), \(1\le t<r\), Lemma 1A and (2) give

\[
 2e(L)\ge
 2(r-1)\left(r\binom s2+st+s-1\right).
\tag{16}
\]

On the other hand, (15) gives \(2e(L)\le n\Delta_s\). The doubled lower
bound minus the doubled upper bound is

\[
 \widehat F_s(t)=A_st-\widehat B_s.
\tag{17}
\]

The definition (13) is exactly the first eligible integer \(t\ge1\) for
which \(\widehat F_s(t)>0\). For larger orders, Lemma 1A gives the lower
bound

\[
 2(r-1)\left(p_r(n)+\left\lfloor\frac nr\right\rfloor-1\right).
\]

Its increment minus the increment of \(n\Delta_s\) is at least

\[
 2(r-1)\left\lfloor\frac nr\right\rfloor-\Delta_s
 \ge A_s>0.
\]

Thus the contradiction persists for every \(n\ge sr+T_s\). \(\square\)

There is also a simple closed-form version.

**Corollary 4.** If

\[
 2r>s^2-s+4,
\tag{18}
\]

then (14) holds with

\[
 T_s=\binom{s-1}{2}.
\tag{19}
\]

**Proof.** Use the coarser induction thresholds
\(\binom{s-2}{2}\) and \(\binom{s-1}{2}\) in (15)-(17). At the proposed
new threshold, the doubled lower bound minus the doubled upper bound is

\[
 \frac{(s-2)(s-1)(2r-s^2+s-4)}4>0.
\]

The increment after that point is positive as in Theorem 3. \(\square\)

In particular,

\[
 T_3(r)=1
 \qquad(r\ge6).
\tag{20}
\]

The first new thresholds are

\[
 T_4(r)=2\qquad(r\ge6),
\tag{20a}
\]

and, for \(r=6,7,8\),

\[
 (T_5(6),T_5(7),T_5(8))=(5,5,4).
\tag{20b}
\]

The same induction gives a pointwise degree consequence that will be used
below.

**Lemma 4A (residual minimum degree).** Suppose \(T_{s-1}(r)\) is
defined, \(|W|=sr+t\), and

\[
 \alpha(G_i[W])\le s,
 \qquad \omega(G_i[W])\le r-1.
\]

Then every vertex of \(G_i[W]\) has degree at least

\[
 r+t-T_{s-1}(r).
\tag{20c}
\]

**Proof.** The nonneighbors of a vertex induce a graph with independence
number at most \(s-1\) and clique number at most \(r-1\). Theorem 3 says
that there are at most \((s-1)r+T_{s-1}-1\) such nonneighbors. Subtracting
this from \(|W|-1\) gives (20c). \(\square\)

## 4. The \(r-4\)-block contradiction

The following consequence is the main application to the outer
low-degree branches.

**Theorem 5.** Let \(r\ge6\), fix a color \(i\), and let \(v\) have
\(G_i\)-degree \(d\le r-1\). Its nonneighbor set \(U\) cannot contain
\(r-4\) pairwise disjoint copies of \(K_r\) in color \(i\).

**Proof.** Since \(v\) is anticomplete to \(U\) in color \(i\),

\[
 \alpha(G_i[U])\le r-1.
\tag{21}
\]

Extend the proposed blocks to a maximal packing of \(k\) color-\(i\)
copies of \(K_r\) in \(U\), and let \(R\) be the remainder. Put

\[
 s=r-k-1.
\]

The representative-selection argument gives

\[
 \alpha(G_i[R])\le s.
\tag{22}
\]

For completeness, an independent \((s+1)\)-set in \(R\) could be
extended through the \(k\) blocks by choosing one independent
representative from each. Each previously chosen vertex forbids at most
one vertex in the next \(K_r\), and
\((s+1)+k=r\). This would make an independent \(r\)-set in \(U\),
contrary to (21).

The packing is maximal, so

\[
 \omega(G_i[R])\le r-1.
\tag{23}
\]

Write \(t=r-d\ge1\). Since

\[
 |U|=r^2-d=r(r-1)+t,
\]

the remainder has order

\[
 |R|=sr+t.
\tag{24}
\]

If \(k=r-4\), then \(s=3\), and (20), (22)-(24) contradict Theorem 3.
If \(k=r-3\), Theorem 2 gives the same contradiction at \(s=2\).
If \(k=r-2\), then (22) makes \(R\) a clique, while
\(|R|=r+t\ge r+1\). This gives a monochromatic \(K_{r+1}\). Finally,
a packing with \(k\ge r-1\) contains \(r-1\) blocks and leaves at least
one vertex outside those blocks. That vertex and one independent
representative from each of the \(r-1\) blocks give an independent
\(r\)-set in \(U\). These cases exhaust every maximal extension of the
original \(r-4\) blocks. \(\square\)

More generally, a maximal packing with

\[
 k=r-s-1
\]

is excluded whenever \(T_s(r)\) is defined and

\[
 r-d\ge T_s(r).
\tag{25}
\]

## 5. Comparison with the scalar Kang-Pikhurko stop bound

The colored ladder does not yet force the required blocks. The remaining
distance can be stated exactly.

For this comparison, let \(G_i\) be a least color graph, let \(v\) be a
minimum-degree vertex, assume \(2\le d=d_{G_i}(v)\le r-1\), and put
\(t=r-d\). If

\[
 X=e_{G_i}(N,U),\qquad Y=e_{G_i}(N),\qquad A=X+Y,
\]

then minimum degree gives \(X+2Y\ge d(d-1)\). Since
\(Y\le\binom d2\), it follows that \(A\ge\binom d2\). Now consider a
maximal packing with \(k=r-s-1\). The remainder has order \(n=sr+t\).
The least-color bound \(e(G_i)\le M_r\) shows that its edge count is at
most

\[
 U_{r,d,s}
 =M_r-d-\binom d2-(r-s-1)\binom r2,
 \qquad
 M_r=\frac{r(r^2+1)}2.
\tag{26}
\]

Its complement is \(K_{s+1}\)-free and is not \(s\)-partite. The latter
claim follows because an \(s\)-partition would have a part of order at
least \(r+1\), which would be a forbidden clique in the remainder.
Kang and Pikhurko's theorem, followed by its local equality exclusion,
therefore gives

\[
 e(R)\ge p_s(n)+\left\lfloor\frac ns\right\rfloor.
\tag{27}
\]

For the equality exclusion, use their extremal construction. Its \(s\)
old parts have total order \(n-1\). If \(t\ge2\), one old part has order
at least \(r+1\). If \(t=1\), all old parts have order \(r\). For a
special old part \(S\), the two sets \(S\cup\{x\}\) and
\(S\cup\{y\}\) in that construction force both
\(|A|\le1\) and \(r-|A|\le1\), which is impossible for \(r\ge3\).

Thus a scalar-feasible stop must satisfy

\[
 p_s(sr+t)+\left\lfloor\frac{sr+t}{s}\right\rfloor
 \le U_{r,d,s}.
\tag{28}
\]

Equations (25) and (28) are the exact two tests. They do not cover all
parameters. In particular, \(s=r-1\), corresponding to no peeled block,
always passes (28). The slack is

\[
 \frac{d(2r-d-1)-2r}{2}>0
 \qquad(2\le d\le r-1,\ r\ge6).
\tag{29}
\]

The closed-form colored ladder reaches
\(s<\sqrt{2r}+O(1)\), while (29) leaves the stop \(s=r-1\). The exact
recursion (11)-(13) improves the finite thresholds but still leaves this
gap. The next theorem needed for the full problem is a block-production
or colored-stability statement that moves a low-degree residual from the
scalar-feasible range into one of the layers excluded here.

## 6. A recursive block-production theorem

The colored ladder can also be used at the bottom of a recursive
minimum-degree argument. This gives a first unconditional block-production
range.

Fix the ambient parameter \(r\). For integers \(a,m\ge0\), let
\({\cal F}_r(a,m)\) be the family of induced graphs \(G_i[W]\), ranging
over target colors in hypothetical balanced \(r\)-colorings, such that
\(|W|=m\) and

\[
 \alpha(G_i[W])\le a,
 \qquad
 \omega(G_i[W])\le r-1.
\tag{30}
\]

Every member and each of its induced subgraphs satisfies

\[
 e(G_i[Z])\le D_r(|Z|)
 \qquad(Z\subseteq W)
\]

by Lemma 1. Notice also that

\[
 D_r(r+1)=\binom r2+1,
\]

so every member also inherits the local cap.

The full-color provenance in this definition is necessary. An abstract
graph satisfying only the two invariants in (30) and the induced target
edge cap need not satisfy the terminal exclusions from Theorem 3.

We next define a certified lower bound \(B_r(a,m)\), with value \(+\infty\)
when the recursion certifies that \({\cal F}_r(a,m)\) is empty. Put

\[
 B_r(0,0)=0,\qquad B_r(0,m)=+\infty\quad(m>0),
\tag{31}
\]

and

\[
 B_r(1,m)=
 \begin{cases}
  \binom m2,&m\le r-1,\\
  +\infty,&m\ge r.
 \end{cases}
\tag{32}
\]

For \(a\ge2\), define the scalar lower bound

\[
 Q_r(a,m)=p_a(m)+
 \begin{cases}
  0,&m\le a(r-1),\\
  \lfloor m/a\rfloor-1,&a(r-1)<m\le ar,\\
  \lfloor m/a\rfloor,&m\ge ar+1.
 \end{cases}
\tag{33}
\]

For a possible minimum degree \(\delta\), put

\[
 C_r(\delta)=
 \begin{cases}
  \binom{\delta+1}{2},&0\le\delta<r-1,\\
  \binom r2+1,&\delta=r-1,\\
  \displaystyle
  \delta+
  \left\lceil\frac{r+2}{r}\binom\delta2\right\rceil,
    &\delta\ge r.
 \end{cases}
\tag{34}
\]

If \(T_a(r)\) is defined and \(m\ge ar+T_a(r)\), set
\(B_r(a,m)=+\infty\). Otherwise let

\[
 R_r(a,m)=
 \min_{\substack{0\le\delta<m\\
 B_r(a-1,m-1-\delta)<+\infty}}
 \max\left\{
 B_r(a-1,m-1-\delta)+C_r(\delta),
 \left\lceil\frac{m\delta}{2}\right\rceil
 \right\},
\tag{35}
\]

where the minimum of an empty set is \(+\infty\). Set

\[
 b_r(a,m)=\max\{Q_r(a,m),R_r(a,m)\}.
\]

Finally, set \(B_r(a,m)=+\infty\) if
\(b_r(a,m)>D_r(m)\), and set \(B_r(a,m)=b_r(a,m)\) otherwise.

**Theorem 6 (recursive colored lower bound).** Every graph
\(F\in{\cal F}_r(a,m)\) satisfies

\[
 e(F)\ge B_r(a,m).
\tag{36}
\]

In particular, a value \(B_r(a,m)=+\infty\) certifies that the family is
empty.

**Proof.** We induct on \(a\). The cases \(a=0,1\) are immediate. For
\(a\ge2\), Turan's theorem gives \(e(F)\ge p_a(m)\). If
\(m>a(r-1)\), the complement of \(F\) is \(K_{a+1}\)-free and is not
\(a\)-partite: an \(a\)-partition would give a clique of order at least
\(r\) in \(F\). Kang and Pikhurko therefore give the middle line of
(33).

When \(m\ge ar+1\), their equality construction is incompatible with the
local cap, which supplies the extra unit in the last line of (33). If
\(m\ge ar+2\), its \(a\) old parts have total order \(m-1>ar\), so an old
part gives a clique of order at least \(r+1\). If \(m=ar+1\), all old
parts have order \(r\). In the notation of their construction, the special
old part \(S\), exceptional vertex \(x\), witness vertex \(y\), and
nonempty proper set \(A\subset S\) give

\[
 e(F[S\cup\{x\}])=\binom r2+r-|A|,
 \qquad
 e(F[S\cup\{y\}])=\binom r2+|A|.
\]

The local cap would require both \(r-|A|\le1\) and \(|A|\le1\), which is
impossible for \(r\ge6\). This proves \(e(F)\ge Q_r(a,m)\).

Now choose a minimum-degree vertex \(x\), write
\(\delta=d_F(x)\), \(N=N_F(x)\), and
\(U=V(F)\setminus(N\cup\{x\})\). The graph \(F[U]\) lies in
\({\cal F}_r(a-1,m-1-\delta)\). Put

\[
 X=e_F(N,U),\qquad Y=e_F(N).
\]

Minimum degree gives

\[
 X+2Y\ge\delta(\delta-1).
\tag{37}
\]

Since \(Y\le\binom\delta2\), this first gives
\(X+Y\ge\binom\delta2\). If \(\delta=r-1\), equality would force
\(Y=\binom{r-1}{2}\) and \(X=0\). Then \(N\cup\{x\}\) would be a
copy of \(K_r\), contrary to (30), so one extra edge is required.

If \(\delta\ge r\), average the local cap over the sets
\(\{x\}\cup S\), where \(S\) runs through the \(r\)-subsets of \(N\).
Each such \(S\) spans at most \(\binom{r-1}{2}\) edges, and hence

\[
 Y\le\frac{r-2}{r}\binom\delta2.
\tag{38}
\]

Combining (37) and (38) gives

\[
 \delta+X+Y\ge C_r(\delta).
\tag{39}
\]

The induction hypothesis on \(F[U]\), followed by (39), proves the
first term inside the maximum in (35). Since \(\delta\) is the minimum
degree of the \(m\)-vertex graph \(F\), the degree sum also gives

\[
 e(F)\ge\left\lceil\frac{m\delta}{2}\right\rceil.
\]

Taking both bounds for the same value of \(\delta\), and then minimizing
over the possible minimum degrees, proves (35). Theorem 3 justifies every terminal
\(+\infty\) value. Finally, every member of the family has
\(e(F)\le D_r(m)\), so \(b_r(a,m)>D_r(m)\) also makes the family empty.
This completes the induction. \(\square\)

Here is the packing consequence. Let \(G_i\) be a least color graph, let
\(v\) be a minimum-degree vertex of degree \(d\le r-1\), and let \(U\)
be its nonneighbor set. Suppose \(j\) disjoint color-\(i\) copies of
\(K_r\) have already been selected in \(U\), and let \(R_j\) be their
complement in \(U\). If \(R_j\) has no further \(K_r\), then

\[
 R_j\in{\cal F}_r(r-1-j,r^2-d-jr).
\tag{40}
\]

Indeed, representative selection gives
\(\alpha(R_j)\le r-1-j\). The least-color and minimum-degree estimates
from Section 5 also give

\[
 e(R_j)\le
 E_{r,d,j}:=M_r-d-\binom d2-j\binom r2.
\tag{41}
\]

We have proved the following entry criterion.

**Corollary 7 (certified packing step).** If

\[
 B_r(r-1-j,r^2-d-jr)>E_{r,d,j},
\tag{42}
\]

with \(+\infty\) larger than every integer, then every packing of \(j\)
copies of \(K_r\) in \(U\) extends to a packing of \(j+1\) copies.
If (42) holds for \(j=0,\ldots,r-5\), then the proposed balanced coloring
does not exist, by Theorem 5.

The exact recursion gives the following margins. An entry \(+\infty\)
means that the corresponding no-next-block family is empty.

\[
\begin{array}{c|c|ccc}
r&d&\multicolumn{3}{c}{B_r-E_{r,d,j}\text{ for }j=0,1,2}\\ \hline
7&0&57&+\infty&+\infty\\
7&1&42&+\infty&+\infty\\
7&2&25&+\infty&+\infty\\
7&3&18&28&+\infty\\
7&4&10&9&+\infty\\
7&5&5&4&+\infty\\
7&6&-1&-2&-3
\end{array}
\tag{43}
\]

Thus every \(r=7\) branch with \(d\le5\) is impossible. This recursion
alone leaves \(d=6\). R7_FIXED_OUTER_CLOSURE.md adds a weighted light-edge
refinement that closes that final row.

**Corollary 8 (the fixed \(r=7\) degree reduction).** In a hypothetical
balanced seven-coloring of \(K_{50}\), every least color graph has minimum
degree six.

**Proof.** The general least-color reduction gives
\(2\le\delta\le6\). For each \(d\le5\), every entry in the corresponding
row of (43) is either positive or \(+\infty\). Corollary 7 therefore
produces three disjoint copies of \(K_7\) in the nonneighbor graph, contrary
to Theorem 5. Hence \(d=6\). \(\square\)

For \(r=8\), the four required packing steps are

\[
\begin{array}{c|rrrr}
d&j=0&j=1&j=2&j=3\\ \hline
0&60&104&+\infty&+\infty\\
1&44&72&+\infty&+\infty\\
2&35&41&+\infty&+\infty\\
3&24&23&+\infty&+\infty\\
4&17&16&+\infty&+\infty\\
5&8&7&6&+\infty\\
6&3&2&1&+\infty\\
7&-4&-5&-6&-7
\end{array}
\tag{44}
\]

Consequently every \(r=8\) branch with \(d\le6\) is impossible.

**Corollary 9 (the fixed \(r=8\) degree reduction).** In a hypothetical
balanced eight-coloring of \(K_{65}\), every least color graph has minimum
degree seven.

**Proof.** The general least-color reduction gives
\(2\le\delta\le7\). Table (44) and Corollary 7 exclude every
\(d\le6\). \(\square\)

This does not close the \(r=8\) case. The degree-seven row remains open.
The same recursion is uniform in \(r\), but its strict margins do not
currently cover every possible minimum degree.
