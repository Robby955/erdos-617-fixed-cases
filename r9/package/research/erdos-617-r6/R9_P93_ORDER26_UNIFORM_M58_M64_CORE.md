# Fixed \(r=9\), order 26: the uniform core lemma for \(58\le m\le64\)

## Status

The core structure and its small vertex covers are classified by a
solver-free argument throughout the levels \(58\le m\le64\).

This note supplies a common input for those seven levels. It does not
exclude any level above \(m=58\), the full degree-nine branch, fixed
\(r=9\), or Erdős Problem 617.

## 1. Core structure

### Lemma 1

Let \(L\) be a triangle-free graph on 16 vertices with

\[
 \alpha(L)\le8
 \qquad\text{and}\qquad
 e(L)=m\ge58.
\]

Then \(L\) is bipartite with two sides \(X,Y\) of order eight. In
particular,

\[
 L=K_{8,8}-Q,
 \qquad
 |Q|=64-m\le6.
\]

The only independent eight-sets of \(L\) are \(X\) and \(Y\). Equivalently,
the only minimum vertex covers are \(X\) and \(Y\).

### Proof

Suppose that \(L\) is not bipartite, and let \(C\) be a shortest odd cycle
of length \(\ell\). Triangle-freeness gives \(\ell\ge5\), and minimality
makes \(C\) chordless.

Every vertex outside \(C\) has at most two neighbors on \(C\). To see this,
suppose that a vertex \(x\) has at least three. The cyclic gaps between
consecutive neighbors of \(x\) all have length at least two, since \(L\) is
triangle-free. Their sum is the odd number \(\ell\), so one gap has odd
length. That gap and the two edges through \(x\) form a shorter odd cycle,
a contradiction.

Mantel's theorem applied outside \(C\) now gives

\[
 e(L)
 \le
 \ell+2(16-\ell)
 +\left\lfloor\frac{(16-\ell)^2}{4}\right\rfloor.
\]

For odd \(\ell\ge5\), the right side is at most 57. This contradicts
\(m\ge58\), so \(L\) is bipartite.

Each bipartition side is independent and therefore has order at most eight.
The two orders sum to 16, so both are eight. Thus \(L=K_{8,8}-Q\), where
\(|Q|=64-m\le6\).

Suppose that an independent eight-set contains \(p\) vertices of \(X\) and
\(8-p\) vertices of \(Y\), where \(1\le p\le7\). All
\(p(8-p)\) cross-pairs between these vertices must lie in \(Q\), but

\[
 p(8-p)\ge7>|Q|.
\]

Hence the only independent eight-sets are \(X\) and \(Y\). Taking
complements proves the assertion about minimum covers. \(\square\)

## 2. Uniform small-cover rigidity

### Lemma 2

Use the notation of Lemma 1 and put \(d=|Q|=64-m\). If \(C\) is a vertex
cover of \(L\) with

\[
 |C|\le14-d=m-50,
\]

then \(C\) contains all of \(X\) or all of \(Y\).

### Proof

Put

\[
 A=X\setminus C,
 \qquad
 B=Y\setminus C.
\]

If \(C\) contains neither side, then \(A\) and \(B\) are nonempty. Since
\(C\) is a cover, every pair in \(A\times B\) must be a deleted edge, so

\[
 A\times B\subseteq Q.
\]

On the other hand,

\[
 |A|+|B|=16-|C|\ge d+2.
\]

For positive integers \(|A|,|B|\), this implies

\[
 |A||B|\ge |A|+|B|-1\ge d+1,
\]

contrary to \(|A||B|\le|Q|=d\). Thus \(C\) contains one whole side.
\(\square\)

The cover threshold at each level is therefore

| \(m\) | deleted edges \(d=64-m\) | every cover through size |
|---:|---:|---:|
| 58 | 6 | 8 |
| 59 | 5 | 9 |
| 60 | 4 | 10 |
| 61 | 3 | 11 |
| 62 | 2 | 12 |
| 63 | 1 | 13 |
| 64 | 0 | 14 |

At (m=64), the displayed value is only the uniform bound from Lemma 2.
Since (Q) is empty, every vertex cover of (K_{8,8}), of any order,
contains a full side.

## 3. The first mixed covers at \(m=59\)

At \(m=59\), write \(L=K_{8,8}-Q\) with \(|Q|=5\). Lemma 2 shows that
every vertex cover of order at most nine contains a full side.

Suppose that \(C\) is a ten-vertex cover containing neither side. Then
\(A=X\setminus C\) and \(B=Y\setminus C\) are nonempty,

\[
 |A|+|B|=6,
 \qquad
 |A||B|\le5.
\]

The only possibility is \(\{|A|,|B|\}=\{1,5\}\). Since \(|Q|=5\), the
deleted graph is exactly \(Q=K_{1,5}\), and \(A\cup B\) is its six-vertex
support. Conversely, this deleted star gives such a mixed ten-cover.

The same calculation gives two useful weaker tests:

1. a mixed cover of order at most 11 requires \(Q\) to contain a
   \(K_{1,4}\);
2. a mixed cover of order at most 12 requires \(Q\) to contain a
   \(K_{1,3}\) or a \(K_{2,2}\).

These statements are structural filters for the \(m=59\) incidence search.
They are not exclusions by themselves.

## 4. Arithmetic replay

The finite inequalities and all seven cover thresholds can be checked with

~~~sh
python3 \
  research/erdos-617-r6/verify_r9_p93_order26_uniform_m58_m64_core.py
~~~

The replay returns

~~~text
cover_thresholds={58: 8, 59: 9, 60: 10, 61: 11, 62: 12, 63: 13, 64: 14}
m59_mixed_ten=[(1, 5), (5, 1)]
uniform_m58_m64_core_arithmetic=VERIFIED
~~~

## 5. Exact nonclaims

1. The lemma does not classify all covers larger than the stated threshold.
2. It does not impose the shell incidence, column-degree, or full-color
   conditions.
3. It does not exclude \(m=59,\ldots,64\).
4. It does not prove the degree-nine branch, fixed \(r=9\), or Erdős
   Problem 617.
