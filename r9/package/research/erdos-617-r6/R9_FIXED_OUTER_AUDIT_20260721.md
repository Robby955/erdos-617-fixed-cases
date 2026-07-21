# Fixed \(r=9\) outer implication audit

Date: 21 July 2026

## Verdict

PASS LOCALLY. The two terminal packages are banked. The new 37-vertex
full-color lemma repairs the last outer row. The complete implication proves
that every nine-coloring of \(K_{82}\) has a ten-vertex set omitting a color.

The human argument and arithmetic replay pass. The order-27 artifacts have
passed replay from a copied package. The order-26 \(m=64\) solver-free proof,
independent CaDiCaL reconstruction, dependency manifest, and clean-checkout
replay pass. External mathematical review remains pending.

## 1. Starting from a hypothetical coloring

Assume every ten vertices see all nine colors. Choose a least color and let
\(G\) be its graph. Then

\[
 e(G)\le369,
 \qquad
 \alpha(G)\le9,
 \qquad
 e_G(S)\le37\quad(|S|=10).
\]

The checked least-color reduction gives

\[
 2\le\delta(G)\le8.
\tag{1}
\]

No fixed-case conclusion is used in deriving (1).

## 2. Terminal inputs

The order-26 proof gives

\[
 P_3(26)\ge121.
\tag{2}
\]

Its minimum-degree split is eight or nine. The common 17-core two-row
theorem excludes degree eight. The degree-nine proof partitions the
16-vertex core into levels \(m=56,\ldots,64\), all of which are locally
closed.

The order-27 proof gives

\[
 P_3(27)=\varnothing.
\tag{3}
\]

Its minimum-degree split is nine or ten. The common 17-core theorem excludes
degree nine. Exact regularity and the edge-degree-sum lemma reduce the 332
degree-ten cores to 50; independently reconstructed LRAT proofs exclude all
50.

The definitions of (2)-(3) match their use below: these are actual induced
target graphs with the inherited full-color inequalities, independence cap
three, and no target \(K_9\).

## 3. Audit of the 37-vertex lemma

Let \(H\) have 37 vertices, \(\alpha(H)\le4\), and \(\omega(H)\le8\).
Assume \(e(H)\le191\).

1. If a vertex has degree at most nine, 27 of its nonneighbors induce a
   graph with independence number at most three and clique number at most
   eight. This contradicts (3). Hence \(\delta(H)\ge10\).
2. Since \(2e(H)/37<11\), a degree-ten vertex \(v\) exists.
3. Its neighborhood \(A\) has order ten and its nonneighborhood \(B\) has
   order 26.
4. Put \(M=45-e(H[A])\). On \(\{v\}\cup A\), the full-color cap
   \(D_9(11)=39\) gives \(M\ge16\).
5. Minimum degree at each \(a\in A\) gives at least
   \(d_{\overline{H[A]}}(a)\) target neighbors in \(B\). The total cross
   incidence is therefore at least \(2M\).
6. The graph \(H[B]\) has independence number at most three because \(v\)
   is target-anticomplete to \(B\). It has no \(K_9\). Input (2) gives at
   least 121 target edges in \(B\).
7. The four disjoint edge regions give
   \[
   e(H)\ge10+(45-M)+121+2M=176+M\ge192,
   \]
   a contradiction.

Retaining \(M\) is necessary: \(e(H[A])=45-M\le29\) is an upper bound,
not a lower bound. The cross-incidence gain \(2M\) more than compensates
for the \(-M\) contribution of \(H[A]\). This proves
\(P_4(37)\ge192\).

## 4. Recursive propagation

With (2), (3), and \(P_4(37)\ge192\), the independent recurrence gives

\[
\begin{array}{c|ccccc}
(a,n)&(4,37)&(5,46)&(6,55)&(7,64)&(8,73)\\ \hline
B_9(a,n)&192&227&264&301&338.
\end{array}
\]

For outer degree eight, the five edge uppers are

\[
 189,225,261,297,333
\]

when read in the same order. The margins are \(3,2,3,4,5\), or
\(5,4,3,2,3\) in packing order \(j=0,\ldots,4\). Every inequality is
strict.

The same implementation checks the other 40 outer cells. They remain strict
or empty. A weakened 37-vertex floor of 189 leaves one zero margin. Keeping
the order-27 node finite restores four negative margins. These two mutation
checks confirm that both new inputs are active dependencies.

## 5. Final block contradiction

For a minimum-degree vertex of \(G\), let \(U\) be its nonneighbor set.
The strict cell at packing stage \(j\) says that a maximal packing cannot
stop after \(j\) target copies of \(K_9\). Representative selection lowers
the residual independence cap by one at every deletion, and counting only
the 36 internal block edges gives a valid residual upper bound.

The five strict degree-eight cells force five disjoint target copies of
\(K_9\) in \(U\). The checked \(r-4\)-block theorem forbids five such
blocks when \(r=9\). This contradiction eliminates the last case in (1).

## 6. Exact theorem and nonclaims

The locally proved theorem is:

> Every nine-coloring of the edges of \(K_{82}\) contains ten vertices
> whose induced edges omit at least one color.

The proof is computer-assisted through the order-26 and order-27 terminal
packages. The 37-vertex bridge and outer propagation are human-readable.
No implication to \(r=10\) or arbitrary \(r\) is claimed. Erdős Problem
617 remains open.
