# The twelve-color case of the Erdős–Gyárfás balanced-coloring conjecture

Robert Sneiderman · 24 November 2026

**Theorem.** Every twelve-coloring of the edges of $K_{145}$ has thirteen vertices whose induced complete graph misses a color.

In the five-row case, the 61 vertices span at least 409 edges of the target color. The global coloring permits at most 408. Two further local bounds, 283 edges on 47 vertices and 358 on 59 vertices, close the other cases. The proof uses earlier four-row certificates. The calculations have two integer implementations. Lean verifies the thirteen-vertex witness in Section 4. [Forward calculation](verify_order_twelve.py) · [Budget-first replay](replay_order_twelve.py) · [Lean proof of the witness](OrderTwelveCollision.lean)

## 1. Local edge bounds and neighborhood deletion

Call a coloring balanced if every thirteen vertices see all twelve colors. Suppose the coloring is balanced. Fix a target color $a$ and use its graph for degrees, neighborhoods, cliques and independence. A set of type $(s,n)$ has $n$ vertices, independence number at most $s$, and no target $K_{12}$. Write $f(s,n)$ for a lower bound on its target edge count. The earlier order bounds on the size of such sets are $N(0)=0,\ N(1)=11,\ N(2)\le23,\ N(3)\le35,\ N(4)\le48$. Only upper bounds are needed. The last two follow from the three-row theorem and $P(4)$ at twelve. [Two- and three-row results, Sections 6 and 8](overfull-core.md)

**The 48-vertex input.** In a set of type $(4,48)$ every degree is at least twelve by $N(3)$. The four-row certificates at order twelve exclude every case in which the minimum total of $d-12$ on an independent quartet is at most three. Section 2 of the same argument shows that either such a quartet exists or some other color partitions the 48 vertices into twelve independent quartets for the target. The latter partition gives a total degree of at least $48\cdot12+12\cdot4=624$. Thus $f(4,48)\ge312$. The 102 profiles surviving the earlier census all have quartet weight at least four. [Four-row argument and census](four-row-descent.md) · [Prerequisite verifier](verify_four_row_descent.py)

In a set of type $(s,n)$, deleting the closed neighborhood of a minimum-degree vertex leaves a set of type $(s-1,u)$, where $u=n-1-d$. Put $\tau=\max(0,u-N(s-2))$, using zero if the order bound is unavailable. A lower bound for the deletion cost is $\binom{d+1}{2}+P$, with
$$
 P=\begin{cases}
 0 & d\le10,\\
 \max(1,\tau-1)&d=11,\\
 \max(11,2\tau-6)&d=12,\\
 11(d-11)&d\ge13 .
 \end{cases}                                                     \tag{1}
$$
Here is the argument behind the premiums. If $A$ is the root's neighborhood, let $m$ count the nontarget pairs in $A$, and let $j(v)$ count those incident to $v$. The number of target neighbors of $v\in A$ in the remainder is $j(v)+h_v$, with $h_v\ge0$ by minimum degree. The exact deletion cost is $\binom{d+1}{2}+m+\sum h_v$. For any nontarget pair $v,w$ in $A$, their target neighbors in the remainder meet every independent $(s-1)$-set there. Otherwise that set extends by $v,w$. A hitting set has size at least $\tau$, so $j(v)+j(w)+h_v+h_w\ge\tau$. At $d=11$ such a pair exists, since a complete $A$ extends by the root, and $j(v)+j(w)\le m+1$. At $d=12$ the closed neighborhood sees all eleven other colors, all inside $A$, so $m\ge11$. The missing pairs cannot form a star, which would leave a target $K_{12}$ with the root, or lie on a triangle. Hence two are disjoint. Their four internal missing degrees sum to at most $m+6$, giving the third line of (1). At higher degrees each other color needs at least $d-11$ edges on the closed neighborhood, since deleting one endpoint per edge leaves an independent set in that color of size at most twelve. [Deletion identity, Section 12](overfull-core.md#12-order-ten)

For each $d$, take the larger of $\lceil nd/2\rceil$ and the residual floor plus (1)'s deletion cost, then minimize over $d$. The order bounds alone give $f(3,35)\ge208$ by this recursion. With the 48-vertex input, the only possible minimum degree at $(5,61)$ with at most 408 edges is thirteen. Indeed $d\le11$ leaves at least 49 nonneighbors and $d=12$ costs at least $78+20$ above the 312 residual edges. The degree sum excludes $d\ge14$.

## 2. Five private cliques and their colored cuts

Assume a set $W$ of type $(5,61)$ has at most 408 edges. Write $q(v)=d(v)-13$. All $q$ are nonnegative and $E=\sum q\le 2\cdot408-61\cdot13=23$. Any nontarget pair $y,z$ has at most
$$
                    2+q(y)+q(z)                                  \tag{2}
$$
common target neighbors. Its common nonneighbors have independence at most three and hence order at most 35. Inclusion-exclusion gives (2).

At least 50 vertices have $q\le1$, since each with $q\ge2$ spends two units. By $N(4)\le48$, choose five independent roots among these, minimizing their total weight $k$ among such choices. Write $a_i=q(x_i)\in\{0,1\}$. The root $x_i$ and all points adjacent only to it among the roots form a private clique $Q_i$. Two nonadjacent private neighbors would replace $x_i$ and give six independent vertices. Every member of $Q_i$ has weight at least $a_i$ by root replacement. Put $\ell_i=|Q_i|=11-b_i$, $B=\sum b_i$. Each of the $6+B$ exterior vertices hits $j_y\ge2$ roots. Root $i$ meets $3+b_i+a_i$ exterior vertices. Therefore
$$
 \sum_y(j_y-2)=3+k-B,\qquad B\le3+k,\qquad
 \#\{y:j_y=2\}\ge3+2B-k.                                        \tag{3}
$$
Call vertices meeting exactly two roots ordinary. The private rows already spend at least $11k-B\ge10k-3$ units of excess. Thus $k\le2,\ B\le5$.

Let an ordinary vertex $y$ meet roots $i,j$ and miss $p,t$ points of their respective rows. The two missed lists are completely target-joined. A nontarget pair across the lists, $y$, and the other three roots would be independent. Their union thus gives $p+t\le11$. If $C_{ij}$ is the actual number of target edges across the rows, then
$$
 pt\le C_{ij}\le 11+b_i b_j,\qquad
 C_{ij}\le b_i b_j+p+t.                                         \tag{4}
$$
For the first upper bound each other color needs at least $\ell_i+\ell_j-12$ edges on the union of the rows. All lie across the cut. After adding $y$, each needs one more edge, and only $p+t$ new nontarget edges are available. Subtracting these eleven requirements gives the second upper bound. The first upper bound holds for any pair of rows.

Assign $y$ to the incident row where it misses fewer points, breaking ties arbitrarily. Its assigned miss count $p$ is at most three. Indeed $(p-1)(t-1)\le1+b_i b_j\le7$ by (4) and $B\le5$. Two lists of length at least four violate this. Joining an eleven-point row completely would create a target $K_{12}$.

## 3. The 91 row profiles

The following finite inequality uses only (2)–(4) and the eleven other colors. For a candidate assigned row of size $\ell=11-b$, let $D$ be its total $q$. Its root has weight $a$, so $\ell a\le D\le23$. For each $p=1,2,3$ try every other row with deficit $c$ and every integer $p\le t<11-c$ satisfying $p+t\le11,\ pt\le bc+p+t$. An empty list of choices forbids $p$. Otherwise the assigned vertex costs at least
$$
 \max\left(0,\ \min_{c,t}[\ell+11-c-p-t-13],\
              \ell-p-2-a-\left\lfloor\frac{D-\ell a}{p}\right\rfloor\right).         \tag{5}
$$
The first expression inside the minimum counts the target neighbors in the two rows. For the last term, every missed point has the $\ell-p$ hits as common neighbors with the assigned vertex. By (2) all $p$ misses have weight at least $\ell-p-2-q(y)$. The row can spend at most $D-\ell a$ above its baseline. Full joins ($p=0$) are permitted only for $b>0$.

Enumerate the nondecreasing lists of misses on the row. Their length is at most $3+b+a$ by the root degree. For the $z$ smallest misses we need
$$
             p_1+\cdots+p_z+\binom z2\ \ge\ 11(z-b-1).            \tag{6}
$$
Each other color needs at least $z-b-1$ edges on the row and those $z$ vertices. Only their misses into the row and their mutual pairs are available. Among $g$ full joins, at most $b$ can have weight less than $\lceil(\ell-2)/2\rceil$. Any two below that threshold are target-adjacent by (2) because they share the entire row. Thus full joins cost at least $(g-b)_+\lceil(\ell-2)/2\rceil$.

Charge the row its $D$, the cost (5) of each positive miss count, and this full-join bound. Each ordinary vertex is charged on just one row. Minimize over their numbers on the five rows, subject to at least $3+2B-k$ assignments. The table gives the minimum charge in this relaxation by $k,B$, over profiles with $\sum\ell_i a_i\le23$. The five pairs $(b_i,a_i)$ are sorted only to remove permutations.

| Root weight $k$ | $B=0$ | $B=1$ | $B=2$ | $B=3$ | $B=4$ | $B=5$ | Profiles |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 21 | 25 | 29 | 28 | | | 7 |
| 1 | 24 | 28 | 31 | 28 | 24 | | 26 |
| 2 | 28 | 31 | 34 | 31 | 27 | 29 | 58 |

Ninety profiles exceed 23. Only $k=B=0$ remains. The second implementation instead splits a budget of 23 among the rows and maximizes how many ordinary vertices the rows can accept. It tests 434 choices with the roots of each weight labelled. Only the same profile survives, with capacity three. [Minimum-charge verifier](verify_order_twelve.py) · [Maximum-count verifier](replay_order_twelve.py)

## 4. Six exterior vertices and five cliques

All five rows now have eleven vertices. Two exterior vertices cannot both miss at most four points of the same row. That row and the two vertices would form a thirteen-set with at most $4+4+1=9$ edges available for the eleven nontarget colors.

In this profile an ordinary vertex misses one or two points of its assigned row, by (4) with $b_i=b_j=0$. Consequently distinct ordinary vertices are assigned to distinct rows. Charge each its own weight and the weights of its missed points on the assigned row. These charges are disjoint. With $p$ misses the charge is at least $q(y)+p\max(0,11-p-2-q(y))$, by (2). This is at least eight for $p=1$ and at least seven for $p=2$. Four ordinary vertices would spend at least 28. By (3) there are exactly three. The other three exterior vertices must each meet exactly three roots, since $\sum(j_y-2)=3$.

The three charges spend at least 21 of the 23 units. Each of the other exterior vertices therefore has weight at most two. In any row at most two of its points were charged, and the uncharged points in the entire graph have at most two units left. Every row thus contains at most four positive-weight points.

Take a vertex $y$ meeting three roots. If it missed at least five points in each incident row, each missed list would contain a weight-zero point. Applying (2) to that point and $y$ gives at most four hits in the row, so each missed list actually has at least seven members. Choose one uniformly and independently from each list. Each pair of rows has at most eleven target edges by (4), so the probability of any target pair is at most $33/49<1$. Some choice avoids the target. The three representatives, $y$, and the two unhit roots then give six independent vertices.

Hence each of the six exterior vertices misses at most four points of some row. No two can use the same row, and there are only five. This contradiction proves $f(5,61)\ge409$.

## 5. Edge bounds on 47 and 59 vertices

Two smaller bounds are needed. For $(4,47)$ under a cap of 282, minimum degree below eleven contradicts $N(3)$. Degree eleven leaves 35 vertices and costs at least $66+11$ by (1), giving at least $208+77=285$. The degree sum now forces twelve-regularity. For $(5,59)$ under a cap of 357, degree at most nine leaves more than 48 vertices. Degree ten costs at least $55+312$, and degree eleven costs at least $66+11+283=360$ once the 47-vertex bound is proved. A higher minimum degree than twelve exceeds the cap.

Handle these two cases in that order, now with $q=d-12$. There are zero units of excess at 47 and at most six at 59. In each case choose $s$ independent weight-zero roots. At 47 use $47>N(3)$. At 59 at least 53 vertices have weight zero, more than $N(4)$. Inequality (2) again holds, by $N(2)\le23$ at 47 and $N(3)\le35$ at 59. There are $s-1+B$ exterior vertices and $\sum(j_y-2)=2-B$, since now $n=12s-1$ and the root degree is twelve. Thus $B\le2$ and at least $s-3+2B$ vertices are ordinary. The same missed-list argument and (4) apply.

At 47, an ordinary vertex that misses any point of a row hits at most two of that row, by (2). Missing points in both incident rows would give at least seven misses per row, contradicting (4). Assign each ordinary vertex to a row it joins completely. All vertices assigned to the same row form a clique with it by (2), so at most $B$ can be assigned. At least $1+2B$ were required. This proves $f(4,47)\ge283$.

At 59, temporarily discard points of weight above $T$, where $T=2$ for $B\ge1$ and $T=3$ for $B=0$. Each remaining row has more than $2+2T$ points. For $B\ge1$, an ordinary vertex hitting at most six points of each incident row would have $pt\ge(5-b_i)(5-b_j)\ge15+b_i b_j$, contradicting (4). For $B=0$, at most eight hits on both sides would give $p,t\ge3$, violating $pt\le p+t$. Thus an ordinary vertex of weight at most $T$ hits more than $2+2T$ original points of some row. By (2) it joins every retained point there. Its assigned companions are mutually adjacent by (2). Capacity is at most $B$ plus the number discarded from the rows. Adding back the high-weight ordinary vertices gives at most $B+\lfloor6/(T+1)\rfloor$ ordinary vertices in all, strictly below $2+2B$. This proves $f(5,59)\ge358$.

## 6. The global coloring

In a balanced $K_{145}$, the sparsest color has at most $\binom{145}{2}/12=870$ edges. By Proposition 7 it has a vertex of minimum degree $11-t$ with $0\le t\le11$. Indeed, otherwise it is twelve-regular and Brooks' theorem gives a proper twelve-coloring of its target graph, hence an independent thirteen-set. No component can be a target $K_{13}$. Delete the closed neighborhood and repeatedly remove target $K_{12}$'s until none remain. Removing a full clique lowers the independence bound by one because every exterior vertex has at most one target neighbor on the clique. Every target-independent set of at most eleven vertices outside can therefore extend into it.

This leaves a set of order $n+t$, $n=12s+1,\ 1\le s\le11$, with independence at most $s$ and no target $K_{12}$. The first deletion costs at least $\binom{12-t}{2}$, and each of the $11-s$ subsequent deletions costs at least 66. Sampling $n$ vertices therefore gives a set of type $(s,n)$ under the cap $870-66(12-s)$. Explicitly, the checker compares
$$
 \left[870-\binom{12-t}{2}-66(11-s)\right]\binom n2
 \ \le\ [870-66(12-s)]\binom{n+t}{2}
$$
at all 132 choices. [Outer reduction, Section 6](overfull-core.md#6-a-reduction-to-local-statements-for-any-hue)

The first four stops exceed the known order bounds. The remaining comparisons from (1), with floors at $(4,48),(4,47),(5,59),(5,61)$, are as follows.

| Vertices | 61 | 73 | 85 | 97 | 109 | 121 | 133 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Target edge floor | 409 | 475 | 541 | 608 | 675 | 742 | 809 |
| Global cap | 408 | 474 | 540 | 606 | 672 | 738 | 804 |

With just the 48- and 61-vertex inputs, the same recurrence gives 474, 539 and 606 at the three later stops in question. The 47- and 59-vertex improvements supply the strict inequalities. All eleven stops are excluded, proving the theorem.

**Reproduction.** Run the following from the directory containing the scripts with Python 3.10 or newer. The four-row verifier reads the existing certificate files alongside it. The two order-twelve scripts use the standard library and import no code from one another.

```sh
python3 -B verify_four_row_descent.py 12
python3 -B verify_order_twelve.py
python3 -B replay_order_twelve.py
```
