# The five-row stop at order eleven and the odd midpoint

Robert Sneiderman’s research notes · 24 November 2026

**Theorem 1.** Every eleven-coloring of the edges of $K_{122}$ has twelve vertices missing a color. The new step is a lower bound of 342 edges at the 56-vertex stop. The shortest proof of that bound uses the degree reduction in Section 2 and 77 cases in Section 5. Section 3 then treats all ten stops. Terpstra Research publicly claimed this fixed order in August 2026. Both our four-row prerequisites and our new argument await external mathematical review. [Earlier public release](https://github.com/terpstra-research/erdos-617-r10-r11/releases/tag/v0.1.1) · [77-case replay](verify_midpoint_row_budgets.py)

## 1. Private cliques of an independent set

Call a coloring *balanced* if every $r+1$ vertices see every color. Fix a target color $a$. In this note neighbors, degrees, independence, and cliques refer to its graph unless a color is specified. Let $N(j)$ be any valid upper bound on the size of a set having independence at most $j$ and containing no $K_r$ in the target color. The discussion takes place inside a putative balanced coloring.

Suppose $W$ has $sr+1$ vertices, independence at most $s$, no $K_r$, and minimum degree at least $r+1$. Write $q(x)=d_W(x)-(r+1)$, $E=\sum_Wq$. If $E\le r-1$ and $N(s-1)\le(s-1)r$, at least $(s-1)r+2$ vertices have $q=0$. Among them choose an independent $s$-set $I=\{x_i\}$. For a nontarget pair $y,z$, their common target nonneighbors have independence at most $s-2$. Thus
$$
 |N_a(y)\cap N_a(z)|\le C+q(y)+q(z),\qquad
 C=\begin{cases}
 2 &\text{if }N(s-2)\le(s-2)r-1,\\
 3 &\text{if }N(s-2)\le(s-2)r .
 \end{cases}                                                     \tag{1}
$$
Indeed their common nonneighbors in $W\setminus\{y,z\}$ number $sr-1-d_W(y)-d_W(z)+|N_a(y)\cap N_a(z)|$.

The root $x_i$ and all vertices adjacent to it alone among the roots form a clique $Q_i$. Two nonadjacent private neighbors could replace $x_i$, contradicting independence at most $s$. Put $|Q_i|=r-1-b_i$, $B=\sum b_i$. The $s+1+B$ vertices outside these rows each meet $j_y\ge2$ roots. The sum of the root degrees is $s(r+1)$, so
$$
 \sum_y(j_y-2)=s-2-B,\qquad B\le s-2 .
$$
At least $3+2B$ exterior vertices therefore meet exactly two roots. Call them ordinary.

For an ordinary $y$ at roots $i,j$, let $p_i,p_j$ count its missed vertices in $Q_i,Q_j$, and $h_i=|Q_i|-p_i$, $h_j=|Q_j|-p_j$. Every edge between the two missed lists has target color. Otherwise $y$, a nontarget pair across the lists and the other $s-2$ roots give $s+1$ independent points. For $w$ missed in $Q_i$, the pairs $wy$ and $wx_j$ are nontarget. They have at least $h_i$ and $p_j$ common target neighbors respectively, the latter from the opposite list. By (1),
$$
 q(w)\ge L_i=\max(0,h_i-C-q(y),p_j-C).                         \tag{2}
$$
The same formula holds with $i,j$ interchanged. Every pair of roots supports at most $C$ ordinary vertices by (1).

## 2. The 56 vertices

Now let $r=11$, $s=5$. The project's two- and three-row theorems and $P(4)$ give $N(1)\le10,\ N(2)\le21,\ N(3)\le32,\ N(4)\le44$. [Order bounds, Sections 6 and 8](overfull-core.md)

**The 44-vertex input.** On an admissible 44-set of independence at most four, every degree is at least eleven, by $N(3)\le32$. The order-eleven four-row certificates exclude every case in which an independent quartet has total excess above degree eleven at most three. Section 2 of that same proof shows that either such a quartet exists or some other hue partitions the set into eleven independent quartets for the target. In the latter case the degree sum is at least $44\cdot11+11\cdot4=528$. Thus at least **264 target edges** are required. [Four-row argument and census, Sections 2 and 6](four-row-descent.md) · [Prerequisite replay](verify_four_row_descent.py)

Suppose an admissible 56-set of independence at most five has at most 341 edges. A vertex of degree at most ten leaves at least 45 nonneighbors, contrary to $N(4)\le44$. If a minimum-degree vertex has degree eleven, it leaves 44 nonneighbors. In the general form of Lemma 22 of the order-ten note, the hitting number of the independent four-sets there is at least $44-N(3)\ge12$. The deletion costs at least $\binom{12}{2}+\max(10,2\cdot12-6)=84$ edges, giving at least $264+84=348$. To recall the premium, the eleven neighbors contain at least ten nontarget pairs, and these cannot form a star since that would leave a target eleven-clique with the root. Two disjoint such pairs each have target neighborhoods meeting every independent four-set of the residual. Only the six pairs on their four endpoints can be counted twice in their internal degrees. [Deletion identity and proof, Section 12](overfull-core.md#12-order-ten)

The minimum degree must therefore be twelve. Now $E=2e_a(W)-56\cdot12\le10$, and (1) holds with $C=2$. In the notation of Section 1, $B\le3$. Let $D_i=\sum_{w\in Q_i}q(w)$ and retain the vertices of each row with $q\le4$. There are at least $10-b_i-\lfloor D_i/5\rfloor$ retained vertices in row $i$.

Use a bound $g$ on the excess of an exterior vertex. A row is usable if its retained lower bound exceeds $2+2g$. Assign an ordinary vertex $y$ with $q(y)\le g$ to a usable incident row if it joins every retained member there. Assign it to just one if it qualifies twice. All vertices assigned to a given row form a clique together with its retained members, by (1). Thus usable row $i$ can take at most $b_i+\lfloor D_i/5\rfloor$ vertices. For purposes of the check, recognize eligibility whenever $p_i=0$ or $L_i>4$ in (2). Recognizing fewer eligible vertices only weakens the test, since the model then allows them to be unassigned.

For reproducibility the entire finite exclusion is as follows.

1. Sort the five $b_i$, and sort $D_i$ within equal $b_i$. Enumerate nonnegative integers with $B\le3,\ \sum D_i\le10$.
2. For each pair $i,j$ compute a lower bound on the excess of an unassigned ordinary vertex there. Enumerate $0\le q\le10,\ 0\le p_i<10-b_i,\ 0\le p_j<10-b_j$. A row of size ten cannot be fully joined. Keep only $p_iL_i\le D_i,\ p_jL_j\le D_j$, as required by (2). If $q\le g$ and either row recognizes the vertex, omit this possibility from the unassigned list. Use the least remaining $q$, or the lower bound eleven when the list is empty.
3. Subtract the total usable-row capacity from $3+2B$, replacing a negative result by zero. At least this many ordinary vertices are unassigned. By (1) at most two use any root pair. Take two copies of each pair's lower bound and sum the required number of smallest entries. Adding $\sum D_i$ gives a lower bound on $E$.

There are 2,903 budget profiles. At $g=2$ the bound exceeds ten for 2,900. The other three all give ten. At $g=0$ their respective lower bounds are as follows.

| Row deficits $b$ | Row excess totals $D$ | Required $E$ |
| --- | --- | ---: |
| $0,0,0,0,2$ | $0,0,0,0,10$ | 13 |
| $0,0,0,0,3$ | $0,0,0,5,5$ | 14 |
| $0,0,0,1,2$ | $0,0,0,0,10$ | 14 |

This proves the lower bound of 342 on 56 vertices. A second implementation enumerates all 21,021 labelled allocations, including every permutation of budgets on equal rows, and maximizes the possible number of unassigned vertices under the exterior budget. Six labelled allocations require the second bound. Its forward recursion also reproduces the six lower bounds in Section 3. These are internal computational checks. [Labelled replay](replay_midpoint_rows.py)

## 3. All ten stops at order eleven

Proposition 7 applied to a least hue starts with at most $\binom{122}{2}/11=671$ edges. Remove the closed neighborhood of a minimum-degree vertex of degree $10-t$ and then $10-s$ full cliques, or stop without removing a clique at $s=10$. The remainder has $n+t$ vertices, $n=11s+1$, independence at most $s$, no target eleven-clique and at most $671-\binom{11-t}{2}-55(10-s)$ edges. Sampling $n$ vertices gives at most $671-55(11-s)$ target edges. The checker verifies this comparison at all $110$ choices of $s,t$. [Outer reduction, Section 6](overfull-core.md#6-a-reduction-to-local-statements-for-any-hue)

For $s\le4$ the order bounds exclude such a set. For $s\ge5$ the budget-first deletion replay uses the new floors at $(4,44)$ and $(5,56)$. If the minimum degree is $d$, the remaining type is $(s-1,n-1-d)$, with $\tau=\max(0,n-1-d-N(s-2))$ if that bound is known and zero otherwise. The cost is $\binom{d+1}{2}$ plus zero for $d\le9$, $\max(1,\tau-1)$ for $d=10$, $\max(10,2\tau-6)$ for $d=11$, and $10(d-10)$ for $d\ge12$. These are the arguments of Lemma 22, with the eleven-color parameters. At higher degrees each of the ten other hues needs at least $d-10$ edges on the closed neighborhood by the vertex-cover bound. At each recursion discard degrees with $nd>2\,\mathrm{budget}$. Both replays use only the order bounds, the deletion costs and the two new floors.

| Vertices | 56 | 67 | 78 | 89 | 100 | 111 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Lower bound | 342 | 401 | 454 | 510 | 566 | 622 |
| Outer cap | 341 | 396 | 451 | 506 | 561 | 616 |

Every possible stop is excluded, which proves Theorem 1.

## 4. The odd midpoint

**Theorem 2.** Write $r=2s+1$, $r\ge13$. Assume $N(s-1)\le(s-1)r,\ N(s-2)\le(s-2)r$. A set $W$ on $sr+1$ vertices of minimum target degree at least $r+1$, independence at most $s$, and no target $K_r$ exceeds the outer stop's edge cap $r(sr+1+r-s)/2$. At $r=11$ the same conclusion follows using the known stronger bound $N(3)\le32$. For example, $M(s-1)$ guarantees the minimum-degree condition as well as the first order bound.

Under the cap we have $E\le r(r-2s)-1=r-1$, so Section 1 applies. Choose an integer $T\ge0$ and set $H=\lfloor(r-1)/(T+1)\rfloor,\ A=r-1-C-2T$. It suffices that
$$
 H\le B+2,\qquad r-1-B-H>C+2T,\qquad A>B,\qquad A(A-B)>r-1.    \tag{3}
$$
At most $H$ vertices of $W$ have $q>T$. Delete those vertices temporarily from the private rows. Every surviving row has more than $C+2T$ members.

The actual labels between rows give at most $r-1+b_i b_j$ target edges across $Q_i,Q_j$. Indeed every other hue needs at least $|Q_i|+|Q_j|-r$ edges on their union, all crossing, and subtraction gives the bound. Thus $p_i p_j\le r-1+b_i b_j$. If both $h_i,h_j\le C+2T$, the missed-list product is at least $(A-b_i)(A-b_j)\ge b_i b_j+A(A-B)$, impossible by (3). So an ordinary vertex with $q\le T$ has some $h_i>C+2T$. By (2) it joins the whole surviving row $i$. Assign it there. All points assigned to this row form a target clique with its surviving members by (1). The total capacity is $B$ plus the number of high vertices deleted from the private rows. The high ordinary vertices are outside those rows. Counting both gives at most $B+H$ ordinary vertices of any excess, against the required $3+2B$.

For odd $r\ge101$, take $T=\lfloor(r-1)/3\rfloor$ if $B\le5$, and $T=\lfloor(r-1)/8\rfloor$ otherwise. In the first case $H\le2$, the second inequality follows from $r-8>3+2(r-1)/3$, and $A\ge(r-1)/3-3\ge r/4,\ A-B\ge5$. In the second case $H\le7,\ B\le(r-5)/2$. Now $r-1-B-H\ge(r-11)/2>3+(r-1)/4$, and $A\ge3(r-1)/4-3,\ A-B\ge(r-5)/4$. Both choices satisfy (3). At odd orders 31 through 99 the first checker tests every $B\le s-2$ and finds a threshold for each. Section 5 gives the remaining finite cases. [Uniform threshold replay](verify_midpoint_excess.py)

## 5. Charging the edges between two rows

Put $Q=r-1$. Let $D$ be the sum of $q$ on all private rows. Thus $0\le D\le Q$. For each ordinary vertex on rows $i,j$, the union of its two missed lists is a clique. Its target neighbors in the two rows are distinct. These facts and the colored cut in Section 4 give
$$
 p_i+p_j\le Q,\qquad p_i p_j\le Q+b_i b_j,\qquad h_i+h_j\le r+1+q(y).
$$
Both missed lists belong to the private rows. By (2) they require $p_iL_i+p_jL_j\le D$. The exterior vertex $y$ spends its own $q(y)$ outside the rows. Thus also $q(y)+p_iL_i+p_jL_j\le Q$. These inequalities charge the two lists of **one** vertex together. Distinct exterior vertices can miss the same row members, so we count only their own excesses when combining vertices.

Fix cutoffs $T,g$. The rows together contain at most $H_D=\lfloor D/(T+1)\rfloor$ vertices of excess above $T$. Use a row when $Q-b_i-H_D>C+2g$. Assign an ordinary vertex of excess at most $g$ to one usable incident row whenever $p_i=0$ or $L_i>T$. It then joins every retained point there. As in Section 2, the assigned vertices and the retained row form a clique. Summing the capacities once per row gives at most $H_D+\sum_{i\ {\rm usable}}b_i$ assignments. Every other ordinary vertex is counted on its root pair, each pair at most $C$ times.

For each pair enumerate $0\le q(y)\le Q,\ 0\le p_i<Q-b_i,\ 0\le p_j<Q-b_j$ under the displayed bounds and both excess bounds. Joining a row of size $Q$ completely would create a target $K_r$, so exclude that choice. The least $q(y)$ for an unassigned vertex is a lower bound for its cost, with $Q+1$ used when no choice survives. Subtract the assignment capacity from $3+2B$ to get the required number of unassigned vertices. Take the cheapest such costs, up to $C$ copies per pair. A total cost above $Q-D$, or insufficient pairs, excludes this budget.

The replay enumerates every partition of $B\le s-2$ padded to $s$ rows, and every integer $D\in[0,Q]$. It tries $T=\lfloor r/3\rfloor+1,\lfloor r/3\rfloor$ and $0\le g\le\lfloor r/4\rfloor$. At $r=11$ it uses $C=2$, and at every other listed order it uses $C=3$. Each budget is excluded by at least one choice. [Exact finite replay](verify_midpoint_row_budgets.py)

| $r$ | 11 | 13 | 15 | 17 | 19 | 21 | 23 | 25 | 27 | 29 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Budgets | 77 | 156 | 285 | 510 | 855 | 1,407 | 2,231 | 3,475 | 5,265 | 7,888 |

This completes Theorem 2. At eleven these 77 budgets give a shorter alternative to the 2,903-profile step in Section 2. The small-order calculation still uses $N(3)\le32,\ N(4)\le44$, and the separate argument excluding minimum degree below twelve.

The order bounds assumed in Theorem 2 are open in the general middle range. The theorem excludes one stop under those hypotheses. The unrestricted large-order result is recorded in the [research handoff](../README.md).
