# The overfull core of a sparsest hue in Erdős 617

Robert Sneiderman research project · Private proof supplement · 23 November 2026

**The open step of the grid supplement is still open.** This note continues §§4–5 of [the grid supplement](grid-obstruction.md). A normalized sparsest hue has at most $r-4$ full cliques for $r\ge7$ and at most $r-5$ for $r\ge11$. The conjecture at each order reduces to $r-2$ local statements. The first four now follow for $r\ge11$, using the three-row theorem in Section 8. The note also gives a condition that forces at least three full cliques and records solver results at orders three and four. Independent mathematical review is pending.

**Setting.** Let $r\ge5$ and suppose a balanced coloring of $K_{r^2+1}$ exists. Normalize it as in §4 of the grid supplement and let $a$ be a nonreserve hue with $e_a\le r(r^2+1)/2$. Every $a$-edge is critical and every $a$-clique of size $r$ (a *full clique*) is an isolated component of $a$. Let $k$ be the number of full cliques, $U$ the set of all other vertices, and $h=r-k$. Then
$$
 |U|=hr+1,\qquad \alpha_a(U)=h,\qquad U\ \text{contains no $a$-clique of size } r .
$$
Indeed $a$ has an edge and every $a$-edge is critical, so $\alpha_a=r$ exactly. Independence is additive over components and each full clique contributes one, so $\alpha_a(U)=r-k$. Call $U$ the **core**. All $a$-degrees below are degrees inside $U$, which are the full degrees. The conjecture holds if no core exists. In a balanced coloring a second demand on an edge is the same thing as an $(r+1)$-set missing a hue, so the question "can another hue force a second demand on an edge of the overfull component" is exactly the question whether a core can exist.

* **At most $r-4$ full cliques.** For $r\ge7$, every set of $3r+1$ vertices whose $a$-independence number is at most three contains a full clique. Hence $h\ge4$. The grid supplement had $h\ge3$.
* **Every maximum independent set of the core is heavy.** Its $a$-degrees sum to at least $hr+2$. Consequently at least $r+1$ core vertices have $a$-degree at least $r+1$.
* **At most $r-5$ full cliques for $r\ge11$.** At $h=4$ every core vertex has $a$-degree at least $r$ and $2r^2+r+1\le e_a(U)\le 2r^2+r+7$. An exact minimum in another hue yields $r-2$ disjoint maximum independent sets whose degree sum excludes $h=4$ once $r\ge19$. Theorem 10 extends the conclusion to $r\ge11$.
* **The conjecture reduces to $r-2$ local statements.** Let $P(s)$ say that no balanced coloring has a hue $a$ and a set of $sr+1$ vertices with $a$-independence at most $s$ and no $a$-clique of size $r$. If $P(1),\dots,P(r-2)$ hold at order $r$, the conjecture holds at order $r$. No normalization is needed. $P(1),P(2)$ always hold, $P(3)$ holds for $r\ge7$ and $P(4)$ for $r\ge11$. The fixed-case proofs for $r=5,6$ are this scheme with one hue and an edge budget.
* **One inequality would give three full cliques.** If the core has mean $a$-degree at least $r+2/h$, then $k\ge3$, and $h\ge5$ once $r\ge14$. That inequality holds whenever the maximum independent sets of the core cover it with equal loads. In general it is a special case of a degree and clique-size bound which a literature search found proved only for maximum degree four.

## 1. Counting on a set with no full clique

Write $B(t)=\binom t2$ and let $p_s(n)$ be the least number of edges of a graph on $n$ vertices with independence number at most $s$. For $n=sq+x$ with $0\le x\le s$ it equals $sB(q)+xq$.

**Lemma 1.** Let $W$ be a vertex set containing no full clique, with $\alpha_a(W)\le s$ and $|W|=sr+x$, where $s\ge2$ and $1\le x\le s$. Then
$$
 \frac{s\,(r(s-3)+2)}{2}\;-\;x(r-s)\;+\;B(x)\;-\;[x=s]\ \ \ge\ 0 .                \tag{1}
$$

*Proof.* The $a$-cliques in $W$ have at most $r-1$ vertices, so $s$ of them cannot cover $W$. The complement of $a$ on $W$ is $K_{s+1}$-free and is not $s$-partite. Brouwer's theorem gives $e_a(W)\ge p_s(|W|)+\lfloor|W|/s\rfloor-1$. For any other hue $c$, a $c$-clique inside $W$ is $a$-independent and has at most $s$ vertices, so $r$ of them cannot cover $W$ either. Since $\alpha_c(W)\le r$, the same theorem gives $e_c(W)\ge p_r(|W|)+\lfloor|W|/r\rfloor-1$. Both applications satisfy the size hypotheses $|W|\ge2s+1$ and $|W|\ge2r+1$. The $r$ lower bounds sum to at most $B(|W|)$. Since $|W|\le r^2+1$ we have $s\le r$ and $x\le r-1$, so $\lfloor|W|/r\rfloor=s$. Substituting $p_s(sr+x)=sB(r)+xr$ and $p_r(sr+x)=rB(s)+xs$ and simplifying gives (1). ∎ [Brouwer, Theorem 2](https://ir.cwi.nl/pub/6791/6791D.pdf)

The left side of (1) is $4-2r$ at $(s,x)=(2,1)$, which is the case of §5 of the grid supplement. It is $6-r$ at $(3,1)$, and $r+8,\ 13,\ 19-r,\ 25-2r$ at $s=4$, $x=1,2,3,4$. For $s\ge5$ it is positive for every $x\le s$. The lemma passes to subsets, so a negative value at $(s,x)$ excludes every larger set with the same independence bound.

**Corollary 1.** Let $r\ge7$. (a) No set of $3r+1$ vertices with $\alpha_a\le3$ avoids all full cliques. (b) The core has $h\ge4$. (c) If $h=4$, every core vertex has $a$-degree at least $r$. (d) If $h=5$ and $r\ge20$, every core vertex has $a$-degree at least $r-2$.

*Proof.* (a) is (1) at $(3,1)$. For (b), $h=1$ would make $U$ a clique on $r+1$ vertices, and $h=2,3$ are excluded by (1). For (c) and (d) take a core vertex $u$ of degree $d$. The set $U\setminus N_a[u]$ has $hr-d$ vertices, no full clique, and independence number at most $h-1$, since $u$ extends any independent set in it. At $h=4$ part (a) gives $4r-d\le3r$. At $h=5$ the value $19-r$ at $(4,3)$ gives $5r-d\le4r+2$. ∎

For $r\ge7$ the same deletion applied to an independent set $J\subset U$ of size $h-3$ shows $|N_a[J]|\ge(h-3)r+1$: independent sets of the core expand by more than $r$ per vertex, which a union of cliques never does.

## 2. Heavy independent sets

**Lemma 2.** Let $I\subset U$ be $a$-independent with $|I|=h$. Then $\sum_{v\in I}d_a(v)\ge hr+2$.

*Proof.* Every vertex of $U\setminus I$ has a neighbor in $I$. Let $P(v)$ be the set of vertices whose only neighbor in $I$ is $v$. Two nonadjacent members of $P(v)$ could replace $v$, so $P(v)\cup\{v\}$ is a clique and $|P(v)|\le r-2$. At least $hr+1-h-h(r-2)=h+1$ vertices of $U\setminus I$ therefore have two or more neighbors in $I$. Counting edges from $I$ gives $(hr+1-h)+(h+1)$. ∎

This is Fajtlowicz's count behind $\alpha\ge2n/(\Delta+\omega+1)$, applied to one independent set. The mean degree on every maximum independent set of the core is at least $r+2/h$, while a union of cliques would give $r-1$.

**Corollary 2.** At least $r+1$ core vertices have $a$-degree at least $r+1$.

*Proof.* Let $W_0$ be the set of core vertices of degree at most $r$. An independent $h$-set inside $W_0$ would have degree sum at most $hr$. So $\alpha_a(W_0)\le h-1$. The graph on $W_0$ has maximum degree at most $r$ and no clique of size $r+1$. Color each component separately: one of maximum degree $r$ is neither $K_{r+1}$ nor an odd cycle, so Brooks' theorem gives $r$ colors, and one of smaller maximum degree is colored greedily with at most $r$. Hence $|W_0|\le r(h-1)$. ∎

**Corollary 3 (the case $h=4$).** Let $r\ge7$ and $h=4$. Then $2r^2+r+1\le e_a(U)\le2r^2+r+7$. The degrees above $r$ sum to at most $r+14$ over the whole core and occur at no fewer than $r+1$ vertices.

*Proof.* By Corollary 1(c) all degrees are at least $r$, and by Corollary 2 the degree sum is at least $(4r+1)r+r+1$. In the other direction each of the $r-1$ other hues needs $p_r(4r+1)+3=6r+7$ edges inside $U$, as in Lemma 1, leaving at most $B(4r+1)-(r-1)(6r+7)=2r^2+r+7$ for $a$. ∎

So a core with $h=4$ is an almost $r$-regular graph on $4r+1$ vertices with independence number four and no clique of size $r$, with between $r+1$ and $r+14$ vertices of larger degree, nearly all of degree exactly $r+1$. The vertices of degree exactly $r$ span no independent four-set, so they number between $3r-13$ and $3r$ and have independence number at most three. This is the smallest surviving case and the most rigid one.

**Corollary 4 (cliques of other hues).** Every monochromatic $r$-clique $Q$ of another hue $c$ meets each full $a$-clique in exactly one vertex and meets $U$ in exactly $h$ vertices, which form a maximum $a$-independent set $J$ of the core. Every core vertex outside $J$ has one or two $a$-neighbors in $J$.

*Proof.* If $Q$ missed a full clique $C$, each $x\in C$ would need an $a$-edge into $Q$, and no $a$-edge leaves $C$. A common vertex set of an $a$-clique and a $c$-clique has at most one point. For a core vertex $y\notin Q$, the $r$ edges to $Q$ contain at most one of hue $c$ and all $r-2$ hues other than $a,c$, so at most two have hue $a$, and at least one does because $J$ is maximal. ∎

## 3. From heavy sets to a mean degree

**Lemma 3.** Give nonnegative weights to $a$-independent $h$-subsets of $U$ and let $L(v)$ be the total weight of the sets through $v$. Then
$$
 \sum_{v\in U}L(v)\,\bigl(d_a(v)-r-2/h\bigr)\ \ge\ 0 .                              \tag{2}
$$
If the loads $L(v)$ are equal and positive, then $e_a(U)\ge(hr+1)(hr+2)/(2h)$.

*Proof.* Multiply Lemma 2 by the weight of each set and add. The loads sum to $h$ times the total weight. ∎

**Hypothesis A.** The mean $a$-degree of the core is at least $r+2/h$.

By Lemma 3, Hypothesis A holds whenever the all-ones vector of $U$ is a nonnegative combination of indicators of maximum independent sets, that is, whenever the fractional chromatic number of the core equals $(hr+1)/h$. The $h$-cliques of the other hues inside $U$ are maximum independent sets of the core and are the natural source of such a family. The September fractional packings of monochromatic cliques are families of this kind in the September setting, with load at most one per hue. Inequality (2) is the form in which such packings would bound the degrees of the target hue. Lemma 1 uses only balance and holds for any hue of any balanced coloring.

**Proposition (conditional).** Assume Hypothesis A. Then $k\ge3$. Moreover $h=3$ is impossible for every $r\ge5$ and $h=4$ is impossible for $r\ge14$. In particular the conjecture follows for $r=5$ and $r=6$ from Hypothesis A and the bound $k\le r-3$ of the grid supplement.

*Proof.* The hue has $kB(r)+e_a(U)\ge kB(r)+(hr+1)(hr+2)/(2h)$ edges. Comparing with $r(r^2+1)/2$ gives $h+2+2/(hr)\le r$. At $h=r-2$ the margin is $1/h$ of an edge, so the exact form of Hypothesis A matters for the third clique. For the second claim repeat the count of Lemma 1 on $U$ with this lower bound for $a$. The remaining capacity is $r(h^2-4h-1)/2+2h-1-1/h$. ∎

**What is known about Hypothesis A.** It would follow from the inequality $\alpha(G)\ge\sum_v 2/(d(v)+\omega(v)+1)$, where $\omega(v)$ is the largest clique through $v$, by convexity. A literature search found that inequality proved only for graphs of maximum degree at most four. The search read listings and later citations of the paper and did not read the paper, so confirm its scope before citing. [Brause, Randerath, Rautenbach, Schiermeyer](https://doi.org/10.1016/j.dam.2015.06.009) The published Kelly–Postle bound $\alpha\ge\sum_v1/(d(v)+1/2)$ applies to the non-complete components of the core. They have no simplicial vertex, because in a critical hue the closed neighborhood of a simplicial vertex is a whole component. On a core without complete components it gives mean degree $r-1/2+1/h$, short of Hypothesis A by $1/2+1/h$. [Kelly and Postle](https://arxiv.org/abs/2407.17363) Treat Hypothesis A as unproved.

A linear form gives almost as much. The tangent to $2/(d+r)$ at $d=r$ is $(3r-d)/(2r^2)$. Mean degree at least $r+2r/(hr+1)$ on the core, which yields $k\ge2$, excludes $h=3$, and excludes $h=4$ for $r\ge15$, follows from
$$
 \alpha(G)\ \ge\ \frac{3rn-2e(G)}{2r^2}\qquad\text{for every graph $G$ with no clique of size } r,
$$
which holds for unions of cliques, for $r$-regular graphs by Brooks, and for all graphs with $\alpha\le2$. In the last case non-neighborhoods are cliques, so every degree is at least $n-r$ and $n(n-r)-(3rn-4r^2)=(n-2r)^2\ge0$. Deleting a vertex of degree $d\ge3r/2$ changes the right side by $(2d-3r)/(2r^2)\ge0$. Deleting the closed neighborhood of a vertex of minimum degree $\delta\le r-2$ removes at least $\delta(\delta+1)/2$ edges and lowers the right side by at most one, since $2r^2-(\delta+1)(3r-\delta)\ge2$. Neither step is available when the minimum degree is $r-1$ or more and neighborhoods are nearly complete, and the inequality is unproved in general. It has no counterexample on at most nine vertices for $3\le r\le6$.

## 4. A hue at its minimum supplies disjoint heavy sets

For a hue $c\ne a$ write $\eta_c=e_c(U)-p_r(hr+1)$, its surplus on the core over the complementary Turán floor. Brouwer's theorem gives $\eta_c\ge h-1$, as in Lemma 1. Write $E_a=e_a(U)-hB(r)-r$ for the surplus of $a$. Counting all pairs of $U$ gives the identity
$$
 \sum_{c\ne a}\eta_c\;+\;E_a\;=\;rB(h)-(r-h).                                      \tag{3}
$$

**Lemma 4.** For every hue $c\ne a$, the core contains at least $r+1-\eta_c$ pairwise disjoint $c$-cliques of size $h$. Each is a maximum $a$-independent set of the core and has $a$-degree sum at least $hr+2$.

*Proof.* The pairs of $U$ not of hue $c$ form a $K_{r+1}$-free graph with $\eta_c$ fewer edges than the Turán graph. Füredi's stability theorem partitions $U$ into $r$ classes, some possibly empty, with at most $\mu\le\eta_c$ such pairs inside classes. Let class $i$ have $m_i$ of them. Deleting one endpoint of each leaves a $c$-clique, and $c$-cliques in $U$ are $a$-independent, so $|V_i|\le h+m_i$. Put $\operatorname{def}_i=h+m_i-|V_i|\ge0$. Summing sizes gives $\sum_i\operatorname{def}_i=\mu-1$. At least $r-(\mu-1)$ classes have $\operatorname{def}_i=0$, and each of those contains a $c$-clique of size exactly $h$. Lemma 2 applies to each. ∎ [Füredi's stability theorem](https://arxiv.org/abs/1501.03129)

If $\delta$ is the least $a$-degree in the core, Lemma 4 leaves $h(\eta_c-1)+1$ vertices uncovered and gives
$$
 \sum_{v\in U}\bigl(d_a(v)-r\bigr)\ \ge\ 2(r+1-\eta_c)-\bigl(h(\eta_c-1)+1\bigr)(r-\delta)_+ .   \tag{4}
$$
By (3) the least surplus is less than $rB(h)/(r-1)$. So when $h^2$ is small compared with $r$, some hue covers almost all of the core with disjoint heavy sets, and (4) turns a lower bound on $\delta$ into Hypothesis A up to an error depending only on $h$. No unproved inequality is needed there.

**Corollary 6 (the case $h=5$).** Let $r\ge50$ and $h=5$. Then $\sum_{v\in U}(d_a(v)-r)\ge2r-62$, and the other hues together have at most $2r+40$ edges on $U$ beyond their minima $10r+9$.

*Proof.* Let $\eta$ be the least surplus. Corollary 1(d) gives $\delta\ge r-2$, so (4) reads $X\ge2r+10-12\eta$ for $X=\sum_v(d_a(v)-r)$. Since $2E_a=4r+X$, identity (3) gives $(r-1)\eta\le9r+5-E_a\le6r+6\eta$, so $\eta\le6r/(r-7)<7$. With $\eta\le6$ we get $X\ge2r-62$ and $E_a\ge3r-31$, and (3) leaves $9r+5-(3r-31)-4(r-1)$. ∎

**Theorem 5.** For $r\ge19$ the core has $h\ge5$. The normalized sparsest hue has at most $r-5$ full cliques.

*Proof.* By Corollary 1 it is enough to exclude $h=4$. By Corollary 3, $e_a(U)\ge2r^2+r+1$, so the other hues together have at most $2r^2+r+7-e_a(U)\le6$ edges on $U$ beyond their minima $6r+7$. There are $r-1\ge18$ of them, so some hue $c$ has $\eta_c=3$. Lemma 4 gives $r-2$ disjoint $c$-cliques of size four, each of $a$-degree sum at least $4r+2$. The nine other core vertices have degree at least $r$ by Corollary 1(c). Hence $2e_a(U)\ge(r-2)(4r+2)+9r$, that is $e_a(U)\ge2r^2+\tfrac32r-2$. This exceeds $2r^2+r+7$ when $r\ge19$. ∎

For $7\le r\le18$ the same count leaves $h=4$ open. At $h=5$ Corollary 6 is as far as this count goes: even with Hypothesis A exactly, identity (3) and the minima $\eta_c\ge4$ leave capacity $2r+8$, so a further input of order $r$ is needed there.

## 5. The one-hue problem at small order

A single hue of a balanced coloring satisfies a family of necessary conditions that mention no other hue. For every vertex set $S$,
$$
 e_a(S)\ \le\ \operatorname{cap}(|S|)=B(|S|)-(r-1)\,p_r(|S|),
$$
because each other hue has independence number at most $r$ on $S$. For $|S|=r+j\le2r$ the bound is $B(r)+B(j+1)$. These are the induced edge floors of the September notes. The **one-hue problem** asks for the least number of edges of a graph on $r^2+1$ vertices with independence number at most $r$ that meets every cap. If the answer exceeded $r(r^2+1)/2$ for some $r$, the conjecture would follow at that order with no reference to the other hues.

* **Order three.** The least number is exactly 18, against a mean of 15 and a floor of 12. A witness and the exhaustive lower bound are replayed by the checker.
* **Order four.** A graph with 40 edges exists, against a mean of 34 and a floor of 28. Searches at 38 and at 34 edges each ran for twenty-five minutes without a decision, so the minimum lies between 31 and 40 and the one-hue question at order four is undecided here.
* **Cores at orders five and six.** Searches for a core with $h=3$ on 16 and 19 vertices and with $h=4$ on 21 vertices, within the edge budget of the mean, also ran out of time undecided.

* **Sets of exactly $sr$ vertices.** The same search at $sr$ vertices finds the order-five exception to Lemma 9 at once and was undecided after ten to fifteen minutes at $(r,s)=(6,2),(6,3),(7,3),(8,3)$. The case $(6,2)$ is empty by Lemma 9, which again shows the solver does not certify absence.
* **Local violations of $P(s)$ with all hues.** A second search colors all pairs of $sr+1$ vertices with $r$ hues, requires every $(r+1)$-set to see every hue, and asks for a hue with independence number at most $s$ and no clique of size $r$. It found nothing in fifteen minutes each at $(r,s)=(5,3),(5,4),(6,3),(6,4),(6,5),(7,4),(8,5),(10,5)$. The solver did not finish any of these, including cases where Lemma 1 proves there is nothing to find, so the runs do not show absence. The same program finds the order-five exception to Lemma 9 at once. [Local search program](search_local_core.py)

The one-hue search encodes the independence clauses and the two smallest caps directly, checks every other cap on each model over all vertex sets, and adds violated caps until the solver refutes the instance or a model passes. [Search program](search_one_colour.py) · [Checker](verify_overfull_core.py)

Lemma 1 explains why counting alone cannot settle the one-hue problem at large order: on a set of $hr+1$ vertices the caps leave capacity of order $rh^2/2$ once $h\ge5$. What the small orders test is whether an overfull set with no full clique can meet the caps on all of its subsets at once.

## 6. A reduction to local statements, for any hue

Nothing in Lemmas 1, 2 and 4 uses the normalization. Call an $r$-coloring of any complete graph *balanced* if every $(r+1)$-set sees all hues, and for $s\ge1$ let

**$P(s)$.** In a balanced coloring there are no hue $a$ and vertex set $W$ with $|W|=sr+1$, $\alpha_a(W)\le s$, and no $a$-clique of size $r$ inside $W$.

$P(1)$ is trivial. Lemma 1 is $P(2)$ for $r\ge3$ and $P(3)$ for $r\ge7$. Lemma 2, Corollaries 1 to 3, identity (3), Lemma 4, inequality (4), Corollary 6 and the proof of Theorem 5 use only the three displayed properties of $U$, with degrees taken inside the set. So they hold for every hue $a$ and every such $W$ with $\alpha_a(W)=s$ in place of $U$ and $h$, and Theorem 5 is $P(4)$ for $r\ge19$. The one step of Lemma 1 that used the order of the ambient graph, $\lfloor|W|/r\rfloor=s$, is automatic here because $x\le s\le r-1$. Corollary 4 and the conditional Proposition of Section 3 remain statements about the normalized coloring.

**Lemma 6 (peeling).** In a balanced coloring let $\alpha_a(Y)\le s\le r-1$ and let $B\subseteq Y$ be an $a$-clique of size $r$. Then $\alpha_a(Y\setminus B)\le s-1$.

*Proof.* A vertex outside $B$ has at most one $a$-neighbor in $B$, since its $r$ edges to $B$ carry the other $r-1$ hues. An independent $s$-set in $Y\setminus B$ therefore has neighbors at no more than $s<r$ points of $B$, and a remaining point of $B$ extends it. ∎

**Proposition 7.** Let $r\ge3$. If $P(s)$ holds for every $1\le s\le r-2$, then $K_{r^2+1}$ has no balanced coloring.

*Proof.* Suppose one exists and let $a$ be a least hue, so $e_a\le r(r^2+1)/2$. Some vertex has $a$-degree at most $r-1$: otherwise $a$ is $r$-regular. No component is $K_{r+1}$, since an $a$-clique on $r+1$ vertices misses the other hues, and none is an odd cycle since $r\ge3$. Brooks' theorem then colors $a$ with $r$ colors, and a color class has $r+1$ vertices. Let $v$ have least $a$-degree $d$, put $t=r-1-d$, $q=(r-1)r+1$ and $Y=V\setminus N_a[v]$. Then $|Y|=q+t$ and $\alpha_a(Y)\le r-1$. Every neighbor of $v$ has at least $d-1$ further edges. Summing over $N_a(v)$ counts the $y$ edges inside $N_a(v)$ twice and the $x$ edges leaving $N_a[v]$ once, so $x+2y\ge d(d-1)$ with $y\le B(d)$, hence $x+y\ge B(d)$. So at least $d+B(d)$ edges meet $N_a[v]$ and $e_a(Y)\le r(r^2+1)/2-B(d+1)$.

If $Y$ contains an $a$-clique of size $r$, remove such cliques one at a time while one remains. By Lemma 6, after $j\ge1$ removals the remaining set has independence number at most $s=r-1-j$ and at least $sr+1$ vertices. It cannot be exhausted, so the process stops at a set with no clique of size $r$ and some $1\le s\le r-2$. Any $sr+1$ of its vertices contradict $P(s)$.

If $Y$ contains no $a$-clique of size $r$, let $W\subseteq Y$ have $q$ vertices. By $P(r-2)$, $\alpha_a(W)=r-1$, and every $u\in W$ has at least $r$ neighbors in $W$, because $W\setminus N_a[u]$ has independence number at most $r-2$. Corollary 2 on $W$ gives $r+1$ vertices of degree at least $r+1$. Hence $e_a(W)\ge(qr+r+1)/2$ for every such $W$, and averaging over all of them gives
$$
 e_a(Y)\,\frac{q(q-1)}{(q+t)(q+t-1)}\ \ge\ \frac{qr+r+1}{2}.
$$
At $t=0$ this reads $e_a(Y)\ge(r^3-r^2+2r+1)/2$ against $e_a(Y)\le(r^3-r^2+2r)/2$. For $t\ge1$ write $M=(r^3-r^2+2r)/2$. The bound on $e_a(Y)$ is $M+t(2r-t-1)/2$, and the claim is $(M+t(2r-t-1)/2)\,q(q-1)<(M+\tfrac12)(q(q-1)+t(2q+t-1))$. Since $2r-t-1\le2(r-1)$ and $2q+t-1\ge2q$, we have $t(2r-t-1)q(q-1)/2\le t(r-1)q(q-1)\le2Mtq\le Mt(2q+t-1)$, using $(r-1)(q-1)=r^3-2r^2+r\le2M$. ∎

**Corollary 8.** For $r\ge19$ the conjecture at order $r$ follows from $P(5),\dots,P(r-2)$.

**Lemma 9 (two rows).** Let $r\ge6$. In a balanced coloring every set of $2r$ vertices with $a$-independence number at most two contains an $a$-clique of size $r$.

*Proof.* Each other hue has independence number at most $r$ on the set, hence at least $r$ edges, which leaves at most $r^2$ for $a$. The pairs not in $a$ form a triangle-free graph $F$ with at least $r(r-1)$ edges whose independent sets are $a$-cliques. If there is no $a$-clique of size $r$, every neighborhood of $F$ has at most $r-1$ points, so $F$ is $(r-1)$-regular. If $F$ is bipartite its two classes have $r$ points each and are independent. If not, the Andrásfai–Erdős–Sós theorem gives a vertex of degree at most $4r/5<r-1$. ∎

So a set with $a$-independence two and no full clique has at most $2r-1$ vertices when $r\ge6$, one fewer than $P(2)$ gives. At $r=5$ the lemma fails locally: the product $C_5[K_2]$ on ten vertices is a hue of a balanced coloring of $K_{10}$ whose other four hues are perfect matchings. The checker verifies an explicit one. Section 8 proves the analogous three-row statement $M(3)$ for every $r\ge11$.

**What a least violation looks like.** Suppose $P(s')$ holds for all $s'<s$ and $W$ violates $P(s)$. Then $\alpha_a(W)=s$; every vertex has at least $r$ neighbors in $W$; every independent $J\subseteq W$ with $1\le|J|\le s-1$ has $|N_a[J]|\ge|J|r+1$; at least $r+1$ vertices have degree at least $r+1$; and by Lemma 4 the excess $X=\sum_{v\in W}(d_a(v)-r)$ satisfies $X\ge2(r+1-\eta)$ with no correction term, where $\eta$ is the least surplus of another hue. Identity (3) then gives $(r-2)\eta\le r(s-3)(s+1)/2+s-1$, while $\eta\ge s-1$. At $s=4$ these are incompatible for $r\ge19$, which is Theorem 5. From $s=5$ on they are compatible.

**Sets of exactly $sr$ vertices, and order ten.** Let $M(s)$ say that no balanced coloring has a hue $a$ and a set of $sr$ vertices with $a$-independence at most $s$ and no $a$-clique of size $r$. Deleting a vertex shows that $M(s)$ implies $P(s)$. $M(1)$ is trivial and Lemma 9 is $M(2)$ for $r\ge6$. So by Proposition 7 the conjecture at order $r$ follows from $M(s)$ for $s\le r-2$, and some of these can be dropped. If $M(s-1)$ holds, every vertex $u$ of a set $W$ of $sr+1$ vertices with independence at most $s$ and no full clique has degree at least $r+1$, since $W\setminus N_a[u]$ has at most $(s-1)r-1$ vertices. Hence $X\ge sr+1$. On the other side $X\le r(s^2-4s+1)+4s-2$ by identity (3) with $\eta_c\ge s-1$, and for the set produced in Proposition 7 from a least hue the edge budget gives $X\le r(r-s)$ when $t=0$; the checker evaluates the budget for every $t$, and $t=0$ is always the worst case. The first bound is below $sr+1$ only at $s=4$, so $M(3)$ implies $P(4)$ for every $r\ge5$. The second is below $sr+1$ for every $s\ge r/2$.

At $r=10$ this closes the stops $s=5,6,7$ of Proposition 7 from $M(4),M(5),M(6)$, while $M(4)$ gives $P(4)$ and $P(1),P(2),P(3)$ hold by Lemma 1. The stop $s=8$ and the case with no clique use $P(8)$. Hence **the conjecture at order ten follows from $M(4)$, $M(5)$, $M(6)$ and $P(8)$ at order ten.** The stop $s=5$ closes by one unit of $X$. At $r=11,12$ the budget does not close the stop $s=5$, and at $r=13,14$ the stops $s=5,6$, so $P(s)$ has to be supplied there directly.

**The cost of the $s+1$ doubles, in the tight case.** Let $W$ have $sr+1$ vertices, $\alpha_a(W)=s$ and no full clique, and let $I$ be a maximum independent set with degree sum exactly $sr+2$. In the notation of Lemma 2 every private clique then has $r-1$ vertices and there are exactly $s+1$ other vertices, the *doubles*, each with exactly two neighbors $v_i,v_k\in I$. For a double $y$ let $A_y$, $B_y$ be its non-neighbors among the private neighbors of $v_i$ and of $v_k$. Both are nonempty, since otherwise $y$ completes a private clique to size $r$. Every vertex of $A_y$ is adjacent to every vertex of $B_y$, since otherwise $I\setminus\{v_i,v_k\}$ with $y$ and a nonadjacent pair from $A_y\times B_y$ is independent of size $s+1$. Counting degrees over $I$, the private neighbors and the doubles gives
$$
 X=-3sr-r+6s+4+2\bigl(e_\times+e(P,D)+e(D)\bigr),
$$
where $e_\times$ counts edges between different private cliques, $e(P,D)$ edges from private neighbors to doubles and $e(D)$ edges among doubles. A double contributes at least $2r-4-|A_y|-|B_y|$ to $e(P,D)$ and the $|A_y||B_y|$ edges of its rectangle $A_y\times B_y$ to $e_\times$, together at least $2r-5$. If the rectangles of different doubles are edge-disjoint, for instance if no two doubles have the same pair of neighbors in $I$, which requires $s\ge4$, then
$$
 X\ \ge\ (s+3)r-4s-6 .
$$
When several doubles share a pair the rectangles can overlap; in the examples tried the loss is of order $s^2$ in total. A set $I$ with larger degree sum is not covered: a private clique of $r-2$ vertices can absorb a double as a member, and such sets may have $X$ near $sr$. So $(s+3)r$ is the cost of the structure with $s$ rows of $r-1$ vertices, and $sr+1$, the value forced by $M(s-1)$, is the bound to aim for in general.

**Row capacity, and why tight sets do not exist for $r>s^2+s+1$.** Two counts with the other hues bound how much can attach to a clique of $a$.

*Lemma 11 (row capacity).* Let $Q$ be an $a$-clique with $r-v$ vertices, $v\ge0$, and $Y$ a set of $z$ vertices outside $Q$ with $N$ pairs inside $Y$ not of hue $a$. Then
$$
 \sum_{y\in Y}d_a(y,Q)\ \le\ (r-1)v+z(1-v)+N .
$$
*Proof.* If $z\ge v$, each other hue has independence number at most $r$ on the $r+(z-v)$ vertices of $Q\cup Y$ and so at least $z-v$ edges there. The pairs of $Q\cup Y$ not in $a$ number $z(r-v)-\sum_y d_a(y,Q)+N$. If $z<v$ the right side exceeds the trivial bound $z(r-v)$. ∎

*Lemma 12 (two cliques).* Disjoint $a$-cliques with $r-v$ and $r-v'$ vertices have at most $r-v-v'+vv'$ edges of $a$ between them. *Proof.* Each other hue needs $r-v-v'$ edges on their union, and only the $(r-v)(r-v')$ cross pairs are available. ∎

*Proposition 13 (tight sets).* Let $W$ have $sr+1$ vertices, $\alpha_a(W)=s$ and no full clique, in a balanced coloring with $r\ge5$. If some maximum independent set $I$ of $W$ has degree sum exactly $sr+2$, then $r\le s^2+s+1$.

*Proof.* Use the tight structure above: private cliques $Q_1,\dots,Q_s$ of $r-1$ vertices and $s+1$ doubles. For a double $y$ with neighbors $v_i,v_k$ in $I$, the rectangle $A_y\times B_y$ consists of edges between $Q_i$ and $Q_k$, so $|A_y||B_y|\le r-1$ by Lemma 12. Since $1\le|A_y|,|B_y|\le r-2$, this gives $|A_y|+|B_y|\le r-1$, and $y$ has at least $2(r-1)-(r-1)=r-1$ neighbors in $Q_i\cup Q_k$. Let $Y_i$ be the doubles adjacent to $v_i$ and $z_i=|Y_i|$, so $\sum_iz_i=2(s+1)$. Lemma 11 with $v=1$ gives $\sum_{y\in Y_i}d_a(y,Q_i)\le r-1+B(z_i)$. Summing over $i$ counts each double at its two cliques:
$$
 (s+1)(r-1)\ \le\ s(r-1)+\sum_iB(z_i)\ \le\ s(r-1)+s(s+1),
$$
because $\sum_iB(z_i)$ is largest when two of the $z_i$ equal $s+1$. ∎

So for $r\ge s^2+s+2$ every maximum independent set of such a $W$ has degree sum at least $sr+3$, and in a least violation $X\ge3(r+1-\eta)$ in place of $2(r+1-\eta)$. The same count in general reads as follows. Let the private cliques of $I$ have $r-v_i$ vertices, $V=\sum_iv_i$, so that there are $V+1$ doubles. Let a double $y$ have $j_y\ge2$ neighbors in $I$, put $\sigma=\sum_y(j_y-2)$, and let $M(y)$ count its non-neighbors among the private neighbors of those $j_y$ vertices. Then
$$
 (r-1)(V+2+\sigma)\ \le\ \sum_yM(y)+\sum_iN_i ,                                   \tag{5}
$$
where $N_i\le B(z_i)$ counts pairs not in $a$ among the doubles adjacent to the $i$-th vertex of $I$. For a double with $j_y=2$ and both non-neighbor sets nonempty, Lemma 12 gives $M(y)\le r+(v_i-1)(v_k-1)$. Identity (3) shows that $P(s)$ follows, for $r$ large, once every maximum independent set of a least violation has degree sum at least $sr+s^2-4s+2$. Inequality (5) is the tool for that: it excludes all maximum independent sets with $V-s$ and $\sigma$ small once $r$ is large compared with $s$. The remaining step, a bound on $M(y)$ for doubles with three or more neighbors in $I$, is the fourth case of Proposition 15 in Section 9. This count is the exact form, for a set of $sr+1$ vertices, of the exterior-vertex argument in §3 of the base manuscript.

**How the fixed-case proofs fit.** The proof for $r=6$ in the fixed-case repository has the shape of Proposition 7 with one hue: a least hue, Brooks, deletion of a minimum-degree vertex with the same edge accounting, and averaging down to 31 vertices. In place of the other hues it uses the cap on seven-sets and an edge budget. Its clique lemmas on 19 and 25 vertices, with at most 66 and 81 edges, are $P(3)$ and $P(4)$ with the budget $X\le r(r-s)$. Its lemmas on 18 and 24 vertices, which that paper labels $P_3$ and $P_4$, are budgeted forms of $M(3)$ and $M(4)$. Its 31-vertex bound of 97 edges has the same threshold as the count $(qr+r+1)/2$ above but is proved there by a second deletion, three clique removals and a terminal lemma on triangle-free graphs. The proof for $r=5$ shares only the first step. It then forces every hue to exactly 65 edges, removes isolated cliques forced by equality, and finishes with layers at independence two, three and four and two classifications on fifteen vertices. Lemmas 1 and 4 use the other hues where those papers use a budget, and take over at small $s$ once $r\ge19$.

## 7. What remains

1. **$P(5)$ and $P(6)$ at moderate order.** Section 9 proves $P(5)$ for $r\ge350$ and $P(6)$ for $r\ge3833$, and $P(s)$ for $r\ge2s^6$ in general. The constants are crude. Lowering the thresholds, and settling $P(5)$ between $r=19$ and $r=349$, needs a sharper count for doubles with three or more neighbors and for several doubles on one pair of rows.
2. **$P(s)$ when $s$ is not small compared with $r$.** Section 9 settles every fixed $s$ at large order by a count on $W$ alone, so the earlier worry that such a count stops at $s=7$ was wrong for large $r$. It still needs $r$ of order $s^6$. Once the least surplus of the other hues exceeds $r$, Lemma 4 supplies no disjoint heavy sets and the last step of Theorem 14 is unavailable. Whether a violation can exist locally for $s$ comparable to $r$ is open.
3. **$M(s)$ and the edge budget.** In Proposition 7 the least hue gives $X\le rk$ with $k=r-s$ cliques removed. Degree at least $r+1$ at every vertex, which is what $M(s-1)$ gives, then closes every stop with $s\ge r/2$. Order ten reduces to $M(4)$, $M(5)$, $M(6)$ and $P(8)$. For $r\ge11$, Section 8 settles $M(3)$. The next local statements are $M(4)$ on $4r$ points and $P(5)$ on $5r+1$.
4. **$P(4)$ at order ten and $P(3)$ below $r=7$.** Theorem 10 covers $P(4)$ from order eleven. Orders up to nine are covered globally by the fixed-case proofs.

## 8. Three rows at orders eleven and above

**Theorem 10 (23 November 2026).** For every $r\ge11$, $M(3)$ holds. In any balanced $r$-coloring, every set of $3r$ vertices with independence number at most three in hue $a$ contains an $a$-clique of size $r$. Consequently $P(4)$ holds for every $r\ge11$.

Suppose $W$ violates $M(3)$. All degrees in the proof are on $W$ unless an induced graph is specified. Let $H$ consist of the edges of all colors except $a$. Then $H$ is $K_4$-free and $\alpha(H)\le r-1$. For each $v$, the set $W\setminus N_a[v]$ has $a$-independence at most two. Lemma 9 gives $|W\setminus N_a[v]|\le2r-1$, so $d_a(v)\ge r$. Put
$$
 q(v)=d_a(v)-r,\quad X=\sum_v q(v),\quad
 \eta_c=e_c(W)-3r\quad(c\ne a),\quad \Sigma=\sum_{c\ne a}\eta_c.
$$
Turán gives $\eta_c\ge0$ because $\alpha_c(W)\le r$. Counting all pairs gives $X+2\Sigma=3r$. If $\Sigma=0$, equality in Turán makes every other hue a union of $r$ vertex-disjoint triangles. Thus $H$ is $2(r-1)$-regular. This degree is strictly greater than $3|W|/5=9r/5$ for $r\ge11$. Goddard and Lyle's Corollary 1 gives an independent set of size at least $|W|/3=r$ in $H$, a contradiction. Hence $\Sigma>0$, and $X<3r$ gives a vertex $x$ with $q(x)=0$. Also $\Sigma\le3r/2<2(r-1)$, so some other hue has $\eta_c\le1$. Brouwer's Theorem 2 partitions $W$ into $r$ cliques of this hue. Each has size at most three by $\alpha_a\le3$. This is a partition into $r$ independent triples of hue $a$. [Goddard–Lyle, Corollary 1](https://people.computing.clemson.edu/~goddard/papers/denseNoClique.pdf) · [Brouwer, Theorem 2](https://ir.cwi.nl/pub/6791/6791D.pdf#page=4)

**Two vertices with many target edges.** Set $S=N_H(x)$, so $|S|=2r-1$. The graph $F=H[S]$ is triangle-free, has $\alpha(F)\le r-1$, and cannot be bipartite, as its larger class would have size at least $r$. Each other hue contributes at least $p_r(2r-1)=r-1$ edges on $S$. Thus $e(F)\ge(r-1)^2$.

We claim $F$ has an edge $yz$ with $d_F(y)+d_F(z)\le r+2$. Take a shortest odd cycle of length $\ell$. It is induced. Each exterior point sees at most two of its vertices. Otherwise its consecutive neighbors cut the cycle into at least three gaps of length at least two, and an odd gap together with the exterior point makes a shorter odd cycle. In any such triangle-free graph on $n$ vertices, Mantel's bound on the remaining graph therefore gives
$$
 e\le \ell+2(n-\ell)+\left\lfloor (n-\ell)^2/4\right\rfloor .
$$
The right side decreases with $\ell$. For $n=2r-1$ and $\ell\ge7$ it is at most $(r-2)^2+3<(r-1)^2$. Thus the cycle $C$ has five vertices. Write $m=r-3$ and $T=F-C$, of order $2m$. Since $5+4m+m^2=(r-1)^2+1$, the deficits $4m-e(C,T)$ and $m^2-e(T)$ are nonnegative and sum to at most one. If $T$ were nonbipartite, the odd-cycle bound at $n=2m,\ell=5$ would give $e(T)\le m^2-m+1<m^2-1$.

The two parts of $T$ have sizes $m,m$ or $m-1,m+1$ since $e(T)\ge m^2-1$. In the unequal case $T$ is complete bipartite and every vertex of $T$ has two neighbors in $C$. A point in the smaller part has degree $m+3=r$ in $F$, an independent neighborhood of forbidden size. Thus the parts have size $m$ and at most one cross edge is absent. If some $y\in C$ sees both parts, it sees precisely the two endpoints of the missing edge. A cycle neighbor $z$ of $y$ sees neither endpoint, so it sees at most $m-1$ vertices of a single part. Their degrees sum to at most $4+(2+m-1)=r+2$. Otherwise label each cycle vertex by the part it sees, choosing either label if it sees neither. Two consecutive vertices have the same label. Their neighbors in that part are disjoint and their degrees sum to at most $m+4=r+1$. This proves the claim.

Within $S$, these $y,z$ have $a$-degree sum at least $2(2r-2)-(r+2)=3r-6$. Their common neighbors in $H$ form an independent set in $H$, since $yz\in H$ and $H$ is $K_4$-free. One such neighbor is $x$, so at most $r-2$ of the $r$ vertices in $N_a(x)$ can also be common neighbors. At least two additional $a$-edges from $y,z$ go to $N_a(x)$, outside $S$. Hence $d_a(y)+d_a(z)\ge3r-4$.

**What the other colors pay at this pair.** Define $D_c(v)=(2-d_c(v))_+$ and $D(v)=\sum_{c\ne a}D_c(v)$, so $d_a(v)\le r+1+D(v)$. For $d_c(v)=j\in\{0,1\}$, the $3r-1-j$ vertices outside $N_c[v]$ have $c$-independence at most $r-1$. They cannot be covered by $r-1$ cliques, each of size at most three. Brouwer's theorem, with the $j$ edges at $v$ added back, gives
$$
 e_c(W)\ge p_{r-1}(3r-1-j)+2+j .
$$
This costs at least five surplus edges for degree zero and three for degree one.

If $y,z$ both have $c$-degree at most one and $yz$ is not color $c$, put $j=d_c(y)+d_c(z)\le2$. Outside $N_c[y]\cup N_c[z]$ at least $3r-2-j$ vertices remain, with $c$-independence at most $r-2$. Choose exactly $3r-2-j$ of them. Their number exceeds $3(r-2)$, ruling out a cover by $r-2$ cliques. Brouwer now gives
$$
 e_c(W)\ge p_{r-2}(3r-2-j)+2+j
          =3r+8-2j=3r+2(D_c(y)+D_c(z)).
$$
If just one endpoint has a shortfall, its single-vertex bound also pays at least twice the shortfall. For the one hue of $yz$, two shortfalls require both degrees to equal one. Its single-vertex bound pays at least three for the combined shortfall of two. In total,
$$
 \Sigma\ge2(D(y)+D(z))-1\ge 2r-13 ,
$$
using $d_a(y)+d_a(z)\ge3r-4$. In particular $\Sigma>6$.

**Every independent triple has positive excess.** Suppose the three roots of a target-independent triple all have degree $r$. Every other vertex meets a root, since $\alpha_a\le3$. A root and its private neighbors form a clique, as two nonadjacent private neighbors would extend the other two roots to an independent four-set. Each root has at most $r-2$ private neighbors. At least three of the $3r-3$ exterior vertices meet multiple roots. The degree sum is $3r$, so these three excess incidences give exactly three doubles, each meeting two roots. All private cliques $C_i$, including their roots, have size $r-1$. Each root meets two of the doubles, so exactly one double lies on each pair of roots.

For a double on $i,j$, its lists of $a$-nonneighbors in $C_i,C_j$ have sizes $u,v\ge1$, since it cannot extend either clique to size $r$. Every edge between the lists has hue $a$. Otherwise the double, the unused root and the two list vertices would form an independent four-set. The double's edges to the cliques and the edges between the lists contribute $2(r-1)-u-v+uv\ge2r-3$. The three rectangles lie on distinct pairs of cliques. Thus $e_a(W)\ge3\binom{r-1}{2}+3(2r-3)$, giving $X\ge3r-12$ and $\Sigma\le6$, a contradiction.

In the partition into $r$ independent triples, at least $r-2$ triples avoid $y,z$. Each contributes at least one unit of $q$. The endpoints themselves contribute at least $r-4$. Hence $X\ge2r-6$, so $2\Sigma\le r+6$. The two bounds on $\Sigma$ imply $4r-26\le r+6$, or $3r\le32$. This contradicts $r\ge11$ and proves $M(3)$. Section 6 gives $M(3)\Rightarrow P(4)$. ∎

At $r=11$ the final integer bounds are $\Sigma\ge9$ and $\Sigma\le8$. At $r=10$ the regular degree equals the strict Goddard–Lyle threshold, and the final bounds allow $\Sigma=7,8$. The proof and its local arithmetic checker await independent mathematical review.

## Scope

Sections 1–7 contain Lemmas 1–4, 6 and 9, Corollaries 1–4, 6 and 8, Theorem 5, Proposition 7, the reduction at order ten, and the count for edge-disjoint rectangles. A second reader re-derived Section 6 and corrected the list of hypotheses at order ten and the description of the fixed-case proofs. Sections 1–4 use the normalized coloring of the grid supplement. Section 6 works for any balanced coloring. The earlier internal checks included Brouwer's and Füredi's theorems and the numbered results in Sections 1–6. The proposition in Section 3 assumes Hypothesis A. The order-three minimum has a solver certificate and an explicit witness. The order-four and core searches were undecided.

Section 8 gives the November 23 proof of Theorem 10 and its consequence for $P(4)$. The checker replays the arithmetic, the root-pair count, and small instances of the five-cycle attachment argument. The full argument is in prose and awaits independent mathematical review. The conjecture for every $r\ge3$ remains open in this project.

**Review note, 23 November 2026 (second seat).** Section 8 was read line by line by the seat that did not write it. Every step was re-derived: the degree bound from Lemma 9, the pair count $X+2\Sigma=3r$, the regular case, the partition into independent triples, the five-cycle claim with both attachment cases, the two additional edges into $N_a(x)$, the single-vertex and pair bounds on the other hues including the hue of $yz$, the excess of independent triples, and the final inequality $3r\le32$. No gap was found. Corollary 1 of Goddard and Lyle was read in the paper and states that any $K_4$-free graph with minimum degree greater than $3n/5$ has an independent set of size $n/3$, which is what the regular case uses. The checker's replay of small five-cycle instances was run, not inspected. This is an internal check by a second model seat and does not replace outside review.

**Added 23 November 2026.** Lemmas 11 and 12, Proposition 13 and inequality (5) in Section 6 (row capacity and tight sets). Their review note is at the end of Section 9.

## 9. Every fixed number of rows, at large order

**Theorem 14 (23 November 2026).** For $s\ge5$ put $E_0=s^2-4s-1$ and
$$
 G(s,E)=2E(E+1)(E+2)+(s+E)(s+E+1)+E(s+E)/2 .
$$
If $r>1+G(s,E_0)$, then $P(s)$ holds at order $r$. In particular $P(5)$ holds for $r\ge350$ and $P(6)$ for $r\ge3833$. The bound $1+G(s,E_0)$ increases with $s$, so $P(s')$ holds for every $s'\le s$ at such $r$.

Notation is that of Lemma 2 and inequality (5). Let $W$ have $sr+1$ vertices, $\alpha_a(W)=s$ and no full clique. For a maximum independent set $I=\{u_1,\dots,u_s\}$ let the private clique $Q_i\ni u_i$ have $r-v_i$ vertices, where $v_i$ is an integer, $\tau_i=v_i-1\ge0$, $T=\sum_i\tau_i$, $V=s+T$. The $V+1$ other vertices are the doubles. A double $y$ has $j_y\ge2$ neighbors $u_i$, $i\in J_y$, and $m_i(y)$ non-neighbors among the private neighbors of $u_i$. Put $M(y)=\sum_{i\in J_y}m_i(y)$, $\sigma=\sum_y(j_y-2)$ and $E=T+\sigma$. The degree sum of $I$ is $sr+2+E$.

**Proposition 15.** If $r\ge E^2+4$, then $r-1\le G(s,E)$.

*Proof.* Inequality (5) comes from Lemma 11 on each $Q_i$ with the doubles adjacent to $u_i$: such a double has $r-v_i-m_i(y)$ neighbors in $Q_i$, so $(r-1)(z_i-v_i)\le\sum_ym_i(y)+N_i$, and summing over $i$ with $\sum_iz_i=2(V+1)+\sigma$ gives (5). Write it as $\sum_y\bigl((r-1)j_y-M(y)\bigr)\le(r-1)V+\sum_iN_i$. We bound each term on the left from below. Lemma 12 gives at most $c_{ik}=r-1+\tau_i\tau_k$ edges of $a$ between $Q_i$ and $Q_k$, and $c_{ik}\le2r-5$ because $\tau_i\tau_k\le E^2\le r-4$.

*Two neighbors, both lists nonempty.* The lists are completely joined, as in the tight case, so $m_im_k\le c_{ik}$. With $1\le m_i,m_k\le r-2$ this forces $m_i+m_k\le r-1$. The term is at least $r-1$.

*Two neighbors, one list empty.* Then $M(y)\le r-2$ and the term is at least $r$.

*Three or more neighbors, some list empty.* Then $M(y)\le(j_y-1)(r-2)$ and the term is at least $r+j_y-2$.

*Three or more neighbors, all lists nonempty.* Choosing one vertex from each list gives, with $y$ and the other $s-j_y$ vertices of $I$, a set of $s+1$ vertices, so every such choice contains an edge of $a$. An edge between the lists of $i$ and $k$ lies in a fraction $1/(m_im_k)$ of the choices. Hence $\sum_{i<k}c_{ik}/(m_im_k)\ge1$, and the two smallest lists satisfy $m_{(1)}m_{(2)}\le B(j_y)(r-1+t^2)$, where $t=\max_i\tau_i\le E$. If $m_{(2)}<(r-2)/2$ then $M(y)<(j_y-1)(r-2)$. Otherwise $m_{(1)}\le j_y(j_y-1)(1+\delta)$ with $\delta=(t^2+1)/(r-2)\le1$, and $M(y)\le(j_y-1)(r-2)+2j_y(j_y-1)$. The term is at least $r-1-2j_y(j_y-1)$.

At most $\sigma\le E$ doubles have three or more neighbors, and $j_y\le E+2$. So the left side is at least $(V+1)(r-1)-2E(E+1)(E+2)$. On the right, $N_i\le B(z_i)\le z_iV/2$ since $z_i\le V+1$, and $\sum_iz_i=2V+2+\sigma$, so $\sum_iN_i\le V(V+1)+\sigma V/2$. Since $V\le s+E$, the inequality becomes $r-1\le G(s,E)$. ∎

*Proof of Theorem 14.* Induct on $s$; $P(1),\dots,P(4)$ hold for $r\ge19$ by Lemma 1 and Theorem 5, so Section 8 is not needed here. Let $W$ violate $P(s)$. By $P(s-1)$ every vertex has degree at least $r$ in $W$, and $\alpha_a(W)=s$. Since $G$ increases with $E$ and $r>1+G(s,E_0)\ge E_0^2+4$, Proposition 15 shows that every maximum independent set has $E\ge E_0+1$, that is, degree sum at least $sr+e_0$ with $e_0=s^2-4s+2$. Let $\eta$ be the least surplus of another hue. Lemma 4 gives $r+1-\eta$ disjoint maximum independent sets and every other vertex has degree at least $r$, so $X\ge e_0(r+1-\eta)$; if $\eta\ge r+1$ this holds because $X\ge0$. With $2E_a=(s-1)r+X$, identity (3) gives
$$
 \eta\,(r-1-e_0/2)\ \le\ r\,(2s-3)/2+s-e_0/2 ,
$$
while $\eta\ge s-1$ and $r-1-e_0/2>0$. These are incompatible when $r>s^3-6s^2+14s-6$, which is below $1+G(s,E_0)$. ∎

At $s=4$ the last threshold is $r>18$ with $e_0=2$, which is Theorem 5. The constants in $G$ are not optimized: the cubic term comes from a crude bound on doubles with three or more neighbors. What the argument shows is that for each fixed number of rows the statement holds from an explicit order on. Since $1+G(s,E_0)<2s^6$ for $s\ge5$, $P(s)$ holds whenever $r\ge2s^6$. The range of $s$ comparable to $r$ is untouched by it.

**Review note, 23 November 2026.** Lemmas 11 and 12, Proposition 13, inequality (5), Proposition 15 and Theorem 14 were re-derived from scratch by a second reader, who found no failing step and asked for the sentences now added: the reason for $c_{ik}\le2r-5$, the derivation of (5), the bound $B(z)\le zV/2$, the two remarks in the last step, and the use of Theorem 5 in place of Theorem 10. The checker covers only the arithmetic of this section. This is an internal check and does not replace outside review.

**Codex review, 23 November 2026 (Section 9).** I re-derived Proposition 15 and Theorem 14 line by line. In (5) the row term is $(r-1)(z_i-v_i)$. For two positive lists, a sum of at least $r$ would cost a product of at least $2(r-2)$ when both entries are at most $r-2$, exceeding $2r-5$. For three or more positive lists, the two smallest have product at most $\binom j2(r-1+t^2)$. Dividing by the second when it is at least $(r-2)/2$ gives the factor $j(j-1)(1+\delta)$ used in the proof. The other two empty-list cases, the charge to at most $E$ vertices, and the bound $\sum_i \binom{z_i}2\le V(V+1)+\sigma V/2$ all follow with the stated directions. In the induction I obtain $r>4s-2+(s-2)e_0=s^3-6s^2+14s-6$ after substituting the least possible surplus. I also expanded the threshold comparisons at $s=5+u$. The differences $1+G-(E_0^2+4)$, $1+G-(s^3-6s^2+14s-6)$, and $2s^6-1-G$ have positive coefficients for $u\ge0$, including their constant terms. The first two integer orders are 350 and 3833. I found no gap. This is an internal mathematical review.

## 10. Three rows at order ten

**Theorem 16 (23 November 2026).** $M(3)$ holds at $r=10$. Consequently $P(4)$ holds at $r=10$.

The proof is that of Theorem 10 with three changes. The regular case uses the non-strict form of the minimum-degree theorem. A shortfall at a single endpoint is charged its full cost. The last step applies Lemma 9 to the vertices of excess zero. The second seat wrote this argument on 23 November 2026. The arithmetic checker and the dated Codex review at the end of this section both pass. External review is pending.

Let $r=10$ and suppose $W$ violates $M(3)$. Notation is that of Section 8. As there, $q(v)\ge0$ by Lemma 9, $X+2\Sigma=30$, and $H$ is $K_4$-free with $\alpha(H)\le9$.

**The regular case.** If $\Sigma=0$, every other hue is ten disjoint triangles and $H$ is 18-regular on 30 vertices, so $\delta(H)=3|W|/5$ with equality. Corollary 1 of Goddard and Lyle asks for strict inequality. The statement with equality allowed is Brandt's theorem: a $K_4$-free graph $G$ on $n$ vertices with $\delta(G)\ge3n/5$ has $\alpha(G)\ge n/3$. Lyle proves it in two steps, which we repeat. Pass to a maximal $K_4$-free supergraph, which keeps the degree bound and has no new independent sets. If it is not the join of an independent set $I$ and a triangle-free graph $T$, Lyle's Theorem 3 gives $\alpha\ge2(2\delta-n)\ge2n/5$; that theorem needs $\delta>4n/7$, and $3/5>4/7$. If it is such a join and $|I|<n/3$, then $\delta(T)\ge\delta-|I|>\tfrac25|T|$, because $5(3n/5-|I|)>2(n-|I|)$ is the inequality $n>3|I|$. Then $T$ is bipartite by Andrásfai, Erdős and Sós, and $\alpha\ge|T|/2>n/3$. Here $n/3=10$, which is an $a$-clique of size $r$ in $W$. Hence $\Sigma>0$. [Lyle, Theorem 3 and Section 5.1](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v21i2p38)

**What carries over from Section 8.** With $\Sigma>0$, each of the following steps uses $r$ only through an inequality that holds at $r=10$.

- There is a vertex $x$ with $q(x)=0$, since $X<30$.
- Some other hue has $\eta_c\le1$, since $\Sigma\le15<18$. Brouwer's theorem partitions $W$ into ten independent triples. Fix this partition $\mathcal T$.
- $F=H[N_H(x)]$ has 19 vertices, is triangle-free and not bipartite, and has $e(F)\ge81$. Its shortest odd cycle has length five, since length seven or more allows at most 67 edges. $T=F-C$ is bipartite, since otherwise $e(T)\le43<48$. Its parts have size seven with at most one cross edge absent, since parts of sizes six and eight would give a vertex of degree ten in $F$.
- $F$ has an edge $yz$ with $d_F(y)+d_F(z)\le12$. Hence $d_a(y)+d_a(z)\ge26$, that is, $q(y)+q(z)\ge6$.
- A hue in which a vertex has degree zero has surplus at least five, and degree one costs at least three. If both $y$ and $z$ have degree at most one in a hue other than that of $yz$, its surplus is at least $2(D_c(y)+D_c(z))$.
- $\Sigma\ge2(D(y)+D(z))-1\ge7$. Since $\Sigma>6$, every independent triple has positive excess.

All of this holds for every vertex of excess zero in place of $x$. Call the edge $yz$ it produces a *heavy pair* of that vertex.

**Sharper accounting.** Fix $x$ and a heavy pair $yz$. Put $Q=q(y)+q(z)$ and $D=D(y)+D(z)$. Let $n_1$ be the number of hues in which exactly one of $y,z$ has a shortfall. Let $\varepsilon=1$ if both have a shortfall in the hue of $yz$, and $\varepsilon=0$ otherwise. A hue with one short end has surplus at least twice the shortfall plus one, by the single-vertex bounds three and five. The hue of $yz$ with two short ends has both degrees equal to one and surplus at least three. Therefore
$$
 \Sigma\ge 2D+n_1-\varepsilon .                                      \tag{6}
$$
Also $D\ge Q-2$, because $q(v)\le1+D(v)$. At least eight triples of $\mathcal T$ avoid $y$ and $z$, and each has excess at least one, so $X\ge Q+8$. Combining,
$$
 30=X+2\Sigma\ge Q+8+4(Q-2)+2(n_1-\varepsilon)=5Q+2(n_1-\varepsilon)\ge5Q-2 .
$$
Hence $Q=6$ and $n_1\le\varepsilon$. Also $D=4$, since $D\ge5$ would give $\Sigma\ge9$ and $X\le12$. Three cases remain.

1. $\varepsilon=0$, $n_1=0$. Then $\Sigma\ge8$ and $X=14$.
2. $\varepsilon=1$, $n_1=1$. The hue of $yz$ accounts for two units of $D$, and one hue with a single end at degree zero accounts for the other two. Then $\Sigma\ge3+5=8$ and $X=14$.
3. $\varepsilon=1$, $n_1=0$. The hue of $yz$ and one further hue each have both ends at degree one. Then $D(y)=D(z)=2$, so $q(y)=q(z)=3$. Here $\Sigma\ge7$, and $X$ is even, so $X\in\{14,16\}$.

The checker enumerates every assignment of shortfalls to the nine hues and confirms that the only outcomes are $(X,q(y),q(z))=(14,3,3),(14,4,2),(14,2,4),(16,3,3)$.

**The case $X=14$.** The vertices other than $y,z$ have total excess eight. If $y$ and $z$ lay in one triple, nine triples would avoid them. So exactly eight triples avoid them, each contains one vertex of excess one and two of excess zero, and the other four vertices of the two remaining triples have excess zero. Thus twenty vertices have excess zero. They contain no independent triple, because every independent triple has positive excess. By Lemma 9 these $2r$ vertices contain an $a$-clique of size ten, a contradiction.

**The case $X=16$.** Now every heavy pair is in case 3, so both of its vertices have excess three. The vertices other than $y,z$ have total excess ten, so the set $Z$ of vertices of excess zero has at least 18 members. The hue of $yz$ has surplus at least three, so it is not the hue of $\mathcal T$, and $y,z$ lie in different triples. Choose one heavy pair for each vertex of $Z$.

If the chosen pair is $\{y,z\}$ for every vertex of $Z$, then $Z$ lies in the common $H$-neighborhood of $y$ and $z$. That neighborhood is independent in $H$, since $yz\in H$ and $H$ is $K_4$-free. So $Z$ is an $a$-clique on at least 18 vertices, a contradiction.

Otherwise some vertex of $Z$ has a heavy pair $\{y',z'\}\ne\{y,z\}$. If the two pairs are disjoint, the four vertices carry excess 12 and at least six triples avoid them, so $X\ge18$. If they share one vertex, the other vertex $w$ of the new pair has excess three. If $w$ lies in the triple of $y$ or of $z$, the vertices other than $y,z$ have total excess at least $3+8=11$. So $w$ lies in one of the eight triples avoiding $y,z$, which then contribute at least $3+7=10$. This is all of the ten: exactly ten vertices have positive excess, $|Z|=20$, and Lemma 9 gives a contradiction as before. This proves $M(3)$ at $r=10$. Section 6 gives $M(3)\Rightarrow P(4)$. ∎

**What this changes.** At order ten, $P(4)$ no longer waits on $M(4)$. The list for order ten in Section 6 is otherwise unchanged: $M(4)$ is still needed for $P(5)$, then $M(5)$, $M(6)$ and $P(8)$. The four-row argument in `four-rows.md` takes $M(3)$ as input, and that input is now available at order ten.

**Why the same proof stops here.** At $r=9$ a heavy pair gives only $\Sigma\ge5$, while positive excess on every independent triple needs $\Sigma>6$. The regular case is not the obstacle there: an argument like the one above still gives an independent set of size nine.

**Codex review, 23 November 2026 (Section 10).** I re-derived Theorem 16, including the equality case at degree 18 on 30 vertices. Lyle's Theorem 3 applies strictly above $4n/7$. In its nonjoin case the independent-set bound is at least 12. In the join case an independent part of size at most nine leaves a triangle-free part with minimum degree strictly above two fifths of its order, making it bipartite. This justifies the equality case separately from any printed endpoint convention. I checked the five-cycle count at 19 vertices, the two surplus costs of three and five, the joint charge including the color of the heavy edge, and the eight untouched triples. They give $Q=6,D=4$ and exactly the four listed ordered outcomes. At $X=14$, the eight units away from the endpoints occupy eight distinct triples, leaving twenty zero vertices. At $X=16$, disjoint heavy pairs spend at least eighteen units. Two intersecting pairs force exactly seven positive vertices outside their three endpoints. A common heavy pair for every zero vertex would put all zero vertices in an independent set of the nontarget graph. These exhaust the cases and justify the final use of Lemma 9. I found no gap in $M(3)$ or its consequence $P(4)$ at ten. The arithmetic checker also passed. Independent external review is pending. [Lyle, Theorem 3 and §5.1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v21i2p38/pdf/#page=3)

## 11. The edge budget passes down the reduction

The second seat wrote this section on 23 November 2026. A dated internal review follows the proof.

Order ten was reduced in Section 6 to $M(4)$, $M(5)$, $M(6)$ and $P(8)$. Those statements ask more than the reduction uses. Every set met in Proposition 7 lies in a least hue, and the bound on that hue's edges is inherited by the smaller sets. For a vertex set $W$ write $X(W)=\sum_{v\in W}(d_a(v)-r)$ with degrees taken inside $W$.

**$S(s)$.** No balanced coloring has a hue $a$ and a set $W$ with $|W|=sr+1$, $\alpha_a(W)\le s$, no $a$-clique of size $r$, and $X(W)\le r(r-s)$.

**$M(s;\beta)$.** No balanced coloring has a hue $a$ and a set of $sr$ vertices with $a$-independence at most $s$, no $a$-clique of size $r$, and $X\le\beta$.

$P(s)$ implies $S(s)$, and $M(s)$ implies $M(s;\beta)$ for every $\beta$.

**Lemma 17.** Let $2\le s\le r-1$. Let $|W|=sr+1$, $\alpha_a(W)\le s$, with no $a$-clique of size $r$ in $W$ and $X(W)\le r(r-s)$. Let $u$ have least degree $d$ in $W$.

1. If $d\le r-1$, then $W\setminus N_a[u]$ contains a set $W''$ of $(s-1)r+1$ vertices with $\alpha_a(W'')\le s-1$ and $X(W'')\le r(r-s+1)$.
2. If $d=r$, then $W'=W\setminus N_a[u]$ has $(s-1)r$ vertices, $\alpha_a(W')\le s-1$, and $X(W')\le X(W)-2(r-1)$.
3. If $d\ge r+1$, then $X(W)\ge sr+1$.

*Proof.* Put $e=e_a(N_a(u))$ and let $c$ be the number of $a$-edges from $N_a(u)$ to $W\setminus N_a[u]$. Every neighbor of $u$ has degree at least $d$ in $W$, so $d+2e+c\ge d^2$.

For the first part put $t=r-1-d$. The set $W\setminus N_a[u]$ has $(s-1)r+1+t$ vertices and independence at most $s-1$. It has $e_a(W)-(d+e+c)\le e_a(W)-d^2+e\le e_a(W)-\binom{d+1}2$ edges, since $e\le\binom d2$, and $2e_a(W)\le r(r-s)+r(sr+1)$. At $t=0$ this set is $W''$ and $X(W'')\le r(r-s)+r(sr+1)-r(r-1)-r((s-1)r+1)=r(r-s+1)$. For $t\ge1$ take a subset of $(s-1)r+1$ vertices with at most the average number of edges. The checker confirms that the resulting bound is below the value at $t=0$ for every $6\le r\le40$, every $s$ and every $t$. This is the computation in the proof of Proposition 7, one level down.

For the second part, $N_a[u]$ has $r+1$ vertices, so it sees each of the other $r-1$ hues. All pairs at $u$ have hue $a$. Hence at least $r-1$ pairs inside $N_a(u)$ are not in $a$, and $e\le\binom r2-(r-1)$. Counting degrees over $W'$, over $N_a(u)$ and at $u$,
$$
 X(W)=\bigl(X(W')+c\bigr)+\bigl(r+2e+c-r^2\bigr)+0 .
$$
Hence $X(W')=X(W)+r^2-r-2e-2c\le X(W)-(r^2-r-2e)\le X(W)-2(r-1)$, using $c\ge r^2-r-2e$. The third part is immediate. ∎

**Proposition 18.** Let $s\ge r/2$. If $S(s-1)$ and $M(s-1;\,r(r-s)-2(r-1))$ hold, then $S(s)$ holds.

*Proof.* Let $W$ violate $S(s)$ and apply Lemma 17. The first case contradicts $S(s-1)$. The second contradicts $M(s-1;r(r-s)-2(r-1))$. The third gives $X(W)\ge sr+1>r(r-s)$, because $2s\ge r$. ∎

**Corollary 19 (order ten).** The conjecture at $r=10$ follows from the four statements
$$
 M(4;32),\qquad M(5;22),\qquad M(6;12),\qquad M(7;2).
$$

*Proof.* $S(1),\dots,S(4)$ hold because $P(1),\dots,P(4)$ hold at order ten, by Lemma 1 and Theorem 16. Proposition 18 gives $S(5)$, $S(6)$, $S(7)$, $S(8)$ in turn. Now follow the proof of Proposition 7 with a least hue. If the removal of cliques stops at some $s\le8$, the remaining set has $sr+1+t$ vertices and at most $r(r^2+1)/2-\binom{r-t}2-(r-1-s)\binom r2$ edges. A subset $W$ of $sr+1$ vertices with at most the average number of edges has $X(W)\le r(r-s)$; this is the budget of Section 6, which the checker evaluates for every $t$. It contradicts $S(s)$.

If $Y$ contains no clique of size $r$, choose $W\subseteq Y$ with 91 vertices and at most the average number of edges, so $X(W)\le10$. If $\alpha_a(W)\le8$, a subset of 81 vertices with at most the average number of edges has negative $X$ and contradicts $S(8)$. So $\alpha_a(W)=9$. If some vertex of $W$ has degree at most nine, the first part of Lemma 17 with $s=9$ gives 81 vertices with independence at most eight and $X\le20$, again contradicting $S(8)$. Otherwise every degree is at least ten, Corollary 2 gives eleven vertices of degree at least eleven, and $X(W)\ge11$, a contradiction. ∎

**Corollary 20 (the four-row piece at order ten).** Assume the exclusions at order ten of every profile with $k\le3$ in `four-row-descent.md`. Then $M(4;32)$ holds at $r=10$, so $S(5)$ holds there, and the conjecture at order ten follows from $M(5;22)$, $M(6;12)$ and $M(7;2)$.

*Proof.* Let $W'$ have 40 vertices, independence at most four, no clique of size ten and $X(W')\le32$. Use the notation of that note: $k$ is the least excess of an independent quartet and $m$ the least surplus of another hue. If $m\le2$ there are ten disjoint independent quartets, so $10k\le X\le32$ and $k\le3$. If $m\ge3$ then $k\le3$ by its Section 2. Every profile with $k\le3$ is excluded there. ∎

The second seat read the lemmas and the checker of `four-row-descent.md` and found no failing step, but did not replay its certificates independently. Corollary 20 inherits that status.

**What the remaining statements say.** On $sr$ vertices the count of all pairs gives $X+2\Sigma=sr(s-2)$, where $\Sigma$ is the total surplus of the other hues over $r\binom s2$ each. So $M(5;22)$, $M(6;12)$, $M(7;2)$ concern sets with at most 261, 306 and 351 edges of hue $a$ on 50, 60 and 70 vertices, and $\Sigma\ge64$, $114$, $174$.

**Limits.** Corollaries 19 and 20 are statements about order ten. For general $r$, Proposition 18 needs $s\ge r/2$, so the stops below $r/2$ still need $S(s)$ from another source. The witnesses recorded in `four-row-descent.md` for the twelve profiles with $k=4$ at order ten have $X\ge40$, so they lie outside the range that order ten needs.

**Internal review, 23 November 2026 (Section 11).** I checked Lemma 17, Proposition 18 and Corollaries 19 and 20 against the definitions in Section 6 and the order-ten quartet exclusions. The finite check quoted in the proof of Lemma 17(i) covers only orders through forty. The following calculation supplies the stated quantifier. Put $n=(s-1)r+1$ and $2A_0=r(n+r-s+1)$. The displayed deletion bound leaves at most $A_0+t(2r-1-t)/2$ edges on $n+t$ vertices. For $t\ge1$,
$$
(2r-1-t)n(n-1)\le2(r-1)n(n-1)<2A_0(2n+t-1),
$$
since $(r-1)(n-1)<2A_0$ and $2n+t-1\ge2n$. Thus the average on an $n$-set is strictly less than $A_0$. For the least-hue sampling in Corollary 19 the same calculation uses $n=sr+1$ and $2A_0=r(n+r-s)$, including the initial 91-set at ten. Within that set the second sampling bounds the number of edges on 81 vertices by $460\binom{81}{2}/\binom{91}{2}<405$.

In Lemma 17(ii) the closed target neighborhood has exactly eleven points at order ten, and all nine other hues must occur among the ten neighbors. The loss of at least eighteen units is valid. The four bounds in Corollary 19 are therefore 32, 22, 12 and 2. For the first bound ten disjoint independent quartets imply $k\le3$ when $m\le2$, and the earlier inequality gives the same bound for $m\ge3$. The order-ten certificates exclude every such profile. This establishes $M(4;32)$ and leaves the three sufficient budgeted statements listed in Corollary 20. The review is internal.

**Companion terminal check, 23 November 2026.** A local balanced coloring on 28 vertices has 126 target edges, target independence three and target clique number nine. The proposed 28-vertex lower bound of 134 requires additional hypotheses. The example cannot extend to 29 vertices while preserving both target parameters. The August 29-vertex terminal is still open here. [Construction and checks](order-ten-terminal.md)

## 12. Order ten

The second seat wrote this section on 24 November 2026. The first seat's internal review and separate replay appear at the end. External mathematical review is pending.

**Theorem 21.** Every coloring of the edges of $K_{101}$ with ten colors has eleven vertices that miss a color.

The proof uses Lemma 6, the stops and edge caps of Proposition 7, Lemma 9, Theorem 16, $P(4)$ at order ten, and Brouwer's theorem. It does not use the four-row certificates or Section 11, although its numbers agree with both. The deletion count and the degree-nine premium below are those of the August note on the outer closure at order ten; what is new is that the premiums are applied at every step.

Fix $r=10$, a balanced coloring and a hue $a$. Call a vertex set *admissible of type $(s,n)$* if it has $n$ vertices, $a$-independence at most $s$, and no $a$-clique of size ten. Let $f(s,n)$ be the least number of $a$-edges on such a set, and $f(s,n)=\infty$ if none exists. Let $N(s)$ be the largest $n$ for which one exists. Then
$$
 N(1)=9,\qquad N(2)\le19,\qquad N(3)\le29,\qquad N(4)\le40,
$$
by Lemma 9, Theorem 16 and $P(4)$. For the last: on 41 vertices every degree is at least eleven by Theorem 16, so there are at least 226 edges of $a$, while each other hue has at least $p_{10}(41)+3=67$ edges by Brouwer, which leaves at most $820-603=217$.

For an admissible set $U$ of type $(s,\cdot)$ let $\tau_s(U)$ be the least size of a vertex set meeting every $a$-independent $s$-set of $U$. Deleting such a set leaves independence at most $s-1$, so
$$
 \tau_s(U)\ge|U|-N(s-1).                                           \tag{7}
$$

**Lemma 22 (one deletion step).** Let $R$ be admissible of type $(s+1,n)$ and let $x$ have least degree $d$ in $R$. Put $A=N_a(x)$ and $U=R\setminus N_a[x]$. Then $U$ is admissible of type $(s,n-1-d)$, and
$$
 e_a(R)=e_a(U)+d+\binom d2+m+h ,
$$
where $m$ is the number of pairs in $A$ not of hue $a$ and $h\ge0$. Moreover, with $\tau=\tau_s(U)$:

1. $e_a(R)\ge\lceil nd/2\rceil$.
2. If $d=9$, then $m\ge1$ and $m+h\ge\tau-1$.
3. If $d=10$, then $m\ge9$ and $m+h\ge2\tau-6$.
4. If $d\ge11$, then $m\ge9(d-9)$.

*Proof.* Adding $x$ to an independent set of $U$ keeps it independent, so $U$ has independence at most $s$. For $v\in A$ let $S_v=N_a(v)\cap U$ and let $j(v)$ be the number of pairs at $v$ inside $A$ that are not of hue $a$. The degree of $v$ in $R$ is $1+(d-1-j(v))+|S_v|\ge d$, so $t_v=|S_v|-j(v)\ge0$. Put $h=\sum_vt_v$. The edges of $R$ outside $U$ number $d+(\binom d2-m)+\sum_v|S_v|=d+\binom d2+m+h$. Part 1 is the degree sum.

Let $uv$ be a pair in $A$ not of hue $a$. If an independent $s$-set $I\subseteq U$ met neither $S_u$ nor $S_v$, then $I\cup\{u,v\}$ would be independent of size $s+2$ in $R$. Hence
$$
 j(u)+j(v)+t_u+t_v=|S_u|+|S_v|\ge\tau .                              \tag{8}
$$
For $d=9$: $A\cup\{x\}$ is not a clique of size ten, so $m\ge1$. Take such a pair $uv$. The pairs counted by $j(u)$ and $j(v)$ are among the $m$ pairs, and only $uv$ is counted twice, so $j(u)+j(v)\le m+1$. Then (8) gives $h\ge\tau-m-1$.

For $d=10$: $A\cup\{x\}$ has eleven vertices and sees the nine other hues, and every pair at $x$ has hue $a$, so $m\ge9$. The pairs not of hue $a$ do not all pass through one vertex $c$, since $A\setminus\{c\}$ with $x$ would be a clique of size ten. A graph with nine or more edges and no vertex on all of them has two disjoint edges $u_1v_1$, $u_2v_2$. Among these four vertices let $i\le6$ pairs be not of hue $a$ and let $o$ such pairs leave the four. Then $j(u_1)+j(v_1)+j(u_2)+j(v_2)=2i+o\le m+i\le m+6$. Adding (8) for the two pairs gives $h\ge2\tau-m-6$.

For $d\ge11$: $A\cup\{x\}$ has $d+1$ vertices, so each other hue has at least $d-9$ edges on it, all inside $A$. ∎

Write $\rho(d,\tau)$ for the resulting lower bound on $e_a(R)-e_a(U)$:
$$
 \rho=\tbinom{d+1}2\ (d\le8),\quad
 \rho=45+\max(1,\tau-1)\ (d=9),\quad
 \rho=55+\max(9,2\tau-6)\ (d=10),\quad
 \rho=\tbinom{d+1}2+9(d-9)\ (d\ge11).
$$

**Static floors.** Turán gives $f(s,n)\ge p_s(n)$. If $n>9s$ the set is not covered by $s$ cliques, and Brouwer gives $f(s,n)\ge p_s(n)+\lfloor n/s\rfloor-1$. In particular $f(2,19)\ge81+8=89$ and $f(3,28)\ge125$. Every $(n-1)$-subset of an admissible set is admissible, so $f(s,n)\ge\lceil nf(s,n-1)/(n-2)\rceil$.

**The ladder.** For each cell $(s+1,n)$ take the minimum over the least degree $d$ of
$$
 \max\bigl(\lceil nd/2\rceil,\ f(s,n-1-d)+\rho(d,\tau)\bigr),\qquad \tau=\max(0,\,n-1-d-N(s-1)),
$$
omitting degrees for which $n-1-d>N(s)$, and using $\tau=0$ when $N(s-1)$ is not known. The checker evaluates every degree of every cell. The cells that decide the result, with the degree that attains the minimum:

- $f(3,29)\ge143$. Degree at most eight leaves twenty non-neighbors, more than $N(2)$. Degree nine gives $89+45+9$, with $\tau\ge19-9$. Degree ten or more gives at least 145.
- $f(4,39)\ge195$. Degree nine gives $143+54=197$. Degree ten or more gives $\lceil390/2\rceil$.
- $f(4,40)\ge212$. Degree at most nine leaves thirty non-neighbors. Degree ten gives $143+55+14$, with $\tau\ge29-19$. Degree eleven gives 220.
- $f(5,49)\ge245$, $f(5,50)\ge264$. At 50 vertices degree ten gives $195+55+14$ and degree nine gives $212+55$.
- $f(5,51)\ge281$. Degree at most nine leaves 41 non-neighbors, more than $N(4)$. Degree ten gives $212+55+16=283$, with $\tau\ge40-29$. Degree eleven or more gives $\lceil561/2\rceil=281$.
- $f(6,60)\ge312$ and $f(6,61)\ge332$.
- $f(7,70)\ge358$ and $f(7,71)\ge376$.
- $f(8,80)\ge404$ and $f(8,81)\ge422$.
- $f(9,91)\ge468$.

**Proof of Theorem 21.** Suppose a balanced coloring of $K_{101}$ exists and let $a$ be a least hue, with at most 505 edges. Follow the proof of Proposition 7. It produces, for some $1\le s\le9$, an admissible set of type $(s,10s+1)$ with at most $505-45(10-s)$ edges: the set left when the removal of cliques stops, or, if $Y$ has no clique of size ten, a subset of $Y$ with 91 vertices. When the vertex $v$ has degree below nine, a subset with at most the average number of edges is used, and the checker of Section 6 confirms that the cap is no larger. The caps are
$$
 100,\ 145,\ 190,\ 235,\ 280,\ 325,\ 370,\ 415,\ 460\qquad(s=1,\dots,9).
$$
For $s\le4$ no admissible set of type $(s,10s+1)$ exists. For $s=5,\dots,9$ the ladder gives at least $281,\ 332,\ 376,\ 422,\ 468$ edges. Each exceeds its cap. ∎

**Remarks.**

- The margin at $s=5$ is one edge: 51 vertices of degree at least eleven have at least 281 edges, against a cap of 280.
- Without $N(4)$ the floors at the last four stops are $327$, $373$, $419$, $465$, the values recorded in the August outer closure. That closure assumed a 29-vertex floor of 153. With the premiums of Lemma 22 at every step the ladder needs only $f(3,29)\ge141$, and Lemma 22 gives 143.
- Removing either premium, or the bound $N(3)\le29$ of Theorem 16, makes the ladder fail at every stop from five on. Theorem 16 is the input to check first.
- The August ledger records a balanced coloring on 28 vertices with 125 edges of the target hue, which equals the floor $f(3,28)\ge125$, and the coloring of `order-ten-terminal.md` has 126. So the rules are not too strong at that cell. The second seat rebuilt the 126-edge coloring from its description and confirmed its parameters; the 125-edge one was not re-examined.
- The three statements left open by Corollary 20 follow: $f(5,50)\ge264$, $f(6,60)\ge312$ and $f(7,70)\ge358$ exceed 261, 306 and 351.
- At other orders the same ladder, with $N(3)=3r-1$ from Section 8 and $N(4)$ from the four-row results, does not close. At order eleven every stop closes except $s=5$, where 56 vertices get a floor of 336 against a cap of 341. At order twelve the stops $s=5,6,7,8$ are short by 11, 2, 1 and 0 edges. From order thirteen on every stop from $s=5$ is open and the gap grows. `ladder_other_orders.py` prints these.

**Internal review of Section 12, 24 November 2026.** I re-derived Lemma 22 and the outer sampling step. For a missing pair inside the neighborhood, the union of its two target neighborhoods in the residual set meets every independent $s$-set there. For two disjoint missing pairs, the sum of their four internal missing degrees is at most $m+6$, since just the pairs inside the four endpoints can be counted twice. The required disjoint pairs exist at degree ten because a pairwise-intersecting family of graph edges is a star or lies on three vertices. Nine missing pairs exclude the latter, and a common center would give a forbidden target ten-clique. At higher degrees each other color has a vertex cover of size at least $d-9$ on the closed neighborhood, and hence at least as many edges. Only the upper bound $N(1)\le9$ is needed for a fixed hue.

I checked the input bounds from Lemma 9, the previously reviewed Theorem 16, and its consequence $P(4)$. In particular a putative admissible 41-set has minimum degree at least eleven by Theorem 16. Every other hue has independence at most ten and clique number at most four in it. Brouwer then gives at least 67 edges per other hue, forcing at most 217 target edges against at least 226. For the outer step, removing the minimum-degree neighborhood and then $9-s$ full cliques leaves $10s+1+t$ vertices with at most $505-\binom{10-t}{2}-45(9-s)$ target edges. Sampling a $(10s+1)$-set meets the stated cap for all nine stops and all ten possible $t$.

I wrote a second checker that starts at an edge budget, branches over every least degree compatible with the degree sum, and descends until the order or edge budget is impossible. It imports no code from the original ladder and uses neither its static Brouwer floors nor its averaging recurrence inside the ladder. With the four input order bounds, it independently recovers the floors 281, 332, 376, 422 and 468 at the five remaining stops. The smallest margin is one edge. I found no gap in this section. The separate 29-vertex lower bound of 153 is unnecessary for this proof. The order-ten claim is independent of the sunflower theorem and the large-order cutoff. The August 2026 Terpstra release already claimed this fixed order; it was not replayed in this review. [Independent budget replay](replay_ten_deletions.py) · [Earlier public release](https://github.com/terpstra-research/erdos-617-r10-r11/releases/tag/v0.1.1)

**Order-eleven continuation, 24 November 2026.** The 56-vertex stop identified above now has a floor of 342 against its cap of 341. The companion argument uses the order-eleven four-row census and counts the exterior vertices that can join the low-degree portions of five private cliques. All ten stops are excluded. Two internal arithmetic replays agree. The same argument gives a conditional theorem at the odd midpoint. [Proof and review status](midpoint-row-excess.md)
