# Four rows at orders fifteen and sixteen

Robert Sneiderman’s research notes · 23 November 2026

**Theorem.** Suppose every $r+1$ vertices of an $r$-edge-colored complete graph see every color. For $r\ge15$, any $4r$ vertices with target independence at most four contain a target clique of size $r$. In the project's notation this is $M(4)$. The earlier proof covers $r\ge17$. The two new orders use the counting certificates below. The regular case is also impossible at $r=13,14$. The new results await independent review. [Earlier four-row proof](four-rows.md) · [Three-row input, including order ten](overfull-core.md) · [Exact replay](verify_four_row_descent.py) · [Certificates and surviving profiles](four-row-descent-certificates.json)

## 1. The nineteen vertices cannot extend to the order-sixteen profile

At $r=16$ take the profile $(0,0,0,7),\ k=7$. Section 6 of the earlier note forces a set $B$ of nineteen vertices. An eight-vertex target clique is completely target-joined to eleven vertices. The target graph on those eleven is the union of four disjoint cliques of sizes $3,3,3,2$. Each of the other fifteen colors is a three-edge matching on $B$.

Let $L$ be any one of the three remaining target cliques of size fifteen. Fix a nontarget color $c$. The points of $B$ sending no $c$-edge to $L$ form a $c$-clique, since $L$ together with any two of them must see $c$. A matching has clique number two. Hence at least seventeen $c$-edges cross from $L$ to $B$. All colors together leave at most $15\cdot19-15\cdot17=30$ target edges across.

Every $x\in L$ must hit an entire one of the four exterior cliques in the target. Otherwise a missed representative of each, together with $x$, is an independent five-set. Each $x$ therefore spends at least two target edges. The budget of thirty forces each to hit the unique group of size two. Either point of this group extends $L$ to a target $K_{16}$. This rules out every labeling with the prescribed structure.

## 2. Degrees, color budgets and the regular branch

Suppose a violating $4r$-set $W$ exists, with $10\le r\le16$. Write $H$ for the graph of all nontarget edges. It is $K_5$-free and $\alpha(H)\le r-1$. The three-row theorem gives $q(v)=d_a(v)-r\ge0$. Set $X=\sum q(v)$, $\eta_c=e_c(W)-6r$, and $\Sigma=\sum_{c\ne a}\eta_c$. Then $X+2\Sigma=8r$. Let $k$ be the least total $q$ on a target-independent quartet, and let $m=\min_{c\ne a}\eta_c\le4$. As in §1 of the earlier proof, there are $h=r$ disjoint such quartets if $m\le2$, and at least $h=r-m$ otherwise. Hence
$$
 (r-1)m\le\Sigma\le\lfloor(8r-hk)/2\rfloor,\qquad q(v)\le X-(h-1)k .
$$
For $m=3$, $4(r-3)>2r+6$ for $r\ge10$. For $m=4$, $4(r-4)>8$. Thus $m\ge3$ implies $k\le3$, and $k\le8$ always. If $k=8$, every other color is exactly a partition into $r$ cliques of size four, $\Sigma=0$, and $q=2$ everywhere. Equality in the complementary Turán bound gives these partitions.

**A bound at small surplus.** For another color put $D_c(v)=(3-d_c(v))_+$. Section 5 of the earlier proof gives $\eta_c\ge3D_c(v)$ and $q(v)\le2+\sum_cD_c(v)$. For $m<3$, $\eta_c-m\ge(3-m)D_c(v)$ as well, since $\eta_c\ge m$ and a positive deficit is integral. These and the displayed bound give a uniform upper bound $Q$ on $q$ for each possible $(m,\Sigma)$. On an interval of possible surpluses we take the maximum of each upper bound after evaluating the individual choices.

A color with any deficiency satisfies the stronger global estimate
$$
 \sum_v D_c(v)\le3(\eta_c-3).
$$
In that color repeatedly delete the closed neighborhood of a vertex of minimum degree $3-h<3$ in the remaining graph. At each deletion $h\in\{1,2,3\}$. The $4-h$ deleted vertices cost at least $\binom{4-h}2$ edges, by minimum degree, and account for at most $(4-h)h$ units of original deficiency. After $t$ deletions the remainder has independence at most $r-t$, order $4(r-t)+\sum h$, and clique number at most four. It cannot be covered by $r-t$ cliques. Brouwer's Theorem 2 therefore gives at least $6(r-t)+4\sum h+3$ edges there, using the tangent to the complementary Turán count at $4(r-t)$. The remainder is nonempty and has $r-t\ge1$ whenever a deletion occurs. Restoring the deleted edges gives $\eta_c\ge3+\sum \binom{h+1}{2}$. Since $(4-h)h\le3\binom{h+1}{2}$, the claim follows. In particular $Z_2=\sum_v(q(v)-2)_+\le3(\Sigma-3)_+$. [Brouwer, Theorem 2](https://ir.cwi.nl/pub/6791/6791D.pdf#page=4)

If $\Sigma\le8$, then $Q\le4$ and at most two vertices can have $q\ge4$. With one deficient color, any such vertex has degree at most one in it. A deletion of degree zero costs at least nine surplus in total, and two deletions of degree at most one cost at least nine. Thus all initially low vertices are removed by the first such deletion, of size at most two. With two deficient colors, both have surplus exactly four. Equality in the deletion count makes the three vertices at its first degree-two deletion an isolated triangle in each color, and outside it there are no deficient points. Two triangles of different colors meet in at most one vertex. This proves the claim. When $\Sigma<4$ every $q\le2$. When $\Sigma<6$ every $q\le3$.

**The strict-degree condition at fourteen and fifteen.** If $Q\le2$, a maximal $K_5$-free supergraph $H^*$ of $H$ has $\delta\ge3r-3$. A triangle-free part of $H^*$ is triangle-free in $H$ and has size at most $2r-1$ by the two-row theorem $M(2)$. Thus $H^*$ cannot be the join of two triangle-free graphs. At $r=14,15,16$ we have $\delta>11(4r)/16$. In the nonjoin case Lyle's Theorem 4 gives an independent set of size at least
$$
 \min\{3(3\delta-2n),\ (20\delta-25n/2)/6,\ 2(2\delta-n)/3\},\qquad n=4r .
$$
At the respective lower degrees this minimum is $40/3,15,50/3$. Rounding up gives a target clique of size at least $r$ in $H$'s complement. This excludes every $k=8$ profile at these three orders. [Lyle, Theorem 4](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v21i2p38/pdf/#page=3)

## 3. Constraints on individual vertices

Fix a minimum quartet with roots $x_i$. Its private target cliques $C_i$ have sizes $s_i=r-1-b_i$, sorted by increasing deficit $b_i$. There are $P=4+\sum b_i$ exterior vertices. For each such $y$ let $J_y$ be the roots it hits, let $p_i$ be its misses in each incident row, and put $H_i=s_i-p_i$ there. Use $p_i=r,H_i=0$ on an unhit root. Thus $H_i$ is a lower bound on actual hits even on an unhit row. The incidence identity is $\sum_y(|J_y|-2)=k-\sum b_i$.

**A floor on every $r$-set.** For any $r$-set $B$, its complement contains a target-independent quartet $I$ by $M(3)$, and $I$ dominates $B$. The $j$ largest target degrees into $B$ from $I$ sum to at least $j\lfloor r/4\rfloor+\min(j,r\bmod4)$. On $B$ plus those $j$ points, each other color needs at least $j$ edges. Subtracting the available pairs gives
$$
 e_H(B)\ge f_0=\max_{1\le j\le4}
 \left(j\lfloor r/4\rfloor+\min(j,r\bmod4)-\binom{j+1}{2}\right).
$$
This gives $3,3,3,4,5,6,6$ at orders ten through sixteen. Use the larger of $f_0$ and the earlier floor $r-7$ whenever $r>4(1+\lfloor\Sigma/3\rfloor)$. Write $f$ for the resulting floor.

**Common target neighbors.** Put $d=1$ when $2Q<r-4$, and $d=0$ otherwise. Every triangle-free induced subgraph of $H$ has at most $2r-1-d$ vertices. The bound for $d=0$ is $M(2)$. If such a set $T$ had size $2r-1$, $H[T]$ would be nonbipartite since its independence is at most $r-1$. It has at least $(r-1)^2$ edges, by the $r-1$ other colors. The five-cycle argument in §8 of the three-row proof gives an edge $yz$ with $d_{H[T]}(y)+d_{H[T]}(z)\le r+2$. Their target degrees in $T$ sum to at least $3r-6$. Their common $H$-neighbors outside $T$ induce a triangle-free graph and number at most $2r-1$ by $M(2)$. Among the $2r+1$ outside points at least two further target incidences are needed. Hence $q(y)+q(z)\ge r-4$, impossible if $d=1$.

For any nontarget edge $uz$, inclusion-exclusion now gives
$$
 |N_a(u)\cap N_a(z)|\le 1+q(u)+q(z)-d.
$$
A vertex partly hitting a target clique therefore hits at most $\mu=1+2Q-d$ of it. When $s_i>\mu$, all fully joined vertices on row $i$ form a target clique with it and number at most $b_i$. For $\Sigma\le8,d=1,s_i>6$ the same argument applied to fully joined points of excess at most three allows at most $b_i$ of those, plus the at most two exceptions from §2.

**Lists and rectangles.** Use the cut, transversal and two-root tests of §§3–5 of the original proof, with the new $Q,f$. For a two-root exterior vertex the two missed lists are completely joined. Consider row $i$, opposite list size $p_j$, and $u=b_i+1$. Any $u$ opposite missed points together with $C_i$ form an $r$-set with at most $u(s_i-p_i)$ nontarget edges. With the exterior vertex and $u-1$ opposite points the analogous maximum is $p_i+(u-1)(s_i-p_i+1)$. Whenever the required opposite points exist, each maximum is at least $f$. With all $p_j$ opposite points the necessary bound is $p_j(s_i-p_i)\ge(r-1)(p_j-u)$.

For $k=8$ we have $\mu=4$ at all orders considered. Each vertex of $C_j$ misses root $x_i$ for $i\ne j$ and therefore has at most four target neighbors in $C_i$. In any two missed lists of positive sizes the number of target pairs is consequently at most $4\min(p_i,p_j)$. Use this together with the earlier cut bound in the transversal union bound, including its opposite-pair correction for four lists. In particular a two-root vertex with nonempty lists has both lists of size at most four.

## 4. Simultaneous inequalities and the certificates

The unknowns are nonnegative counts of exterior types, the six actual target cut sizes $E_{ij}$, and $D_i=\sum_{v\in C_i}q(v)$. The following are necessary bounds. Denote the number hitting root $i$ by $n_i$, let $B=\sum b_i$, and call a vertex *ordinary on $ij$* if $J_y=\{i,j\}$. In the regular branch every vertex has excess exactly two.

- **Row degrees.** $n_i=b_i+2+q(x_i)$. Replacing $x_i$ by any other member of $C_i$ preserves independence, so $s_iq(x_i)\le D_i\le s_iQ$. Counting target edges leaving the row gives $\sum_yH_i(y)+\sum_{j\ne i}E_{ij}\le s_i(b_i+2)+D_i$. If $s_i$ exceeds the number of possible vertices of excess at least four, then $q(x_i)\le3$.
- **Long rows and colors.** For a long row $L$ of size $r-1$, take any disjoint set $A$ of target independence at most $g$. Points of $A$ missing color $c\ne a$ into $L$ form a $c$-clique of size at most $g$. Subtracting the necessary edges of all other colors gives at most $g(r-1)$ target edges across. Taking all outside points yields $D_L\le2(r-1)$, hence $q(x_L)\le2$. For any set $U$ of roots take as $A$ the private rows indexed by $U$ other than $L$, together with the exterior types satisfying $J_y\subseteq U$. They avoid the omitted roots and have target independence at most $|U|$. For $U$ equal to all roots use $\alpha_a(W)\le4$. In the earlier singleton argument two distinct exterior vertices with positive opposite misses would cover at most six points of $L$ when their opposite witnesses differ, or at most $r-1-f+3$ when they agree. Thus at most one exists if $f>3$ in the orders under consideration.
- **Pairs of rows.** The union of $C_i,C_j$ and all ordinary vertices on $ij$ avoids the other two roots, so its target independence is at most two. The triangle-free bound gives at most $m_{ij}=1+b_i+b_j-d$ ordinary vertices. Applied to the set avoiding $i,j$ instead, the weaker $d=0$ bound gives $\#\{y:J_y\cap\{i,j\}\ne\varnothing\}\ge3+b_i+b_j$. Each ordinary rectangle costs $p_i p_j\le E_{ij}$, hence their costs sum to at most $m_{ij}E_{ij}$. Always $E_{ij}\le r-1+b_ib_j$, and every type hitting both roots requires $E_{ij}\le b_ib_j+p_i+p_j$.
- **Total excess.** A lower bound for $q(y)$ is the maximum of $0,\sum_iH_i-r$, and $H_i-1-Q$ over incident, partly hit rows $i$, by the common-neighbor inequality. Call this cost $w_y$, and take $w_y=2$ in the regular case. Then $\sum_yw_y+\sum_iD_i\le X$. For $q_0=2,3$ and for any row index set $I$, $\sum_y(w_y-q_0)_++\sum_{i\in I}D_i\le Z_{q_0}+q_0\sum_{i\in I}s_i$, where $Z_{q_0}$ may be bounded by $4r(Q-q_0)_+$, the bound on $Z_2$, and for $q_0=3,\Sigma\le8$ the exceptional-vertex bound.

**Subset counts.** Let $p_g(z)$ be the least number of edges on $z$ vertices in a graph of independence at most $g$. Write $A(n)=\binom n2-(r-1)p_r(n)$, using $A(r)=\binom r2-f$. For a nonempty row index set $I$, put $V=\sum_{i\in I}s_i,\ T=\sum_{i\in I}\binom{s_i}2,\ H_I=\sum_{i\in I}H_i$. Counting on those rows plus all exterior points gives
$$
 \sum_y H_I(y)+\sum_{\{i,j\}\subseteq I}E_{ij}\ \le\ A(V+P)-T-p_4(P).
$$
A pool of exterior vertices hitting only roots in a set of size $g$ has target independence at most $g$. On a subset of size $z$ in such a pool the sum of row loads is at most $A_z=A(V+z)-T-p_g(z)$, after discarding the nonnegative inter-row edges.

Here is the improvement used for a single row of size $s=r-1-b$. Write $M$ for the *actual* total cross misses of the chosen $z$ points and $N$ for their internal nontarget edges. The set requires $M+N\ge F$, where $F=f$ at $z=b+1$, and otherwise $F=\max(0,(r-1)(z-b-1))$. For each internal nontarget pair with individual miss counts $m_y,m_w$,
$$
 s-1+d\le m_y+m_w+q(y)+q(w).
$$
Summing over the $N$ pairs gives
$(s-1)N\le(z-1)M+z(z-1)Q$. For $t\in\{2,3,Q\}$ with $t\le Q$, it also gives
$(s-1+d-2t)N\le(z-1)(M+Z_t)$, with $Z_Q=0$. Each inequality with positive coefficient of $N$, together with $M+N\ge F$, gives a rounded-up lower bound for $M$. Tighten $A_z$ by $zs-M_{\min}$. Averaging over smaller subsets tightens it further by $\lfloor z A_u/u\rfloor$ for $1\le u<z$. For any load threshold $L$, applying the resulting bound to precisely those pool points with $H_I>L$ gives
$$
 \sum_{\text{pool}}(H_I-L)_+\ \le\ \max_{0\le z\le P}(A_z-zL).
$$

For pool points with at most $t$ misses on one incident row, $M\le zt$. A nontarget pair requires $q(y)+q(w)\ge a=s-2t-1+d$. Hence $N\le\binom z2-p_g(z)$, and $N=0$ when $a>2Q$. If $\Sigma\le8$, put $h=\min(z,\#\text{possible exceptional points})$ using the upper bound in §2. For $a>6$ every such pair meets an exception, and for $a>Q+3$ both ends must be exceptions. Use respectively $N\le\binom z2-\binom{z-h}2$ and $N\le\binom h2$. As soon as $zt+N_{\max}<F$, the pool has at most $z-1$ points of that type.

**Verification.** Each negative leaf gives positive integer multipliers. Their combination has nonnegative coefficient on every allowed type and every one of the ten auxiliary variables, with a strictly negative right side. The checker uses unbounded integers and enumerates every type. A split exhausts either the integer $\Sigma$, the actual integer $E_{ij}$, or the integer number of vertices of a specified type or incidence pattern. A cut branch drops a type only when its required interval for that cut is disjoint from the branch. An empty set of types contradicts $P>0$. An exact witness at a smaller order supplies a common denominator for its counts, edges and degree sums. It only establishes feasibility of the stated counting constraints. Assigning actual colored edges to vertices is a further condition.

## 5. Rerooting excludes the regular case at thirteen

Suppose $r=13,\ k=8$. The regular-case list bound from §3 and the inequalities in §4 exclude 51 of the 53 sorted deficit profiles. The only possibilities are $(0,0,0,8)$ and $(0,0,4,4)$. The rerooting argument uses only the 51 exclusions. Every independent quartet is minimum because $q\equiv2$, so the same conclusion applies after changing the four roots.

Both profiles have total deficit eight. The incidence identity forces *every* exterior vertex to hit exactly two roots. Consequently a vertex outside any quartet has one or two target neighbors in it. Fix a vertex $v$. For each nontarget color $c$, write $I_c(v)$ for the block of its four-clique partition containing $v$, and $b(v,c)$ for the deficit of the private clique of root $v$ using that quartet. Exactly $4+b(v,c)$ neighbors of $v$ hit a second root there. Each hits exactly one such root.

In the $c$-partition, the $r+2$ target neighbors of $v$ avoid its own block and meet each other block once or twice. They therefore determine exactly three edges of color $c$. In particular $e_H(N_a(v))=3(r-1)$. Count target paths $v,y,w$ whose endpoint $w$ is a nontarget neighbor of $v$. For each $w$, its edge to $v$ specifies its unique color $c$ and places it in $I_c(v)$. Counting the paths by this color and then by their middle vertices gives
$$
 \sum_{c\ne a}(4+b(v,c))
   =(r+2)(r+1)-2e_a(N_a(v))=2e_H(N_a(v))=6(r-1).
$$
Thus every vertex has average deficit two across its twelve choices of color. The only possible individual deficits are $0,4,8$. Every vertex has deficit zero at least once, so lies in a target $K_{12}$.

Two distinct target $K_{12}$'s meet in at most four vertices. Indeed, any point in their difference misses some point of the other clique, since a complete join to that clique would give a $K_{13}$, and the common-neighbor bound is four. If they shared a vertex $v$, both would lie in its closed target neighborhood of size sixteen, forcing an intersection of size at least eight. Thus these $K_{12}$'s are disjoint. They cannot cover 52 vertices. This contradiction eliminates $k=8$ at thirteen.

## 6. The surviving profiles

Write a profile as four sorted deficit digits followed by its quartet excess $k$. At order sixteen the original §4 threshold leaves 65 of the 109 profiles with $k\le7$. All 65 keys are archived under `original16`. Applying the original §5 row, root, singleton, miss and arity inequalities before any rectangle split leaves precisely these twelve. The archived rational witnesses and integer exclusions reproduce this intermediate count.

- At $k=6$ the deficits are `0024`, `0033`.
- At $k=7$ they are `0007`, `0016`, `0024`, `0025`, `0033`, `0034`, `0115`, `0124`, `0133`, `0223`.

The new constraints exclude all twelve. At sixteen there are 44 threshold exclusions and 65 further certificates, each a single leaf. At fifteen the threshold excludes 24 profiles and the certificates exclude the remaining 85 in 114 leaves. In both counts the degree argument has already excluded the 53 formal profiles with $k=8$. Together with the earlier proof from seventeen, this proves the stated $M(4)$ theorem.

For all seven orders start with the same 162 formal profiles. The table counts those still open after the stated exclusions. A *shared-cut witness* is one rational assignment whose six cut sizes satisfy the individual lower and upper bounds of every exterior type used. An *integral witness* here has integer values for all the recorded variables and meets the shared-cut bounds. The integral column counts the witnesses archived here. Even an integral witness leaves the individual edges and their colors to be assigned.

| Order | $k=4$ | $k=5$ | $k=6$ | $k=7$ | $k=8$ | Total | Shared-cut | Integral |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 12 | 18 | 27 | 38 | 52 | 147 | 147 | 90 |
| 11 | 11 | 18 | 27 | 37 | 35 | 128 | 128 | 58 |
| 12 | 5 | 18 | 27 | 38 | 14 | 102 | 102 | 34 |
| 13 | 0 | 4 | 25 | 36 | 0 | 65 | 65 | 12 |
| 14 | 0 | 0 | 12 | 5 | 0 | 17 | 17 | 5 |
| 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

The following lists specify every open profile. Write $\mathcal B_k$ for all sorted nonnegative four-tuples of sum at most $k$. “All” means $\mathcal B_k$. An omitted $k$ has no survivors. Leading zeros are significant. The command `python3 -B verify_four_row_descent.py --list` prints every tuple individually.

**Order 10.**

- $k=4$. All.
- $k=5$. All.
- $k=6$. All.
- $k=7$. All.
- $k=8$. All except `1112`.

**Order 11.**

- $k=4$. All except `0003`.
- $k=5$. All.
- $k=6$. All.
- $k=7$. All except `1111`.
- $k=8$. All except `0001`, `0005`, `0014`, `0015`, `0113`, `0114`, `0115`, `0122`, `0222`, `1112`, `1113`, `1114`, `1115`, `1122`, `1133`, `1222`, `1223`, `2222`.

**Order 12.**

- $k=4$. `0000`, `0001`, `0011`, `0111`, `1111`.
- $k=5$. All.
- $k=6$. All.
- $k=7$. All.
- $k=8$. `0000`, `0003`, `0004`, `0007`, `0008`, `0012`, `0013`, `0017`, `0022`, `0034`, `0035`, `0111`, `0112`, `1111`.

**Order 13.**

- $k=5$. `0002`, `0003`, `0012`, `0013`.
- $k=6$. All except `0033`, `1111`.
- $k=7$. All except `0000`, `1111`.

**Order 14.**

- $k=6$. `0003`, `0004`, `0005`, `0006`, `0013`, `0014`, `0015`, `0022`, `0023`, `0113`, `0114`, `0222`.
- $k=7$. `0007`, `0015`, `0016`, `0114`, `0115`.

In total, all 459 surviving profiles have a shared-cut witness.

**Scope.** At ten the only excluded weight-eight profile is $(1,1,1,2)$, and every profile with weight at most three is excluded. The order-ten reduction still needs $M(4),M(5),M(6),P(8)$. These results concern one target color on $4r$ vertices. The private unrestricted threshold for Erdős 617 remains $2^{146}$. [Reduction and reviewed three-row theorem](overfull-core.md) · [Unrestricted proof](weighted-width.md)

## Review note, 23 November 2026 (second seat)

This is an internal check by a second model seat working in the same project. It does not replace outside review.

**Scope read.** Sections 1 to 5 line by line and the checker `verify_four_row_descent.py` line by line. The certificates were replayed with that checker only. No independent replay was written this time, unlike for the earlier four-row note.

**Result.** No failing step found. Re-derived from the hypotheses:

- Section 1: the budget of thirty target edges between a long row and the nineteen vertices, and the forced complete join to the group of size two.
- Section 2: the bounds on $k$ and $m$; $\eta_c-m\ge(3-m)D_c(v)$; the deletion estimate $\sum_vD_c(v)\le3(\eta_c-3)$, including the three increments $1,3,6$ and the tangent form of Brouwer's bound; at most two vertices of excess four when $\Sigma\le8$; the strict-degree step.
- Section 3: the floor $f_0$, with values $3,3,3,4,5,6,6$; the bound $2r-1-d$ on triangle-free sets and the common-neighbor inequality; the three list tests for a two-root vertex; $\mu=4$ in the regular case.
- Section 4: every family of inequalities, namely row degrees, long rows and colors, pairs of rows, total excess, the subset counts, the single-row improvement, and the pools with few misses.
- Section 5: the path count $\sum_c(4+b(v,c))=6(r-1)$ and the disjoint cliques of size twelve.

**Checker.** Each named row in `inequalities` is one of the statements proved in Sections 2 to 4. A context takes maxima of $\Sigma$, $X$ and $Q$ over its interval and uses them only as upper bounds. The three kinds of split are exhaustive for integers, and a cut branch drops a type only when that type is incompatible with the branch.

**The outside theorem at orders 14 to 16.** Lyle's Theorem 4 is used inside its stated range, with $\delta/n=39/56,\ 42/60,\ 45/64$, all above $11/16$. At order 15 its minimum equals $r$ exactly, so the constants matter. Reading its proof, the middle term arises only when the largest triangle-free induced subgraph $S$ is not bipartite, and then $|S|\ge\tfrac54(2\delta-n)$. That is at least 28, 30 and 33 at orders 14, 15 and 16, above the bound $2r-1$ from the two-row theorem. So this case cannot occur here, and the other two terms give independent sets of size 15, 16 and 18 at these orders. The step does not depend on the middle term.

**Not examined.** The witness lists at orders 10 to 14 record open cases and are not claims.

**Use.** The exclusions at order ten of every profile with $k\le3$ are used in Corollary 20 of `overfull-core.md`, which closes the four-row part of the order-ten reduction.
