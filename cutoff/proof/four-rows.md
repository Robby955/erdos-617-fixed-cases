# Four rows in the Erdős–Gyárfás balanced coloring problem

Robert Sneiderman’s research notes · 23 November 2026

**Theorem.** Let $r\ge17$. In an edge coloring with $r$ colors, assume that every $r+1$ vertices see every color. Suppose a set $W$ of $4r$ vertices contains no five vertices pairwise avoiding color $a$. Then $W$ contains a clique of size $r$ in color $a$. This is $M(4)$ in the local reduction.

The proof uses the three-row theorem $M(3)$ for $r\ge11$. The argument at and above 28 uses 109 profiles and a bound monotone in the order. At orders 17 through 27, 226 integer certificates complete the finite calculation. All cases concern an arbitrary target color. The combinatorial proof is in this note and its cited prerequisite. The arithmetic can be replayed with standard-library Python. Independent mathematical review of this result is pending. [Three-row theorem, §8](overfull-core.md#8-three-rows-at-orders-eleven-and-above) · [Checker](verify_four_rows.py) · [Certificate data](four-row-certificates.json)

## 1. A minimum independent quartet

Suppose the theorem fails. All degrees and graphs below are induced on $W$. Write “target” for color $a$, and “independent” for a set avoiding the target. Every other color has independence number at most $r$, and its cliques have at most four vertices. The vertices outside the closed target neighborhood of any $v$ have target independence number at most three. By $M(3)$ there are at most $3r-1$ of them. In particular $q(v)=d_a(v)-r\ge0$. Also, every $3r$-subset contains an independent quartet.

Let $X=\sum q(v)$, $\eta_c=e_c(W)-6r$ for $c\ne a$, and $\Sigma=\sum_{c\ne a}\eta_c$. Turán gives $\eta_c\ge0$. Counting the edges of $K_{4r}$ gives

$$
             X+2\Sigma=8r.                                           \tag{1}
$$

Let $k$ be the minimum of $\sum_{v\in I}q(v)$ over independent quartets. Put $m=\min_{c\ne a}\eta_c$. Then $m\le4$ by (1). A color with surplus at most two partitions $W$ into $r$ monochromatic quartets by Brouwer's Theorem 2, since each covering clique has size at most four. We call such a partition a *factor*. Extra edges of that color between blocks are allowed. If $m\ge3$, Füredi's stability theorem applied to the complement of a least-surplus color gives $r$ parts with at most $m$ wrong-colored internal pairs altogether. If part $i$ has $t_i$ such pairs, deleting one endpoint of each leaves a monochromatic clique. Thus $4+t_i-|V_i|\ge0$. These deficits sum to $\sum t_i\le m$, so at least $r-m$ parts have deficit zero and contain disjoint quartets. Hence $(r-4)k\le X\le2r+6$ if $m\ge3$. This implies $k<5$ for $r\ge17$. If $m\le2$, the factor gives $rk\le X\le8r$. [Brouwer, Theorem 2](https://ir.cwi.nl/pub/6791/6791D.pdf#page=4) · [Füredi, Theorem 1](https://arxiv.org/abs/1501.03129)

The case $k=8$ would force $\Sigma=0$. Equality in Turán makes every other color exactly a union of $r$ copies of $K_4$. The graph of all nontarget pairs is then $K_5$-free and $3(r-1)$-regular. Its minimum degree is **strictly** greater than $7(4r)/10$ since $r>15$. The Brandt bound for $K_5$-free graphs gives an independent set of size at least $4r/4=r$, a target clique. One can apply Lyle's Corollary 5 to a maximal $K_5$-free supergraph, since adding edges preserves the degree lower bound and any resulting independent set remains independent in the original graph. Thus $0\le k\le7$. [Lyle, Corollary 5](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v21i2p38/pdf/#page=4)

## 2. What the other colors require on every set of size r

Let $B\subset W$ have size $r$. The complementary $3r$ vertices contain an independent quartet $I$. It dominates $B$ in the target color, so at most $3r$ pairs between $B$ and $I$ are nontarget. Each other color needs at least four edges on $B\cup I$. Indeed, deleting one endpoint of each edge of a color leaves an independent set in that color. At most six nontarget edges lie inside $I$. Therefore
$$
                    e_{\ne a}(B)\ge4(r-1)-3r-6=r-10.                \tag{2}
$$

There is a useful improvement when $r>4(1+\lfloor\Sigma/3\rfloor)$. Choose one factor for each color with surplus at most two, giving at least $r-1-\lfloor\Sigma/3\rfloor$ colors. If $B$ meets every block of every chosen factor, it meets each exactly once. Every vertex outside $B$ then has at least one edge into $B$ of each of those colors. Four outside vertices could cover at most $4(1+\lfloor\Sigma/3\rfloor)<r$ points of $B$ in the target color, contradicting domination by $I$. Hence a factor of some color $c$ has a block $I'$ disjoint from $B$, and another block has at least two points in $B$. The $r-2$ colors other than $a,c$ require $4(r-2)$ edges on $B\cup I'$. None are inside $I'$, at most $3r$ are across, and at least one nontarget edge of $B$ already has color $c$. This proves $e_{\ne a}(B)\ge r-7$.

In what follows $f$ is a lower bound from this section valid for **all** $r$-sets at once. In particular any outside vertex misses at least $f$ points of a target clique of size $r-1$.

## 3. Four private cliques and the edges forced between them

Choose a quartet attaining $k$, with roots $x_1,\ldots,x_4$. Let $C_i$ consist of $x_i$ and all vertices whose only target neighbor among the roots is $x_i$. It is a target clique, since two nonadjacent private neighbors together with the other three roots would be independent. Write $s_i=|C_i|=r-1-b_i$, with $0\le b_1\le\cdots\le b_4$. There are $P=4+\sum b_i$ exterior vertices. Every exterior vertex $y$ meets a set $J_y$ of $j_y\ge2$ roots. The number incident to root $x_i$ is $2+b_i+q(x_i)$. Summing these counts yields
$$
                  \sum_y(j_y-2)=k-\sum_i b_i.                     \tag{3}
$$
In particular $\sum b_i\le k$. Write $p_i=p_i(y)$ for the number of vertices missed by $y$ in an incident row. Then $0\le p_i<s_i$.

Let $E_{ij}$ be the number of target edges between rows $i,j$. Every other color needs at least $n-r$ edges on $n$ vertices by the endpoint deletion argument. Apply this first to the two rows and then to their union with a vertex $y$ incident to both. All nontarget edges lie across the rows or at $y$. Subtracting the two lower bounds from the available pairs gives
$$
                 E_{ij}\le b_i b_j+\min(r-1,p_i+p_j).             \tag{4}
$$

For each incident row choose one of its missed vertices. Unless a chosen pair is a target edge, these choices, $y$, and the unhit roots form an independent five-set. Thus when all lists are nonempty, uniform independent choices from the lists satisfy
$$
  1\le \sum_{i<j\in J_y}t_{ij},\qquad
  t_{ij}=\min\left(1,\frac{b_i b_j+\min(r-1,p_i+p_j)}{p_i p_j}\right).
                                                                    \tag{5}
$$
For four lists the events on opposite pairs are independent. Group the six pairs into three opposite pairs and sum the probabilities of the three unions. This gives the stronger necessary upper bound $\sum t_{ij}-\sum_{ij|hl}t_{ij}t_{hl}$ for coverage. Here $x+y-xy$ increases in each argument on $[0,1]$. An empty list blocks a transversal by itself.

For an exterior vertex with exactly two incident rows the missed lists are completely joined in the target. Their union is a target clique, so $p_i+p_j\le r-1$. If equality holds and both lists are nonempty, adding either root to that clique produces an $r$-set. Its nontarget edges are precisely the edges from that root to the opposite list, so both lists have size at least $f$. If $b_i=0$, then $p_i\ge f$. Whenever $p_j>0$ an element of the opposite list hits all $p_i$ elements but misses at least $f$ points in row $i$. Hence $2f>r-1$ forces $p_j=0$ in that case.

**Two rectangles on the same cut.** If the target cut between $C_i,C_j$ already contains a $t\times u$ rectangle, the additional rectangle required by any two-root vertex on these rows occupies with it at least
$$
          tu+p_i p_j-\min(t,p_i)\min(u,p_j)                       \tag{6}
$$
edges. This must fit (4). If the cut contains no such rectangle, every two-root vertex there has $p_i<t$ or $p_j<u$. Both alternatives refer to the same actual coloring. For example, at order 17, between two deficit-three rows a $2\times9$ and a $9\times2$ rectangle together require at least 32 target edges, against at most $16+9=25$.

## 4. Row capacity and the uniform proof from 28

Fix a row with deficit $b$ and $z$ exterior vertices incident to it. Write $F(z)=f$ for $z=b+1$, and $F(z)=\max(0,(r-1)(z-b-1))$ otherwise. The union requires at least $F(z)$ nontarget edges, by §2 at size $r$ and the edge floor for each other color above that size. Within the $z$ exterior vertices there are at most $\binom z2-T_4(z)$ nontarget edges, where $T_4(z)$ is the complementary Turán floor at independence four. The other nontarget edges are counted exactly by the sum of the $z$ miss counts. Thus at most $z-1$ incident vertices can have at most $L$ misses if
$$
                zL+\binom z2-T_4(z)<F(z).                         \tag{7}
$$

Use $f=r-10$ and choose an integer $L_i\ge-1$ for each row. Mark every exterior vertex having at most $L_i$ misses in an incident row $i$. The choice $L_i=-1$ marks none. Let $c_i$ be the marking cap from (7), or $P$ if it gives no restriction. If $U=P-\sum c_i>0$, at least $U$ vertices are unmarked. By (3), one of them hits at most $2+\lfloor(k-\sum b_i)/U\rfloor$ roots. Its incident lists have sizes at least $L_i+1$. Test every incident root set up to that size using (5) with $b_i b_j+p_i+p_j$ as the edge bound. The ratios $1/p_i+1/p_j+b_i b_j/(p_i p_j)$ decrease in positive list sizes, so it suffices to use the lower endpoints. A root set with a zero lower endpoint is allowed.

For each of the 109 sorted profiles $(b_1,b_2,b_3,b_4,k)$ satisfying (3) and $0\le k\le7$, the checker finds thresholds at $r=28$ excluding every possible incident root set of this vertex. There are respectively 1, 2, 4, 7, 12, 18, 27 and 38 profiles of weights zero through seven. With those same thresholds the left side of (7) stays fixed and its right side is nondecreasing in $r$. The transversal bound used here no longer contains $r$. This proves the assertion for **every** $r\ge28$.

## 5. Completing orders 17 through 27

Use the same threshold test at each individual order. It eliminates 976 of the $11\cdot109$ profiles, including every one with $k<5$. For the remaining 223, a factor exists by §1 and $\Sigma\le S=\lfloor(8-k)r/2\rfloor$. In §2 we therefore use $f=r-7$ when $r>4(1+\lfloor S/3\rfloor)$, and $f=r-10$ otherwise.

**Degree bound used to list individual vertices.** If a vertex has degree $3-h$ in another color $c$, with $1\le h\le3$, there are $4(r-1)+h$ points outside its closed $c$-neighborhood. They have $c$-independence at most $r-1$ and cannot be covered by $r-1$ cliques of size at most four. Brouwer's bound gives at least $6(r-1)+4h+3$ edges there. Adding the $3-h$ edges at the vertex gives $\eta_c\ge3h$. Summing at one vertex gives $q(v)\le2+\lfloor\Sigma/3\rfloor$. At least $r-1$ factor blocks avoiding $v$ each contribute at least $k$ to $X$. Thus a uniform upper bound on $q(v)$ is given by (8). [Brouwer, Theorem 2](https://ir.cwi.nl/pub/6791/6791D.pdf#page=4)
$$
 Q=\max_{0\le t\le S,\ t\in\mathbb Z}
     \min\bigl(2+\lfloor t/3\rfloor,\ (8-k)r+k-2t\bigr).           \tag{8}
$$
A vertex hitting roots $J$ has at least $\sum_{i\in J}(s_i-p_i)$ target neighbors. For a two-root vertex, if $p_i>0$, any missed vertex of row $i$ hits its own $s_i-1$ row mates and the entire opposite list. Thus $p_j\le Q+b_i+2$.

**Singleton colors at a long row.** In a row $L$ of size $r-1$, at most one incident two-root vertex can have a positive miss in the other row. To prove this, take such a vertex $y$ and a missed point $z$ in the other row. The target neighborhoods of $y,z$ together cover $L$ by the complete rectangle. Thus $T=L\cup\{y,z\}$ has at most $r$ nontarget edges, and at least $r-2$ other colors occur exactly once there. Every point outside $T$ must send each singleton color into $T$, since replacing an endpoint of its unique edge gives another $r+1$-set. Each such point has at most three target neighbors in $T$. A second pair $y',z'$ with $z'\ne z$ could therefore cover at most six points of $L$. If $z'=z$, the bound on the $r$-set $L\cup\{z\}$ allows $z$ at most $r-1-f\le9$ target neighbors in $L$. Together with $y'$ this gives at most twelve. Both contradict coverage of $r-1$ vertices.

**Integer certificates.** For each feasible type $T=(J,(p_i)_{i\in J})$, let $n_T\ge0$ be its number of exterior vertices. In addition to (3), the lower bound $b_i+2$ on row incidences, the singleton bound, and (7), use the following summed row inequality. Set $\phi(0)=0$ and recursively put
$$
 \phi(z)=\max\left(0,\ F(z)-\binom z2+T_4(z),\
                  \max_{1\le u<z}\left\lceil z\phi(u)/u\right\rceil\right).
$$
The inner maximum is omitted for $z=1$. This lower-bounds the sum of misses on **any** $z$ incident vertices by the row count and averaging over their $u$-subsets. Select all incident vertices with fewer than $L$ misses to obtain
$$
      \sum_{y:\,i\in J_y}(L-p_i(y))_+
                 \le \max_{0\le z\le P}(zL-\phi(z)).                \tag{9}
$$
Each line of the data file specifies a nonnegative integer combination of these inequalities. The checker verifies its strictly negative right side and a nonnegative coefficient for **every** possible exterior vertex type. Hence its left side is nonnegative for any proposed coloring. The verifier enumerates all integer miss vectors, with no linear-programming solver or compression of the types.

The certificate labels are `count-` for $-\sum n_T\le-P$, `arity+` for (3) in the upper direction, `root` for the negated lower bound on incidences, `long singleton` for the preceding bound of one, `cap` for (7) using $r-10$, and `miss` for (9). Rows in the file are numbered from zero. Three profiles bifurcate according to (6) between the last two rows.

| Order | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Certified profiles | 54 | 48 | 46 | 23 | 17 | 15 | 10 | 6 | 2 | 1 | 1 |

At order 17, the weight-six profile $(0,0,3,3)$ splits on a $1\times4$ rectangle. The weight-seven profile $(0,0,3,4)$ splits on a $2\times5$ rectangle at both 17 and 18.

The 223 profiles give 226 certificate leaves. Replay checks 320,099 exterior vertex types summed over leaves and incident row sets. This completes the proof of $M(4)$ at every order from 17 on.

## 6. The order-19 example and the boundary at sixteen

Consider $k=7$ and deficits $(0,0,0,7)$ at $r=19$. The rows have sizes $18,18,18,11$. There are eleven exterior points, each hitting exactly two rows. Since $S=9$ and $19>4(1+3)$, every 19-set has at least twelve nontarget edges. At any incident long row an exterior point therefore misses at least twelve vertices. Its other list must be empty, since a vertex in it would have to hit those twelve in the long row while itself missing twelve there. This also rules out hitting two long rows. Every exterior point consequently hits the entire short row. In the short row plus all eleven points, every nontarget edge must lie among the eleven, at most $\binom{11}{2}-T_4(11)=45$. The 22 vertices require at least three edges in each of eighteen other colors, or **54**. This excludes the configuration directly.

At $r=16$ the same profile has row sizes $15,15,15,8$. A factor exists by the same surplus argument, $S=8$, and the improved floor is nine. The identical argument again forces all eleven exterior points to hit the entire short row. Now there are nineteen vertices and fifteen other colors, and both counts are **45**. Equality forces the target graph on the eleven exterior vertices to be the disjoint union of cliques of sizes $3,3,3,2$ by equality in Turán. Every other color on these nineteen vertices must consist of three disjoint edges among the eleven: if two edges met, a cover of size at most two would leave seventeen vertices missing that color. This is a necessary structure for this branch at sixteen. The existence of a coloring extending it to all 64 points is open in this argument.

**A coloring attaining equality on those nineteen vertices.** Color every edge inside the short row and from it to the eleven exterior points with the target color. Split the eleven into three triples $A,B,C$ indexed modulo three and a pair $D_0,D_1$. Give each group its internal target edges. The following five matchings and their two cyclic translates give the fifteen other colors. A translate increments all indices in $A,B,C$ together and fixes $D$.

| First edge | Second edge | Third edge |
| --- | --- | --- |
| $A_0D_0$ | $A_1D_1$ | $B_0C_0$ |
| $B_0D_0$ | $A_0B_1$ | $A_1C_1$ |
| $B_0D_1$ | $A_0B_2$ | $A_1C_2$ |
| $C_0D_0$ | $A_0B_0$ | $B_1C_2$ |
| $C_0D_1$ | $A_0C_2$ | $B_2C_1$ |

These matchings use every cross-group pair exactly once. Every 17-set retains an edge of each matching since it omits only two vertices. It contains a target edge since target independence is four. The largest target clique has size eleven, the eight short-row points plus one triple. Thus the bound of 45 is attained by an actual balanced coloring of this induced set. The checker inspects all 171 subsets of size seventeen. The three long rows are outside this example.

For a hypothetical violation of $P(5)$ on $5r+1$ vertices at $r\ge17$, the vertices outside any closed target neighborhood have target independence at most four and span no target $K_r$. This theorem leaves at most $4r-1$ such vertices, so the minimum target degree is at least $r+1$. The general Erdős problem at order 19 and the project's order-ten route remain open. [Reduction, §6](overfull-core.md#6-a-reduction-to-local-statements-for-any-hue)

To replay from this directory, run `python3 -B verify_four_rows.py`. The prerequisite checker is `python3 -B verify_overfull_core.py`.

## Review note, 23 November 2026 (second seat)

This is an internal check by a second model seat working in the same project. It does not replace outside review.

**Scope read.** Sections 1 to 5 line by line, the checker `verify_four_rows.py` line by line, and the citation to Lyle against the paper's text. Section 6 was read for its arithmetic only.

**Result.** No failing step found. Each numbered display was re-derived from the hypotheses: the edge count (1), the two floors $r-10$ and $r-7$ of Section 2, the incidence count (3), the cut bound (4), the transversal condition (5) with its four-list refinement, the rectangle union (6), the row counts (7) and (9), and the degree bound (8). The singleton lemma was checked in both of its cases, $z'\ne z$ and $z'=z$. The checker enumerates exactly the vertex types that Sections 3 and 5 allow, and each certificate inequality it evaluates is one proved in the text.

**Arithmetic.** `replay_four_rows_second.py` rebuilds the bounds from the text of this note with rational arithmetic and shares no code with the checker. It reproduces every count: 109 profiles excluded at order 28, then 976 threshold exclusions, 223 certified profiles, 226 leaves, 3 rectangle splits and 320,099 vertex types at orders 17 through 27, with the same number of certified profiles at each order as in the table of Section 5.

**Citation.** Lyle's Corollary 5 is printed with the hypothesis $\delta\ge(7/10)n$. At equality that statement fails: the join of two blown-up 5-cycles is maximal $K_5$-free with $\delta=7n/10$ and independence number $n/5$, and the paper gives this graph as the sharpness example for its Lemma 13. The strict form used in Section 1 is the correct one. It follows from Lemma 13, stated for $\delta>7n/10$, when the graph is a join of two triangle-free graphs, and otherwise from Theorem 4, whose three terms are each at least $n/4$ once $\delta\ge7n/10$. At order 15 the graph of nontarget pairs has degree exactly $7n/10$, so this theorem does not exclude $k=8$ there.

**Two remarks for a later version.**

- Sections 1 to 5 are valid as written at order 16: $M(3)$ holds, $k=8$ is excluded, and $k\ge4$ gives a factor. The theorem starts at 17 only because profiles survive at 16. The threshold test of Section 4 alone leaves 65 of the 109 profiles there, and 85, 86, 92, 105 and 109 at orders 15 down to 11.
- Identity (1) for $s$ rows on $sr$ vertices reads $X+2\Sigma=sr(s-2)$, with each surplus measured from $r\binom s2$.

## Descent to fifteen, 23 November 2026

The four-row theorem now extends to orders fifteen and sixteen. The matching coloring on nineteen vertices in §6 cannot extend to the three long rows. The supplement gives the direct contradiction, the twelve profiles passing the original unbranched inequalities at sixteen, and the complete census at orders ten through sixteen. Rechoosing the quartet of roots also rules out the regular branch at thirteen. The original proof from seventeen received the second-seat review above. The new descent awaits independent review. [Descent and census](four-row-descent.md) · [Exact replay](verify_four_row_descent.py)
