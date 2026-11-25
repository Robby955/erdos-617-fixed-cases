# Choosing rows on all $r^2+1$ vertices

The two sections below give the original extraction and private-neighborhood estimates cited by the cutoff proof. Section numbers follow the November 22 working note.

## 1. Selecting and restoring cliques on the full vertex set

Suppose every $(r+1)$-set sees all $r$ colors. Each color graph has independence number at most $r$, and any monochromatic clique has size at most $r$. Write $J$ for a sparsest color and $B(v)=v(v-1)/2$. Unless specified, edges, degrees, cliques and independent sets refer to $J$.

Apply Füredi's stability theorem to the complement of $J$ on all $r^2+1$ vertices. It gives $r$ parts $R_i$, with $\mu_i$ internal pairs missing $J$, such that
$$
 \mu=\sum\mu_i\le\eta=e_J(V)-rB(r)-r\le B(r).
$$
The last bound uses $e_J(V)\le r(r^2+1)/2$. Put $b_i=|R_i|-r$, $O=\sum (b_i)_+$, $V_2=\sum b_i^2$, and let $X$ count interpart edges. Each of the other colors needs at least $(b_i)_+$ internal edges, since deleting one endpoint per edge leaves an independent set. Consequently
$$
 \sum b_i=1,\quad O\le\mu/(r-1)\le r/2,\quad
 X=\eta+\mu-(V_2-1)/2\le r(r-1).
$$
Here $V_2\ge1$. [Füredi's stability theorem](https://arxiv.org/abs/1501.03129)

**Stars into a single part.** Set $U_i=\mu_i-(r-1)b_i$, so $U_i\ge0$ and $\sum U_i=\mu-(r-1)$. If $Z$ consists of $m$ vertices outside $R_i$, each nontarget hue has at least $m+b_i$ edges on $R_i\cup Z$. Counting the available nontarget pairs gives
$$
 e_J(Z,R_i)\le U_i+(1+b_i)m+B(m).                                      \tag{1}
$$
Qualify a part as a destination if $b_i\le r/1024$ and $U_i\le r^2/2048$. At most $512+1024=1536$ parts fail. Put $\tau=33/200$ and $a=81/500$. A qualified part has at most $U_i/(ar)$ exterior vertices of degree greater than $\tau r$ into it. Indeed, for any $m\le\lfloor r/256\rfloor$ such vertices, (1) gives
$$
 U_i>mr\left(\tau-1/1024-(m+1)/(2r)\right)\ge mar.
$$
For $r\ge2^{20}$, even $m=\lfloor r/256\rfloor$ would exceed the qualifying budget. Applying the inequality to the actual number proves the claim (the empty set satisfies it directly).

First remove vertices one at a time when they send more than $\tau r$ current edges to a single qualified foreign part. Then remove vertices whose current total interpart degree exceeds $r/4$, again one at a time. Let $P_s,P_t$ count the respective removals. Counting original stars in the first stage and freshly removed edges across both stages gives
$$
 P_s\le\mu/(ar),\qquad \tau rP_s+rP_t/4\le X.                         \tag{2}
$$
Trim oversized parts to $r$, costing at most $O$ vertices. The total deficit from $r$ across these $r$ slots is at most $P_s+P_t+O-1<6r$, using (2) and $4+(1-4\tau)/(2a)+1/2<6$.

**Extracting cliques.** Across *all* slots take a maximal family of $q$ nontarget pairs in distinct slots whose $2q$ endpoints are jointly independent. In unchosen slots delete neighbors of these endpoints, costing at most $qr/2$ vertices. The survivors of each unchosen slot form a clique by maximality. Let $f$ of those slots now have size below $r/2$. The other unchosen slots, with size at least $r/2$ and interslot degree at most $r/4$, admit independent representatives by Haxell's theorem. Together with the endpoints they give $r+q-f\le r$. Hence $q\le f$. The $f$ omitted short slots account for at least $fr/2$ final deficit. This pays for all $qr/2$ newly lost vertices. Thus the retained cliques have total deficit at most $P_s+P_t+O-1$. In applications of Haxell's theorem first erase edges within each list. [Independent transversal theorem, Theorem 1](https://arxiv.org/abs/2305.10595)

For a bound on the *number* of omitted slots, at most 48 slots were below $7r/8$ before deleting the neighbors. At most $4q/5$ of the initially larger unchosen slots fall below $r/4$, since each loses more than $5r/8$. For this count only, take the unchosen lists still of size at least $r/4$. Prune vertices of current interlist degree greater than $r/16$ in succession. This costs at most $16X/r\le16r$ vertices, so at most 128 additional lists fall below $r/8$. Haxell extends the original pairs by one point from every remaining list. Hence
$$
 q\le48+4q/5+128,\qquad q\le880,\qquad f\le12+q\le892 .
$$
The bound on $f$ uses total deficit at most $6r+qr/2$ after deleting neighbors. Revert this temporary pruning. Set aside the $q$ chosen slots, the $f$ short slots and all unqualified destinations. The number $e$ set aside is at most $3308<4096$.

For a remaining clique $C_i\subseteq R_i$, put $d_i=r-|C_i|$, $\ell_i=e_J(C_i,V\setminus C_i)$, and $a_i=\max(d_i/r,\ell_i/r^2)$. If $b_i>0$, the compulsory $(r-1)b_i$ internal nontarget edges avoid $C_i\times C_i$. Subtracting them from $B(r+b_i)-B(r-d_i)$ bounds the cut inside $R_i$ by $rd_i+B(b_i+1)-B(d_i+1)$. For $b_i\le0$ the bound $rd_i$ suffices. Summing the bounds on $\max(rd_i,\ell_i)$ uses at most $V_2$ for the terms $B((b_i)_++1)$. At least $\tau rP_s+rP_t/4$ of the original $2X$ cross incidences had a removed endpoint. Thus
$$
\begin{aligned}
 r^2\sum a_i
 &\le r(P_s+P_t+O-1)+V_2+2X-\tau rP_s-rP_t/4\\
 &\le 5X+(1-4\tau)rP_s+rO-r+V_2
 \le (1061/162)r^2.
\end{aligned}\tag{3}
$$
Indeed $5X+V_2\le10\eta+1$, $rP_s\le r^2/(2a)$, and $11/2+(1-4\tau)/(2a)=1061/162$.

**Restoration.** Within each retained part add back any vertex surviving the first pruning stage that is complete to its current clique and has full degree at most twice the clique's current size. Repeat until no such vertex remains. Each addition lowers the deficit. It changes the cut by $d_J(v)-2|C_i|\le0$ and preserves the other row cuts. Consequently (3) persists. Every point of a restored clique still has at most $\tau r$ edges to *each* other retained clique because both consist of survivors of the first pruning stage and the destination qualified. The restriction on degree into a single row is what the grouped extension below uses.

## 3. Rooted rows with at most $5(r-1)/2$ excess incidences

There is also a row choice requiring no large-order hypothesis. Write $N=r^2+1$, $l_v=d_J(v)+1$, $s_0=r+1$, $x_v=l_v/s_0$ and $\lambda=5/2$. There exist $r$ independent roots $A$. For a vertex $y$ let $q_y=|N_J[y]\cap A|$. The vertices with $q_y=1$ belonging to each root form a clique containing it. For the set $P$ of the other vertices,
$$
    |P|+\sum_{y\in P}(q_y-2)=\sum_{y\in P}(q_y-1)\le 5(r-1)/2.       \tag{4}
$$
In particular the $r$ cliques have total deficit $D=|P|-1$. Thus $D\le(5r-7)/2$. Each row of size at most $r-3$ costs at least three units, so at least $\lceil(r+7)/6\rceil$ disjoint cliques have size at least $r-2$.

**Proof.** Sparsity gives $\sum_v(x_v-1)\le0$. The local minima of a uniform random vertex ordering, each tested in its closed neighborhood, form an independent set. Hence $\sum_v1/l_v\le r$. For $g(x)=(x-1)^2/x$, this gives
$$
 \sum_v g(x_v)=s_0\sum_v1/l_v-N+\sum_v(x_v-1)\le r-1.
$$
Put $a_0=9/10,\ b=(\lambda+a_0)/2=17/10,\ L=\lambda s_0$ and $w_v=(L-\max(l_v,a_0s_0))_+$. Among the positive-weight vertices choose an independent set $A$ of greatest total weight, breaking ties by greatest cardinality $t$. Put $p(x)=(a_0-x)_+/x,\ z(x)=(x-\lambda)_+/x$. By the same random ordering its weight is at least $\sum_v w_v/l_v$ after discarding zero-weight minima. Expanding $w_v/l_v=\lambda/x_v-1-p(x_v)+z(x_v)$ yields
$$
  w(A)\ge LN/s_0-N+\sum_v[\lambda g(x_v)-p(x_v)+z(x_v)]
         \ge LN/s_0-N .
$$
For the last inequality use $p\le\lambda g$, since $\lambda(x-1)^2-(a_0-x)=(5/2)(x-4/5)^2$.

Every positive-weight vertex is dominated by $A$. In each root's private neighborhood take the root and the uniquely dominated vertices satisfying $x_v\le b$. These form a clique. Otherwise two such nonadjacent private vertices can replace their root while preserving independence. Their combined weight is at least $(\lambda-a_0)s_0$, the largest possible root weight. This contradicts maximal weight or the tie break. The resulting $t$ cliques cover at most $rt$ vertices. For each vertex outside them,
$$
 1\le q_y-1+\mathbf 1_{x_y>b}+\mathbf 1_{x_y\ge\lambda}.
$$
Indeed an undominated point has zero weight, a uniquely dominated omitted point has $x_y>b$, and a multiply dominated point has $q_y\ge2$. On the covered points the right side is nonnegative. Also $\sum_y q_y=\sum_{u\in A}l_u\le Lt-w(A)$. It follows that
$$
 0\le (r+L)t-N-LN/s_0+
 \sum_v[\mathbf 1_{x_v>b}+\mathbf 1_{x_v\ge\lambda}+p(x_v)-z(x_v)-\lambda g(x_v)] .
$$
The bracket is at most $g(x_v)$. Below or at $b$ use $p\le\lambda g$. Above $b$, use monotonicity of $g$ for $x>1$, $(\lambda+1)g(b)=343/340>1$, and $(\lambda+1)g(\lambda)>2$. Were $t\le r-1$, the right side would be at most $-r-1-2\lambda+(r-1)<0$. Thus $t=r$. All vertices are now dominated by the independence cap. All uniquely dominated neighbors of a root form a clique, because any two nonadjacent ones could replace it to give an independent $(r+1)$-set. Finally
$$
 \sum_{y\in P}(q_y-1)=\sum_{u\in A}l_u-N
             \le L(r-N/s_0)=\lambda(r-1).
$$
Counting vertices proves $D=|P|-1$.
