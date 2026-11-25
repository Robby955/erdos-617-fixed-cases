# Weighted transversals and the cutoff $r\ge 2^{146}$

Robert Sneiderman’s research notes · 23 November 2026

**Theorem.** For every integer $r\ge 2^{146}$, every coloring of the edges of $K_{r^2+1}$ with $r$ colors contains $r+1$ vertices whose induced edges omit a color.

The bound applies to every coloring. It improves the previous bound $2^{165}$ by a factor of $524{,}288$. Two ingredients control discarded parts. A weighted independent transversal charges missing representatives to short lists. The ordered partition supplies distinct edge incidences for the surplus in oversized chosen parts. The combined proof awaits independent review. The conjecture for every $r\ge3$ remains open. [Preceding proof, §§3–5](cutoff-165.md) · [Numerical certificate](verify_weighted_width.py) · [Local Lean lemmas](WeightedWidth.lean) · [Combined PDF](../paper.pdf)

## 1. Count the unused part of the stability bound

Suppose a counterexample exists. Choose a sparsest color $J$, and call its edges target edges. Each color has independence number at most $r$, and every monochromatic clique has at most $r$ vertices. Write $p_k(n)$ for the minimum number of edges on $n$ vertices with independence number at most $k$, the sum of the internal binomial coefficients of $k$ balanced parts.

Consider any induced target graph with independence number at most $k$ and excess $\eta=e_J-p_k(n)$. In its complement choose a vertex of maximum residual degree. Take that vertex and all its residual nonneighbors as a part, then continue on its neighbors. The pivots form a clique in the complement, so at most $k$ parts occur. Pad with empty parts. In each step the residual degrees of the vertices in the part are at most the number of later vertices. Summing gives $e(\bar J)+\mu\le e(K(R_1,\ldots,R_k))$, where $\mu$ counts internal pairs missing $J$. Let $V=\sum_i(|R_i|-r)^2$, let $V_{\rm bal}$ be its balanced value at the same $n,k$, and let $X$ count the interpart target edges. Expanding binomial coefficients gives
$$
 \mu\le\eta-\tfrac12(V-V_{\rm bal}),\qquad
 X=\eta+\mu-\tfrac12(V-V_{\rm bal})\le 2\eta-(V-V_{\rm bal}).                 \tag{1}
$$
We also keep the inequality before summing. In part $R_i$ the residual complement degrees sum to $2\mu_i+e_{\bar J}(R_i,R_{>i})\le |R_i||R_{>i}|$, where $R_{>i}$ consists of all later parts. Thus there are at least $2\mu_i$ target edges directed from $R_i$ to later parts. [Füredi, proof of Theorem 1, equation (4)](https://arxiv.org/pdf/1501.03129#page=3)

On the full graph, take $k=r$. Then $V_{\rm bal}=1$, $\eta\le\binom r2$ by sparsity, and $X/r^2\le 1-v$ for $v=V/r^2$. Write $b_i=|R_i|-r$, $\mu_i$ for the internal missing count, and $U_i=\mu_i-(r-1)b_i$. Each other color needs at least $(b_i)_+$ edges in $R_i$, by deleting one endpoint per edge. Hence $\sum_i(b_i)_+\le r/2$, $U_i\ge0$, and (1) gives $\sum_i U_i=\mu-(r-1)\le r^2(1-v)/2$.

A destination qualifies if $b_i\le r/256$ and $U_i\le r^2/1200$. At most 728 parts fail. First prune any vertex with more than $r/4$ current neighbors in one qualifying foreign part. Record one such destination and its current star. In a qualifying part the number of possible sources is at most $U_i/((61/250)r)$, hence at most $\omega r$ where $\omega=5/1464$. This is the ordered-star count in the earlier extraction. Next prune while any current total interpart degree exceeds $\tau r$, with $\tau=199/400$. Write $pr,tr$ for the two deletion counts. The stars and the edges spent at the second stage are fresh. Consequently
$$
 p\le p_*(1-v),\qquad Z=1-p/4-\tau t\ge v,\qquad p_*=125/61.
$$
Set $Y_*=2-p/2-\tau t$. For any family of surviving cliques, charge each clique its target edges outside its raw part, excluding the recorded stars. If $y_i'r^2$ is this count at clique $i$, then $\sum y_i'\le Y_*-2v$. Indeed the original incidence count is at most $2(1-v)r^2$. Both ends of a recorded edge disappear from the sum, and at least one end of each second-stage edge disappears. Edges between surviving cliques are fully counted. [First-stage count](cutoff-218.md#1-choosing-rows-with-less-total-deficit) · [Recorded edges](cutoff-190.md#1-count-the-source-of-a-large-star-once)

## 2. Give missing representatives to the short lists

Before trimming any part, choose a maximal family of $q$ pairs, one pair in each of $q$ distinct surviving parts, with all $2q$ endpoints independent. Delete their neighbors in the unchosen parts. Each remaining list is a clique by maximality. Write $m_i\le r$ for its size. Set $d=1-2\tau=1/200$, $L=(1+2\tau)/2=399/400$, and $b=\lfloor Lr\rfloor$. Since $(L-2\tau)r>1$, we have $b>2\lfloor\tau r\rfloor$.

For the following test alone, truncate lists of size at least $b$ to $b$ and pad shorter ones with isolated dummy vertices to $b$. Erase within-block edges. The resulting graph has maximum degree at most $\lfloor\tau r\rfloor$. Give real vertices weight one and dummies weight zero. The weighted independent transversal theorem gives a choice of one vertex per block, with mutually independent real choices, of weight at least
$$
 r-q-W,\qquad W=\sum_{m_i<b}(1-m_i/b).
$$
The real choices and the $2q$ endpoints are independent in the original graph. The independence cap $r$ implies **$q\le W$**. All lists, including those from unqualified parts, enter this test. [Graf, Harris and Haxell, Theorem 7](https://arxiv.org/pdf/1907.00033#page=4)

Keep the original untruncated lists of size at least $b$ in qualifying parts as ordinary cliques $C_i$. Put $x_i=1-|C_i|/r,\ D=\sum x_i,\ Y=\sum y_i'$. Let $a_i r$ be the early deletions in raw part $i$, during both pruning stages. The chosen parts then contain exactly $(q+\sum_{\rm chosen}(b_i/r-a_i))r$ survivors. Their endpoints remove at most $2\tau qr$ further vertices from unchosen parts. The $F$ short lists have combined deficit at least $(1-L)F+LW$, since $m_i/r\le Lm_i/b$. Using $q\le W\le F$, and dropping the favorable $-1/r$ from the original order, gives
$$
 D+\tfrac d2(F+q)\le p+t+\sum_{\rm chosen}(b_i/r-a_i).                   \tag{2}
$$
On $0\le p\le p_*,\ t\ge0,\ Z\ge0$, the maximum of $1/2+p+t$ is $85689/24278<3.53$. Hence $D<3.53$ and $n=F+q\le1411$. If $e_0$ is the number of omitted slots, then $e_0\le728+n$.

Consider the chosen raw parts with $b_i>r/256$. Write $O=\sum b_i/r$ and $a=\sum a_i$ over these parts only. All are unqualified destinations. The ordered inequality in §1 supplies at least $2\sum\mu_i\ge 2(r-1)Or$ outgoing target edges from them. Count just the incidence at the earlier endpoint of each such edge. These incidences are distinct, and every one is absent from $Y$.

To account for overlap, distribute exactly $r/4$ units of edge weight over each first-stage recorded star and exactly $\tau r$ units over the fresh edges at each second-stage source, with at most one unit per edge. At the first stage count this weight at both ends, and at the second count it only at the source. These are the charges already used for $Y_*$. An incidence in the preceding outgoing count cannot be a first-stage destination charge, since its part is unqualified. All its possible overlap is therefore at an early source in these parts. The total overlap is at most $\tau a r^2$, including sources from both stages. It follows that
$$
 Y\le Y_*-2(1-1/r)O+\tau a .
$$
Here we discarded the favorable $2v$. The sum on the right of (2) over chosen parts is at most $O-a+q/256$. The table parameters satisfy $2(1-1/r)\beta\ge\alpha$ and $\tau\beta\le\alpha$. Combining the last two bounds pays for both $O$ and $a$. Since $q\le n/2$, we obtain
$$
 \frac{Y}{\alpha}+\frac{D}{\beta}
 \le\frac{Y_*}{\alpha}+\frac{p+t}{\beta}
            -\frac{d-1/256}{2\beta}\,n .                                \tag{3}
$$

## 3. Integrate both endpoints of the width test

Take $K=1120,\ K'=K+2n$. Give each ordinary row weight $a_i=\max(y_i',\alpha x_i/(2\beta))$, reusing $a_i$ only in this section. Set aside the $K'-e_0-1$ largest weights. There are at least $K'/4$ such rows, because $e_0+1\le729+n$ and $729\le3K/4$. Put $Q_i=\alpha x_i^2/(4\beta^2)\le a_i^2/\alpha$. For the rows still under consideration define
$$
 s(z)=K'+\#\{i:a_i>z\},\qquad F(z)=s(z)z/\alpha+\sum_{a_i\le z}Q_i/z .
$$
Let $R=2^b$ with $b$ from the table in §5, $S=2^{(146-b)/4}$, $\ell=\alpha/S$, and $H_0=\alpha/K'$. We have $K'\le3942$ and $S>2K'$. The full integral of a positive-weight row against $dz/z$ is $a_i/\alpha+Q_i/a_i\le y_i'/\alpha+x_i/\beta$. A zero-weight row costs zero. The contribution of the $K'z/\alpha$ term on $[0,H_0]$ is one.

Suppose $F\ge1$ on $[\ell,H_0]$. Its integral below $\ell$ is at least $F(\ell)\ge1$. For $a_i>\ell$ the integral there equals the row's value $\ell/\alpha$. For $0<a_i\le\ell$ it is $a_i/\alpha+Q_i/a_i-Q_i/\ell\ge Q_i/\ell$, since $a_i/\alpha\ge Q_i/a_i\ge Q_i/\ell$. The base term also equals its endpoint value after integration.

There is a further saving of $1/4$ from the rows set aside and the square terms above $H_0$. Write $u=\max a_i/H_0$ over the remaining rows, taking zero on the empty family. The rows set aside cost at least $u/4$ in total. If $u\ge1$, this suffices. If $u\le1/2$, failure at $H_0/2$, where every remaining row has passed its threshold, gives $\sum Q_i/H_0\ge1/4$. This is precisely their integral above $H_0$. For $1/2\le u\le1$, failure at $uH_0$ gives $\sum Q_i/H_0\ge u(1-u)$. Together the two savings are at least $u/4+u(1-u)\ge1/4$, since the difference is $(1-u)(u-1/4)$.

Failure throughout the interval would imply $\log(S/K')\le Y/\alpha+D/\beta-1/4$. By $\log(K'/K)\le2n/K$ and $(d-1/256)/(2\beta)\ge2/K$, (3) would give $\log(S/K)\le Y_*/\alpha+(p+t)/\beta-1/4$. Section 5 verifies the strict reverse. Take a level with $F(z)<1$, set $s=s(z)$ and $w=sz/\alpha$, and omit the remaining rows of weight above $z$. There are exactly $h=s-1$ omitted slots. On the retained cliques,
$$
 s\max y_i'\le\alpha w,\quad s\max x_i\le2\beta w,\quad
 s\sum x_i^2\le4\beta^2w(1-w),\quad K\le s<S,\quad r\ge R s^4.          \tag{4}
$$
The first two inequalities follow from the threshold. The third follows by multiplying the inequality $\sum Q_i/z<1-w$ by $4\beta^2sz/\alpha$.

## 4. A shortage of at least $3r/20$

Use $f=9/40,\ \rho=f/s,\ \rho_0=f/K$. Let $G$ consist of all exterior points with at most $\rho r$ neighbors in each retained clique, and put $\Delta=hr-|G|$. We show $\Delta>cr$ for $c=3/20$. Let $A,X_0,B$ upper bound the first three left sides in (4). Ordinary lists of size at least $r/41$ in any subfamily have independent representatives by the counting lemma, since inter-clique edges are undiscounted and $4\cdot41^2 A/K<1$. Independent $h+1$ points of $G$ would therefore extend through all ordinary rows. In a temporary ordinary row remove vertices whose **unrecorded** foreign degree exceeds $r/8$. Its remaining fraction is at least $1-o$, $o=1/256$, since $(X_0+8A)/K<o$. The degree from a survivor outside its original clique is at most $(1/8+\omega+1/256+X_0/K)r<(7/50)r$. This includes the points in its own raw part outside the clique. [Ordinary list counting lemma](cutoff-289.md#1-parameters-and-a-count-of-independent-transversals)

If $\Delta\le cr$, take $hr+1$ points of $G$ when available and otherwise take $G$. This auxiliary set has order $hr+b'$ for $b'=1$ or $b'=-\Delta,\ 0\le\Delta\le cr$ in the second case. Its target independence number is at most $h$. Write $I=2^{-20}$, so $h\ge799,\ h^2/r<I,\ 1/r<I$. The target and the $r-1$ other Turán floors give $2\eta_a/r^2\le \xi=c^2+I$. In fact $2\eta_a\le rh(h-1)+c^2r^2$ by the signed-integer floor expansion in base §3. For the $h$ auxiliary parts of (1), put $x=X_a/r^2,\ u_i=(r-|R_i^a|)_+/r$. Since the balanced squared deviation is at most $(b')^2/h+h/4$, (1) yields
$$
 x\le\xi,\qquad x+\sum u_i^2\le T=(1+1/799)c^2+3I,\qquad
 \sum u_i\le D_a=c+\frac{\xi}{2(1-I)}.
$$
The last bound charges each overfull auxiliary part to the other colors and adds the net deficit. [Turán floor and auxiliary construction](balanced-coloring.md#3-a-shortage-of-exterior-vertices)

Prune auxiliary vertices of current interpart degree above $t_a r$, $t_a=43/200$. If $zr$ vertices are pruned, $0\le z\le x/t_a$ and at most $(x-t_a z)r^2$ interpart edges remain. For any $j=1,2,3$ rows the sum of their final positive deficits, divided by $r$, is at most
$$
 D_j=b_j+(T-b_j^2/j)/t_a,\qquad b_j=\min(D_a,jt_a/2),\qquad D_0=0 .
$$
Indeed their raw sum $u$ satisfies $x\le T-u^2/j$, and all subsequent deletions cost at most $x/t_a$ in total. The quadratic maximum on $[0,D_a]$ is the value displayed. In particular $u_i+x/t_a\le D_1$. The three bounds are below $0.158546,\ 0.205577,\ 0.225734$. Every auxiliary survivor part is a clique. A nonedge would leave fractions at least $1-D_1-2t_a>0$ in the other auxiliary parts. Its square exceeds $\xi$, so the expected number of interpart edges among uniform representatives is less than one.

Use thresholds $\theta_a=81/200$ and $\theta_o=369/1000$ for large attachments to auxiliary and ordinary rows respectively. As in the earlier attachment proof, extend either two independent exterior points or one exterior point and at most two compatible prescribed representatives. Extra rows may be omitted. Each unfilled row has only small attachments from the prescribed exterior points. To fill auxiliary rows, it suffices that each list be nonempty and the product of any two list fractions exceed the entire normalized remaining edge count $x-t_a z$. Uniform independent choices then have expected conflicts less than one.

For two exterior points let $w_0=1-2\theta_a$, and sort the raw lower bounds $b_1'=w_0-u_1,\ b_2'=w_0-u_2$ so $b_1'\le b_2'$. If $a=u_1+u_2$, their product plus $u_1^2+u_2^2$ is at least $w_0^2-w_0a+3a^2/4$. Its minimum for $0\le a\le D_a$ exceeds $T$, so $b_1'b_2'>x$. Both bounds are positive since $w_0>D_1$. Charging all $z$ deletions against the smaller factor leaves product at least $b_2'(b_1'-z)$. This exceeds $x$ at zero and is positive at $z=x/t_a$, since $u_i+x/t_a\le D_1$. Linearity yields the required strict inequality.

For one exterior point use $w_0=1-\theta_a$. At most two representatives forbid at most $2t_a r$ points across all unfilled auxiliary rows. Ordinary representatives have the smaller outside-clique degree bound $7r/50$. Here $w_0-2t_a>D_1,\ w_0-D_a>t_a$. Thus $b_1'-2t_a>x/t_a,\ b_2'>t_a$, giving $b_2'(b_1'-2t_a-z)>x-t_a z$. In both cases the same individual estimates give nonempty lists even if only one row is unfilled. All auxiliary choices are in $G$. Their total cost in any ordinary row is at most $fr$. The available fractions $1-o-2\theta_o-f$ and $1-o-\theta_o-f-2(7/50)$ both exceed $1/41$.

For the $hr+1$ auxiliary set use the $h$ auxiliary rows alone. Otherwise use them with the $r-h$ temporary ordinary rows on the full graph. In each case the vertex count is one more than the number of rows times $r$, and the target independence cap is the number of rows. Every exterior point has a large attachment. A point with a unique large row must join all its vertices, and any two such points assigned to that row are adjacent, by the preceding extensions. Enlarge the cliques by those points. If $P$ exterior points remain, the enlarged deficits in vertices sum to $P-1$.

For completeness, price each large arrival at $(kd_i+q_0)r$, where $d_i$ is the enlarged normalized deficit, $k=77/100,\ q_0=1/10000$. Write $\vartheta$ for its row threshold and $e$ for its individual deficit cap $o$ or $D_1$. The checker tests
$$
 2(\vartheta-ke-q_0)(1+k)>1,\quad
 2(\vartheta-ke-q_0)q_0>(\vartheta+e+1/2)I,\quad 2((1+k)e+q_0)<1 .
$$
The one-clique capacity applied to $\lfloor2((1+k)d_i+q_0)r\rfloor$ arrivals then gives $(n+1)/(2r)-d_i\le kd_i+q_0$ for the actual count $n>0$, including rounding as in §3 of the 190 supplement.

For a point with two large rows let $j$ be the number of auxiliary ones, let $e_1,e_2$ be the individual caps before enlargement, and set $U=D_j+(2-j)o$. If their combined degrees were at most $(1+kU+2q_0)r$, the two lists of nonneighbors would have product larger than the entire target cut between these cliques. For each ordered pair of types the checker verifies positive factors and
$$
 (1-e_1-\vartheta_1)(\vartheta_1-e_2-kU-2q_0)>
                  \min(e_1e_2,U^2/4)+I .
$$
The minimum product at fixed combined degree is at an endpoint by concavity. The two-clique capacity bounds the normalized cut by the right side. Compatible representatives would extend with the point. Its net contribution after prices must therefore exceed $r$. Any three large arrivals also pay more than $r$ net, since $j\theta_a+(3-j)\theta_o-k(D_j+(3-j)o)-3q_0>1$ for $0\le j\le3$. Every additional arrival contributes positively. Summing the one-clique capacities gives $rP\le(r-1)(P-1)$, impossible. For $P=0$ the sum of deficits is already impossible. This proves the claimed shortage. [Attachment prices and rounding](cutoff-190.md#3-charge-an-arrival-at-its-own-row)

## 5. The five width bands and the final signed cut

In the following table $b=\log_2 R$. Select a closed band containing $Y_*$.

| Band for $Y_*$ | $b$ | $4000\alpha$ | $4000\beta$ |
| --- | ---: | ---: | ---: |
| 0 to 0.50 | 14 | 656 | 924 |
| 0.50 to 0.55 | 14 | 656 | 922 |
| 0.55 to 0.68 | 14 | 652 | 916 |
| 0.68 to 1 | 15 | 652 | 916 |
| 1 to 2 | 17 | 654 | 918 |

For each band the checker clips the pruning trapezoid by its two boundary lines. At every vertex $Y_*/\alpha+(p+t)/\beta-1/4<\log(S/K)$. The minimum certified difference exceeds $0.01427$. Logarithms are enclosed by the positive series for $2\operatorname{arctanh}$.

The first band also identifies a limit of these constants. At the relaxed boundary $p=125/61,\ Z=0$, we have $Y_*=119/244,\ t=11900/12139$. For $r=2^{145}$, the sufficient width cost there exceeds $\log(S/K)$ by more than $0.159$ when $S=2^{(145-14)/4}$. Whether actual edge incidences can consume that entire budget is a separate question.

Apply the marked-sender and excess-arc construction of §5 of the 165 supplement. The per-destination degree bound is $r/4$ between retained cliques. A retained row has at most $\omega r$ recorded sources, and $D+1/2+p<7,\ 2D<9$. The ordinary extension for excess arcs requires $1-X_0/K-3/4-f>1/41$, which holds. Change the unique-sender retry probability to $100\rho<1$. The success probability at neighbor fraction $q_y>1/2$ is $(1-q_y)(1+100\rho q_y)$. The marginal probability of a given representative is at most $j/r$ for
$$
 \gamma=A/f,\quad g=X_0/f,\quad \kappa=B/f,\quad
 j=(1+100\rho_0)/(1-g\rho_0).
$$
The retry surplus is at least $37\rho r(1-q_y)$ by $50(1-\rho_0)-1-g>37$. The excess-arc conflict coefficient stays $4/3$ and the variance coefficient stays $\lambda=501/1000$, since $2g\rho_0/(1-g\rho_0)<1/1000$. [Excess arcs and tested cut](cutoff-165.md#5-charge-only-the-excess-of-a-heavy-load) · [Retry calculation](cutoff-289.md#3-using-the-labels-of-edges-into-a-row)

Here are the remaining inputs to that signed cut. Put $\eta'=1/(Rf^2)$, $y_{\rm hi}$ equal to the upper end of the band, and
$$
 \begin{aligned}
 n_*&=513\gamma/512+1/256+g\rho_0+\omega,& a&=\min(5/2,(249/250)/n_*),\\
 k'&=(4/3)/(a-4/3),& b_1&=j(1+1/k'),\\
 V'&=a(513 y_{\rm hi}/(512f)+7/K)+9b_1/K .
 \end{aligned}
$$
The heavy-load count at each row is at most $n_*r$, using $2jg\rho_0<1/512$. The tests $an_*+2b_1g\rho_0<1,\ a>4/3,\ a\kappa<2$ give valid row probabilities and the square estimate of the 165 supplement. Its repair bound in units of $\rho^2r^2$ is
$$
 {\cal P}(W',l)=\frac{k'(b_1W'+l)^2}{2-a\kappa}
 +k'\eta'\left(\frac{(1+V')^2+V'/K}{2}+\frac1{2K}\right).
$$
Here $l=(\Delta-m)/(\rho r)$, $m$ is the expected number of marks, and $W'\rho r$ bounds the sum of unique-sender counts times their assigned normalized deficits. The first application uses $2\kappa$. The retry surplus gives the second input
$$
 Z_1=8{\cal P}(2\kappa,0)+2\eta',\qquad
 W_1=\big((1-g\rho_0)^{-1}+\lambda g/37\big)\kappa+gZ_1\rho_0/37 .
$$
Put $Z_2=8{\cal P}(W_1,0)+2\eta'$ and $\epsilon(l)={\cal P}(W_1,l)+gl+l^2/2+\eta'(1/2+1/(2K))$. Both oversampling tests $Z_i\rho_0^2<\min(c/128,1/16)$ pass. The one-row signed-cut comparison and the bound on expected failures require $0\le l\le\lambda\kappa$ and
$$
 (1-\epsilon(l))(c-\lambda\kappa\rho_0)+l-\lambda\kappa
                 -Z_2\rho_0-1/(fRK^2)\le0 .                              \tag{5}
$$
These reductions use the shortage from §4 and the same surplus coefficient 37. [Two applications of the signed cut](cutoff-190.md#4-recover-the-cost-of-uniquely-assigned-senders)

Divide $w\in[0,1]$ in (4) into 128 closed intervals per band. Use the maximum of each of its first three right sides separately on each interval for $A,X_0,B$. The checker uses these upper bounds throughout, verifies $0<\epsilon(l)<1$ at both endpoints of the $l$ interval, and verifies all the list, degree and probability conditions above. The left side of (5) is concave in $l$, since $c-\lambda\kappa\rho_0>0$. All $5\cdot128\cdot2=1280$ endpoint values exceed $0.0003327$, contradicting (5). This proves the theorem subject to the cited earlier arguments. The exact computation certifies the constants and tests the discarded-incidence bound on all 1,024 labelled five-vertex target graphs with every choice of omitted raw parts. Five local inequalities are checked in Lean. The general combinatorial argument is in the manuscript.
