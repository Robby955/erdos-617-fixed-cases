# A large-order bound for the Erdős–Gyárfás balanced coloring conjecture

Robert Sneiderman · Draft of 22 November 2026

**Theorem 1.** For every integer $r\ge 2^{483}$, every coloring of the edges of $K_{r^2+1}$ with $r$ colors has a set of $r+1$ vertices whose edges omit a color.

**Theorem 2.** In a hypothetical counterexample with 19 colors, a sparsest color contains either a clique of size 19 or three disjoint cliques of size 18. It also contains seven disjoint cliques of size at least 17. Three of its disjoint cliques can be chosen so that another color contains 13 vertex-disjoint triangles, each meeting all three.

**Theorem 3.** In every affine plane of order $r\ge7$ there is a balanced coloring on $r^2$ vertices with three specified rows for which fixing the old edges incident to those rows forces the conjectured conclusion after adding one vertex. All other edges are free. The witness uses the new vertex, the rows, and at most one other vertex. The specified rows each contain $r-1$ points.

Sections 1–6 give the large-order proof. Sections 7–9 prove the finite restriction and the affine-plane statement. These claims await independent review. The general conjecture requires every integer $r\ge3$. [Erdős and Gyárfás, Conjecture 1](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf)

## 1. Extracting target-color cliques

Assume a counterexample and choose a sparsest color $J$. Every color graph has independence number at most $r$, and every monochromatic clique has order at most $r$. Edges, degrees and independence below refer to $J$ unless a different color is specified. Put $B(x)=x(x-1)/2$. Write $p_k(n)$ for the minimum number of edges of a graph of order $n$ with independence number at most $k$. By Turán's theorem this is the sum of $B$ on $k$ balanced integer part sizes.

Füredi's stability theorem applied to the complement of $J$ gives $r$ parts $R_i$ on all $r^2+1$ points. The number $\mu$ of internal pairs missing $J$ is at most $\eta=e_J(V)-rB(r)-r\le B(r)$, since the color has at most $r(r^2+1)/2$ edges. Put $b_i=|R_i|-r,\ O=\sum (b_i)_+,\ V_2=\sum b_i^2$. Each other hue needs at least $(b_i)_+$ edges in $R_i$, by deleting one endpoint per edge. Since $\sum b_i=1$ and $V_2\ge1$, the number $X$ of target edges between parts satisfies
$$
 O\le\mu/(r-1)\le r/2,\qquad X=\eta+\mu-(V_2-1)/2\le r(r-1).
$$
[Füredi's stability theorem](https://arxiv.org/abs/1501.03129)

Delete points of current total interpart degree greater than $r/4$, one at a time. Each deletion removes fresh cross edges, so the number $P$ deleted satisfies $rP/4\le X$. Trim parts above $r$ to $r$. The sum of the deficits from $r$ over all slots is at most $P+O-1\le9r/2$.

Take a maximal family of $q$ pairs, each inside a different slot, whose $2q$ endpoints are jointly independent. In unchosen slots discard their neighbors, at most $qr/2$ points. Each unchosen slot's survivors form a clique by maximality. Let $f_0$ unchosen slots now have size below $r/2$. The other unchosen slots admit independent representatives by Haxell's theorem, since their interlist degree is at most $r/4$. With the endpoints this gives $r+q-f_0\le r$. Omitting the short slots therefore pays for all the neighbor deletions in the deficit sum, since $f_0r/2\ge qr/2$. [Haxell's independent transversal theorem](https://arxiv.org/abs/2305.10595)

To bound the number of omitted slots, at most 36 were initially below $7r/8$ after trimming. Among initially larger unchosen slots, at most $4q/5$ fall below $r/4$ after discarding the neighbors. On lists still of size at least $r/4$, temporarily prune current interlist degrees above $r/16$. At most $16X/r\le16r$ points are lost and at most 128 more lists fall below $r/8$. Haxell extends the original endpoints on the remaining lists. Thus $q\le36+4q/5+128$, giving $q\le820$. Also $f_0\le9+q$, by the total deficit after neighbor deletion. Undo the temporary pruning and set aside the chosen and short slots. Their count is $e\le1649$.

For each resulting clique $C_i$ put $d_i=r-|C_i|,\ \ell_i=e_J(C_i,V\setminus C_i),\ x_i=d_i/r$, and $a_i=\max(x_i,\ell_i/r^2)$. We claim
$$
                 \sum x_i\le 9/2,\qquad \sum a_i\le 11/2.               \tag{1}
$$
For $b_i>0$, at least $(r-1)b_i$ internal nontarget pairs avoid the clique interior. Subtract these from $B(r+b_i)-B(r-d_i)$ to bound the cut inside $R_i$ by $rd_i+B(b_i+1)-B(d_i+1)$. For $b_i\le0$, it is at most $rd_i$. The original $2X$ cross incidences include at least $rP/4$ at removed points. Since $B((b_i)_++1)\le b_i^2$, the deficit estimate gives
$$
 r^2\sum a_i\le r(P+O-1)+V_2+2X-rP/4\le5X+rO-r+V_2\le(11/2)r^2 .
$$
For the last bound use $5X+V_2\le10\eta+1$. Every retained point has at most $r/4$ target neighbors in the other retained cliques together.

## 2. Selecting the width by a weight threshold

Set
$$
 f=6/25,\quad \gamma=14/25,\quad \kappa=113/5000,\quad
 \alpha=\gamma f,\quad \beta^2=\kappa f,\quad k_0=2^{14}.
$$
For a level $z>0$, let $s(z)=e+k_0+1+\#\{i:a_i>z\}$. Define
$$
 A(z)=s(z)z,\qquad C(z)=\sum_{a_i\le z}x_i^2/z .
$$
Integrate $A/\alpha+\alpha C/(4\beta^2)$ against $dz/z$ between $\alpha 2^{-115}$ and $\alpha 2^{-14}$. Each row contributes at most $a_i$ to the integral of $z\#\{a_i>z\}$, and at most $x_i^2/a_i\le x_i$ to the integral of $C$. A zero weight contributes zero. By (1) the integral is at most
$$
 \frac{11}{2\alpha}+\frac{9\gamma}{8\kappa}
       +\frac{k_0+1650}{k_0}<69.90<101\log2 .
$$
Hence at some level the integrand is below one. At this level $A<\alpha$ and $AC<\beta^2$ by the arithmetic–geometric mean inequality. In particular $s=s(z)<2^{115}$. Omit the rows above the level and any $k_0$ additional rows. There are enough, since $s<r$. Put $h=s-1,\ \rho=f/s$. For the $r-h$ remaining ordinary cliques, define $D=\sum d_i,\ \sigma=\sum d_i^2,\ w=\sigma/r$. Then
$$
 d_i\le\gamma\rho r,\quad \ell_i\le\gamma\rho r^2,\quad
 w\le\kappa\rho r,\quad D\le9r/2,\quad \sum\ell_i\le11r^2/2.           \tag{2}
$$
We have $s\ge2^{14}$ and $r\ge R s^4$ with $R=2^{23}$, because $23+4\cdot115=483$.

Arbitrary lists of size at least $r/110$ in any subset of ordinary rows have independent representatives. Draw independently and uniformly. Every target-edge event has probability at most $110^2/r^2$. The events sharing either of its rows, including itself, number at most $2\gamma\rho r^2+1$. The symmetric Lovász local lemma applies since $4\cdot110^2(2\gamma\rho+1/r^2)<1$. All local-lemma applications below have these same ordinary lists.

The explicit affine square in the preceding draft had full rows with actual cut weights bounded by $1/(26i)$ in row $i$. These rows already pass the present pointwise test at $k_0$, because $1/26<\alpha$, and their squared deficits vanish. A scalar obstruction remains. Take $x_i=a_i=3/(40i)$ for $1\le i\le 2^{80}$. Its mass is below $9/2$. After any $h\le2^{74}$ deletions the least possible squared tail is obtained by removing the largest terms. Integration gives
$$
 (h+1)\sum_{i>h}^{2^{80}}x_i^2\ge (3/40)^2\big(1-(h+1)/(2^{80}+1)\big)>\beta^2 .
$$
This example establishes a limitation of (1) alone. Whether a coloring on $r^2+1$ points realizes a profile of this strength is open here.

## 3. A shortage of exterior vertices

Let $G$ contain all exterior points having at most $\rho r$ target neighbors in each ordinary row. Write $\Delta=hr-|G|$. We prove
$$
                    \Delta>cr,\qquad c=121/2000.                        \tag{3}
$$
An independent $h+1$ points of $G$ would leave at least $(1-\gamma\rho-f)r>r/110$ choices per ordinary row and extend to an independent $(r+1)$-set. Thus $\alpha_J(G)\le h$. If $|G|\ge hr+1$, take $X_0\subseteq G$ of order $hr+1$. Otherwise suppose $0\le\Delta\le cr$ and take $X_0=G$. Write $|X_0|=hr+b$, where $b=1$ or $-\Delta$.

For signed integers $v$, extend $p_k(v)$ by the same balanced-integer-parts formula. In particular $p_k(-v)=p_k(v)+v$ for $v\ge0$, and $p_k(kt+v)=kB(t)+tv+p_k(v)$. Applying the target and nontarget Turán floors on $X_0$ gives
$$
 0\le\eta_0=e_J(X_0)-p_h(hr+b)\le rB(h)+c^2r^2/2 .
$$
Indeed the upper bound before simplification is $rB(h)-(r-h)b+B(b)-p_h(b)-(r-1)p_r(b)$. With $\xi=c^2+2^{-40}$ we get $2\eta_0\le\xi r^2$, since $h^2/r<2^{-40}$.

Apply Füredi to the complement of the target on $X_0$ with $h$ parts. Write $V_0=\sum (|R|-r)^2$, $V_{\rm bal}$ for the balanced value and $X_a$ for the cross edges. Expansion of the internal binomials, using at most $\eta_0$ internal missing pairs, gives $2X_a+V_0\le M^2=4\eta_0+V_{\rm bal}$ and $X_a\le2\eta_0$. If $b=hq+j,\ 0\le j<h$, then $V_{\rm bal}=b^2/h+j(1-j/h)$. Consequently $M^2/r^2\le(2+2^{-14})c^2+3\cdot2^{-40}<\delta^2$, with $\delta=43/500$. Prune points of current interpart degree above $\tau r$, where $\tau=9/100>\delta$. For each part with original positive deficit $d=(r-|R|)_+$, its final deficit is at most
$$
 d+X_a/(\tau r)\le d+(M^2-d^2)/(2\tau r)\le M .
$$
If two survivors in a part were nonadjacent, every other part would retain at least $r/2$ common nonneighbors. Random representatives from them have at most $4\xi<1$ target edges in expectation. This would violate the target independence cap $h$. Thus there are $h$ auxiliary cliques of sizes at least $(1-\delta)r$. Arbitrary lists of size at least $r/10$ in them admit independent representatives by the same expectation bound, now $100\xi<1$.

In the positive case use just these auxiliary rows on $X_0$. In the other case use them together with the ordinary rows on all vertices. For this step temporarily remove from each ordinary clique the points with degree above $r/32$ outside its original clique. At most $32\ell_i/r$ are removed, leaving at least $(1-33\gamma\rho)r\ge255r/256$. In either case there are $pr+1$ vertices and $p$ rows, with target independence cap $p$. Put $\theta=93/250$. Call an attachment large when its target degree to a row exceeds $\theta r$.

Prescribe either one exterior point and at most four mutually compatible representatives in different rows, or two independent exterior points. Suppose all exterior attachments to the rows still to be filled are small. Rows may be deliberately omitted. Fill auxiliary rows first. In the first case every prescribed representative forbids at most $\max(\tau,1/32)r$ per auxiliary row. In the two cases the remaining fractions are at least $1-\delta-\theta-4\tau$ and $1-\delta-2\theta$, both above $1/10$. In any ordinary row every auxiliary choice together costs at most $h\rho r\le fr$, because the auxiliary rows lie in $G$. The two available fractions are at least $255/256-\theta-f-4/32$ and $255/256-2\theta-f$, each above $1/110$. The list results therefore give the whole extension.

It follows that every exterior point has a large row. A point with a unique large row is complete to it, since one nonneighbor could be prescribed there. Two such points assigned to the same row are adjacent, since otherwise they could extend together while omitting it. Adjoin all these points to their respective cliques, giving deficits $v_i\le\delta r$. If $P_0$ exterior points remain, then $\sum v_i=P_0-1$, and every one has at least two large attachments to the rows before enlargement.

Two capacities will be used repeatedly. For any target clique $C_i$ of size $r-v_i$, and any $z$ exterior points $Y$,
$$
   \sum_{y\in Y}\big(d_J(y,C_i)+v_i\big)\le(r-1)v_i+z+B(z).
                                                                         \tag{4}
$$
Each nontarget hue needs at least $z-v_i$ edges on the union. Likewise two disjoint target cliques have at most $r-v_i-v_j+v_iv_j\le r+v_iv_j$ target edges between them, since each nontarget hue needs at least $r-v_i-v_j$ edges there.

Write $t=133/500$. A row has fewer than $\lfloor tr\rfloor$ remaining large arrivals. Otherwise (4), applied to that many points at the enlarged row, would give
$$
 \theta(t-1/r)<(1-t+1/r)\delta+t^2/2+t/(2r),
$$
which fails for $r\ge2^{20}$. Each row's term $z+B(z)$ is therefore at most $z(tr+1)/2$.

Consider a point with exactly two large rows, and let $u_1,u_2$ be its two degrees divided by $r$ before enlargement. If $u_1+u_2\le1+t+1/r$, then both are at least $\theta$ and both are at most $1+t+1/r-\theta$. Its two nonneighbor lists have product at least
$$
 r^2(1-\delta-\theta)(\theta-\delta-t-1/r)>r+\delta^2r^2 .
$$
Indeed the product of the two lower bounds $1-\delta-u_i$ is smallest at maximal sum, then at an endpoint by concavity. The factors there are positive. The two-clique cut bound gives a compatible pair, which would extend with this point by the preceding extension. Thus its two arrivals together, after paying $(tr+1)/2$ apiece, contribute more than $r$.

For exactly $j=3,4$ large rows, use $\lambda_3=153/1000,\ \lambda_4=43/200$. If all nonneighbor lists had size at least $\lambda_jr$, independent random representatives would meet at most $B(j)(1/r+\delta^2)/\lambda_j^2<1$ target edges in expectation and could extend with the point. One attachment exceeds $(1-\delta-\lambda_j)r$. The net charge in units of $r$ exceeds $1-\delta-\lambda_j+(j-1)\theta-j(t+1/r)/2>1$. For $j\ge5$, use $5(\theta-(t+1/r)/2)>1$. Applying (4) to these arrivals at all enlarged rows now gives $rP_0\le r\sum v_i$, impossible since $\sum v_i=P_0-1$. This proves (3).

## 4. Sampling and circular arcs

Use the original ordinary cliques. There are $D+\Delta+1$ exterior points outside $G$, called senders. A strong attachment is one of degree greater than $r/2$. Assign a sender with at least two strong attachments to two of them, a sender with a unique strong attachment to that row, and call the others moderate. At row $i$, let $b'_i$ be its strong assignment count and $N_i$ its count of unique strong senders. Applied to $2d_i+1$ strong arrivals, (4) would require $r/2<d_i+1$. Thus $N_i\le b'_i\le2d_i$.

At a unique strong sender let $q$ be its target-neighbor fraction in its row. Draw a uniform representative there. If the first draw hits a neighbor, make a second independent uniform draw with probability $\lambda=4\rho$. Keep the first nonneighbor obtained. The success probability is $v=(1-q)(1+\lambda q)$. All successes and all moderate senders are eligible. Trials are independent between senders. The strong degree plus the row deficit is at least $rq$. Since $q\ge1/2$ and $\lambda q\ge\rho(1+\lambda q)$, it pays at least $r(1-v)+\rho r v$. The two assignments of a multiply strong sender pay at least $r$ together.

Let $A$ be the expected eligible count and $L=D+\Delta+1-A$. Summing (4) on the strong assignments gives $rL\le rD+2\sigma$, using $\sum b'_i/2\le D$. Hence $A\ge\Delta+1-2w>0$. Mark eligible senders independently with probability $p=\min(1,\Delta/A)$. Put $Z$ for the marks, $W=G\cup Z$, $m=\mathbb E|Z|$, $u=\Delta-m$. Then
$$
            0\le u\le2w,\qquad (c-2\kappa\rho)r\le m\le hr .           \tag{5}
$$

Add edges on $W$ to impose three conflicts. Two marks bringing representatives in the same row conflict. A representative that sees another exterior point creates a conflict between their exterior points. Representatives in different rows that see one another also create a conflict. For any other row $i$, the load $t_{xi}$ of a marked sender is its degree into $C_i$ plus its representative's degree there, omitting the latter for moderate senders. Give load zero in the sender's represented row and for unmarked senders. Every positive load is at most $3r/4$, by the definition of a unique strong row and the $r/4$ interpart degree bound.

In each row give every mark with $t_{xi}>\rho r$ an arc of $4t_{xi}$ consecutive positions on a circle of $3r$ positions, with independent uniform starts. Intersecting arcs create an edge between their senders. In an independent $h+1$-set of the repaired graph, the heavy loads in an unrepresented row sum to at most $3r/4$, by disjointness of their arcs. The other points and loads together cost at most $(h+1)\rho r=fr$. The available fraction $1-\gamma\rho-3/4-f$ exceeds $1/110$. Thus Section 2 fills the unrepresented rows. Together with the selected exterior points and their compatible representatives this would give $r+1$ independent vertices. The repaired graph has independence at most $h$ for every sample and every choice of starts.

Let $E_i=\mathbb E e_J(C_i,W)$, let $F_i$ be the expected sum of degrees into $C_i$ from representatives in other rows with multiplicity, and let $n_i$ be the expected number of heavy loads in row $i$. Write
$$
 Q=\sum n_i(E_i+F_i)/r,\quad Q_F=\sum n_i F_i/r,\quad
 T=\sum N_i E_i/r,\quad B_n=\sum n_i d_i/r .
$$
Two arcs of lengths $a,b$ intersect for at most $a+b$ relative starts, since the start difference must be a difference of two positions in the length intervals. Conditional on the sender trials, the collision probability of two heavy arcs is at most $4(t_{xi}+t_{yi})/(3r)$. Sum over unordered pairs and expand into ordered terms. For distinct senders the heavy indicator of one is independent of the load of the other. Also $\sum_x\mathbb E t_{xi}\le E_i+F_i$. Thus the expected cost of the arc edges is at most $4Q/3$. Counting only pairs of distinct senders avoids a diagonal contribution.

A specific representative has marginal probability at most $(1+4\rho)/|C_j|\le1.005/r$ for a particular sender in row $j$, at any thinning probability. Hence $F_i\le\ell_i/512$ by $N_j\le2d_j$. Since $\rho r n_i\le E_i+F_i$ and $E_i\le\ell_i$, (2) gives $\sum n_i\le23sr$, $\sum N_i\le9r$, $\sum n_i^2\le Q/\rho$, and $B_n\le\sqrt{\kappa Q}$. The two-clique bound also gives
$$
 F_i\le(1.005/r)\sum_{j\ne i}N_j(r+d_jd_i)\le10r+2.02wd_i,
 \qquad Q_F\le230sr+2.02w\sqrt{\kappa Q}.                               \tag{6}
$$

Let $P_*$ count distinct added edges. The conflicts from a representative hitting another exterior point cost at most $1.005T$, by independence from each other sender and deterministic membership of $G$. A representative misses its own sender. If $b$ unique strong senders are marked in expectation in a row, their same-row conflicts cost at most $b^2/2$ by independence. We have $b\le(1+4\rho)N_i/2$ by the success probability, and $b r/2\le E_i$. The sum of these first two costs is at most $1.51T$. Distinct-row representative conflicts cost at most
$$
 \frac{1.005^2}{r^2}\sum_{i<j}N_iN_j(r+d_i d_j)\le243r+2.1w^2,
$$
by $\sum N_i\le9r$ and $\sum N_i d_i\le2\sigma$. Therefore at every thinning probability,
$$
                 \mathbb E P_*\le (4/3)Q+1.51T+2.1w^2+243r .            \tag{7}
$$

## 5. Charging repairs to the actual colors

Take a particular sample and a set $I$ of tested rows. Set $H=h+|I|\le r,\ v=hr-|W|,\ D_I=\sum_{i\in I}d_i,\ z=v+D_I$. On $U=W\cup\bigcup_{i\in I}C_i$, let $X_I=e_J(W,\bigcup_{i\in I}C_i)$, and let $Y$ count target edges between tested cliques. Let $a$ be the excess of the repaired edge count on $W$ over $p_h(|W|)$, and $b$ the sum of the excesses of all nontarget hues on $U$ over $p_r(|U|)$. They are nonnegative by the independence caps. Partitioning all pairs on $U$ and expanding the signed balanced-part formula of Section 3 gives
$$
\begin{aligned}
 P_*+rB(H)+\sum_{i<j\in I}d_i d_j+vD_I+B(v)-X_I
  =Y+a+b+(H-1)z+p_h(v)+(r-1)p_r(z).
\end{aligned}
$$
For example, before expansion $X_I+Y=B(|U|)-\sum_{i\in I}B(r-d_i)-p_h(|W|)+P_*-a-(r-1)p_r(|U|)-b$. The right side of the displayed identity is nonnegative even for negative $z$, since $p_r(z)\ge-z$ then. All Turán applications concern actual graphs of nonnegative order.

Test rows independently with probabilities $\pi_i$, independently of the sender trials and arc starts. With $B_\pi=\sum\pi_i d_i$, the expected cut satisfies
$$
 \sum\pi_i E_i\le \mathbb E P_*+r\mathbb E B(H)+(B_\pi+u)^2/2+m/2 .    \tag{8}
$$
Indeed $\mathbb Ev=u,\ \operatorname{Var}(v)\le m$ by independent marking outcomes. For a single fixed row the last two terms can instead be bounded by $ud_i+u^2/2+m/2$, because the pair-of-rows sum vanishes.

Take $a_0=89/50$ and $\pi_i=(a_0n_i+2N_i)/r$. These are valid since $\pi_i\le a_0(513/512)\gamma+4\gamma\rho<1$. Also $\sum\pi_i\le42s$, so $\mathbb EB(H)\le ((43s)^2+42s)/2<925s^2$. The left side of (8) is $a_0(Q-Q_F)+2T$, while $B_\pi\le a_0\sqrt{\kappa Q}+4w$. Combining (5)–(8), expand the square and absorb its mixed term together with the mixed term from $a_0 Q_F$, using
$$
  a_0(6+2.02)w\sqrt{\kappa Q}
  \le Q/10+(5/2)[a_0(6+2.02)]^2\kappa w^2 .
$$
This yields
$$
\begin{aligned}
 (a_0-4/3-a_0^2\kappa/2-1/10)Q+(2-1.51)T
 &\le \big(2.1+18+(5/2)[8.02a_0]^2\kappa\big)w^2+928s^2r .
\end{aligned}
$$
Multiplying by $4.29$ dominates $(4/3)Q+1.51T$. Using (7) and then (8) for one row gives
$$
 \mathbb E P_*\le138w^2+3992s^2r,\qquad
 E_i\le140w^2+2wd_i+3993s^2r .                                          \tag{9}
$$

If $A>\Delta$, let $z'=\min(A-\Delta,\Delta/128,r/16)$ and use $p'=(\Delta+z')/A<2p$. Then $Q'\le4Q,\ T'\le2T$, by linear scaling of each sender trial and the fixed set $G$. Applying (7) and the same bound on $(4/3)Q+1.51T$ limits $\mathbb E P'_*$ to $4(138w^2+3992s^2r)$. Conversely, if the oversample has size $hr+b'$, the target floor on the repaired graph and the actual nontarget floors give
$$
 P'_*\ge(r-h)b'-B(b')-rB(h).
$$
For $b'\ge0$, expanding the floors adds the nonnegative terms $p_h(b')+(r-1)p_r(b')$ to the right side. For $b'<0$ the displayed right side is nonpositive. Since $\mathbb E b'=z'\le r/16$, $h\le r/4$, and $\operatorname{Var}(b')\le\Delta+z'\le sr$, this gives $\mathbb E P'_*\ge rz'/2-rs^2$. Hence
$$
 z'\le1110w^2/r+32000s^2 .
$$
Divided by $r$, this is at most $1110\kappa^2\rho^2+32000/(Rs^2)<\min(c/128,1/16)$. By (3), only $A-\Delta$ can attain the minimum. Also allowing $A\le\Delta$, we obtain
$$
                         L\ge D-1110w^2/r-32000s^2.                     \tag{10}
$$

## 6. The last capacity inequality

Assign each moderate sender in advance to a row where its degree exceeds $\rho r$. Let $v_i$ count those marked in the base sample at row $i$, with mean $\bar v_i$. Since $\rho r\bar v_i\le E_i$, (2) and (9) give
$$
 \bar v_i/(\rho r)\le 140\kappa^2+2\kappa\gamma+3993/(f^2R)
 <\epsilon,\qquad \epsilon=211/2000 .
$$
We have $\operatorname{Var}(v_i)\le\bar v_i$ and $\sum\bar v_i\le m$. In (4) use all strong assignments and all marked moderate assignments. The expected charge on the left is at least $rL+\rho r m+\sum d_i\bar v_i$. This keeps the deficit paid by each moderate assignment. The unique strong surplus from Section 4 pays $\rho r$ for an expected successful mark, since $p\le1$.

On expanding $(b'_i+v_i)(b'_i+v_i+1)/2$, the strong squares cost at most $2\sigma$, and the strong linear terms cancel the subtraction of $D$ in $(r-1)D$. The mixed terms minus the moderate deficit charge cost at most $\sum d_i\bar v_i$, because $b'_i\le2d_i$. This is bounded by $\sqrt{\sigma\epsilon\rho r m}$ using Cauchy–Schwarz. The moderate squares and linear terms cost at most $\epsilon\rho r m/2+m$. By (10),
$$
 (1-\epsilon/2)\rho r m\le
  2wr+\sqrt{\sigma\epsilon\rho r m}+1110w^2+32000s^2r+m .
$$
By (5), the square-root term divided by $\rho r m$ is at most $\sqrt{\epsilon\kappa/(c-2\kappa\rho)}<199/1000$. Dividing by $\rho r^2$ and using $r\ge Rs^4$, $m\le sr$, would force
$$
 (1-\epsilon/2-199/1000)(c-2\kappa\rho)
   \le 2\kappa+1110\kappa^2\rho+32001/(fRs).
$$
At $s=2^{14}$ the left side exceeds the right by more than $1/20000$. The margin increases with $s$. This contradiction proves Theorem 1.

## 7. Three nearly full rows at 19

Suppose $r=19$ and write $N=362$. We first select 19 independent vertices, called roots, with a bound on their total closed degrees. For a vertex $v$ put $l_v=1+d_J(v)$. By sparsity $\sum l_v\le20N$. The local minima of a uniform random vertex ordering, each compared with its closed neighborhood, form an independent set. Thus $\sum1/l_v\le19$.

Let $L_0=222/5,\ A_0=88/5,\ w(l)=(L_0-\max(l,A_0))_+$, and $g(l)=w(l)/l$. Among positive-weight vertices choose an independent set of maximum weight, breaking ties by maximum size $t$. Its weight $W_0$ is at least $\sum_v g(l_v)$ by the same ordering argument. Write $q_y$ for the number of roots in the closed neighborhood of $y$. All positive-weight points are dominated by the chosen set. For each root take itself and its uniquely dominated neighbors with closed degree at most 31. These form a clique. Otherwise two nonadjacent private points could replace the root, preserving weight or improving it, since each has at least half the maximum possible weight. The exchange increases the cardinality in case of a tie.

The resulting cliques cover at most $19t$ points. Put $I(l)=\mathbf1_{l>31}+\mathbf1_{l\ge45}$. On the uncovered points, $1\le q_y-1+I(l_y)$, and on the covered points the right side is nonnegative. Indeed an undominated point has zero weight, and an omitted uniquely dominated point has closed degree above 31. Finally $\sum q_y=\sum_{u\text{ root}}l_u\le L_0t-W_0$. Together these give
$$
                       2N\le(19+L_0)t-\sum_v(g(l_v)-I(l_v)).
$$
For each possible integer closed degree,
$$
 g(l)-I(l)\ge791/130-(73/390)l-4414/(195l).
$$
Multiply the difference by $390l$. On the four successive integer ranges ending at 17, 31, 44 and 362, the resulting polynomials are
$$
 (l-16)(73l-1205),\quad(l-19)(73l-1376),\quad(l-32)(73l-817),\quad
 73l^2-3153l+8828 .
$$
Each is nonnegative at the integers in its interval. Summing gives $2N-(19+L_0)18+\sum(g-I)\ge11/65$, so $t=19$. Also $g(l)\ge L_0/20-1-(L_0/400)(l-20)$. For $18\le l\le44$ multiply by $l$ and use $(l-20)^2\ge0$. For $l\le17$ the difference times $1000l$ is $111l^2-3440l+26800>0$, and for $l\ge45$ the lower bound is negative. It follows that
$$
             \sum_{u\text{ root}}l_u-N\le(19-N/20)L_0=999/25<40 .
$$

All vertices are dominated since there are 19 independent roots. The root $u_i$ and all its uniquely dominated neighbors form a private clique $C_i$. Two nonadjacent private neighbors could replace $u_i$ to make 20 independent points. Put $d_i=19-|C_i|$, and let $P$ be the exterior vertices. For $x\in P$, let $T_x$ be its neighboring roots. Counting vertices and then closed incidences gives
$$
       |P|=1+\sum d_i,\quad |T_x|\ge2,\quad
       \sum_{x\in P}(|T_x|-1)=\sum_{u\text{ root}}l_u-N\le39 .
                                                                         \tag{11}
$$
In particular $\sum d_i\le38$ and at least seven rows have size at least 17.

If $T_x=\{i,j\}$, write $p_i,p_j$ for its nonneighbor counts in those two cliques. Their nonneighbor lists must form a complete target bipartite graph, since a missing cross edge would extend $x$ with the other 17 roots to an independent 20-set. On $C_i\cup C_j\cup\{x\}$, each of the other 18 hues needs at least $20-d_i-d_j$ edges. Counting the nontarget pairs available gives
$$
 p_i p_j\le e_J(C_i,C_j)\le p_i+p_j+(d_i-1)(d_j-1),\qquad
       (p_i-1)(p_j-1)\le1+(d_i-1)(d_j-1).                              \tag{12}
$$

First rule out a packing with no full row and at most one size-18 row. If all deficits are at least two, (11) forces every deficit to equal two and all exterior points to have two roots. With exactly one deficit equal to one, the possible totals are 37 and 38. At 37 the other 18 deficits are two. At 38 one is three and the other 17 are two. In all these profiles (12) forces each two-root point to miss at most two vertices in one of its rows. If both counts were at least three, the left side would be at least four whereas the right side is at most three. Assign each such point to one such row. A row can receive at most $d_i$ assignments, since the row with $d_i+1$ arrivals has order 20 and at most $2(d_i+1)+B(d_i+1)\le14<18$ nontarget pairs.

At total deficit 38, all 39 exterior vertices have exactly two roots by (11), exceeding that capacity. At total deficit 37, at most one has three roots and none has four. If all have two, capacity again fails. Otherwise the 37 two-root points fill every row's capacity. In row $i$, its clique and its $d_i$ assigned points form a 19-set $W_i$ containing at most $2d_i+B(d_i)\le5$ nontarget pairs. Every additional point must therefore see at least 13 different nontarget hues on its edges to $W_i$. The three-root point misses at least 11 vertices in each of its three private rows, since it sees at most six target edges into each $W_i$ and each row has size at least 17. Each pair of rows has at most 19 target edges by the two-clique bound in Section 3. Independent uniform choices from the three lists have at most $3\cdot19/11^2<1$ target edges in expectation. Compatible choices together with the point and the 16 untouched roots give 20 independent vertices.

Now suppose exactly two rows have deficit one and all others have deficit at least two. Write $D=\sum d_i=36+e$, with $e\in\{0,1,2\}$. Equation (11) gives $\sum_{x\in P}(|T_x|-2)\le2-e$. Two exterior points with the same two roots that share a nonneighbor in either of their two rows must be joined in $J$. Otherwise those two points, the common nonneighbor, and the 17 untouched roots are independent.

When $e=2$, every exterior point has two roots. If one row has deficit four, assign each point where it misses at most one in that row or at most four in a row of deficit one or two, whenever possible. Equation (12) leaves exactly one exception type. Its two deficits are four and two, and it misses respectively two and five points. Their forced rectangle already uses all ten permitted target edges in the cut by (12). Thus all exceptions for any fixed pair of rows miss the same sets and are pairwise adjacent in $J$. Assign them to the deficit-two row. Four or five missed points per arrival give the following capacity test. At three arrivals in a deficit-two row the number of nontarget pairs is at most $3\cdot5+3=18$. Equality requires three exceptions and all three edges between them to be nontarget. Those exceptions have the same other root, contradicting their adjacency. A deficit-one row with two arrivals has at most nine nontarget pairs. The deficit-four row with five arrivals has at most 15. Thus every row receives at most its deficit.

The other $e=2$ profile has two deficit-three rows. Assign a point where it misses at most two in a row whenever possible. Every exception has those two deficit-three roots and misses three in each by (12). Their cut has at most ten target edges and contains a $3$-by-$3$ rectangle from each exception. Two different such rectangles have union of size at least twelve. Therefore the exceptions share their missed sets and are pairwise adjacent in $J$. Assign them to the same one of the two rows. Four arrivals in a deficit-three row have at most $4\cdot3+6=18$ nontarget pairs. Equality would require four mutually nonadjacent exceptions. Rows with smaller deficits satisfy the earlier strict capacity test. Both $e=2$ profiles would assign $D+1$ points to total capacity $D$.

When $e\le1$, at most one row has deficit three. Equation (12) assigns every two-root point with at most two misses in its row, and each row again has capacity $d_i$. Call a row full to capacity if it receives $d_i$ assignments. For any unassigned point, a row full to capacity gives at least $19-d_i-1-2d_i-B(d_i)$ nonneighbors in its private clique by the 19-set argument above. This is at least 11 for $d_i\le2$ and six for $d_i=3$.

If there is exactly one unassigned point, all rows are full to capacity. At $e=1$ it has three roots, at most one in a deficit-three row. The expected target-edge count of uniform choices in its three lists is at most $20(2/(6\cdot11)+1/11^2)<1$. At $e=0$ it has at most four roots, giving at most $6\cdot19/11^2<1$. If no point is unassigned, capacity already fails.

The last possibility is $e=0$ with two three-root points. All but one row are full to capacity, and the remaining row is short just one assignment. Either point whose support avoids that row extends by the three-list estimate. If both touch it, let $W$ consist of its clique and its $d_i-1$ assigned points. This 18-set has at most two nontarget pairs. With both three-root points it has order 20, so at least 15 nontarget edges run from them to $W$, allowing one more on their mutual pair. At most two of the 15 meet an assigned point. One of the two therefore has at least seven nonneighbors in the private clique. Its other two lists each have at least 11 choices. The expected target-edge count is at most $19(2/(7\cdot11)+1/11^2)<1$, again giving 20 independent vertices. This proves the clique alternative of Theorem 2.

## 8. Alignment in the other colors

Let $C_1,\ldots,C_b$ be disjoint target cliques of sizes $r-d_i$ in a hypothetical counterexample, with $2\le b\le r$ and $D_b=\sum d_i\le r$. Write $U=\bigcup C_i$ and $T=\sum_{i<j} e_J(C_i,C_j)$. For each other hue $a$, let $s_a=e_a(U)-p_r(|U|)$. Its graph on $U$ has a family of at least $r-D_b-s_a$ vertex-disjoint monochromatic $b$-cliques, each meeting every $C_i$. Moreover
$$
 \sum_{a\ne J}s_a=\sum_{i<j}(r-d_i-d_j+d_i d_j)-T .                    \tag{13}
$$
Indeed the $r$ balanced sizes for $br-D_b$ are $b$ and $b-1$, giving $p_r(|U|)=rB(b)-(b-1)D_b$. All nontarget pairs cross between the rows. Subtract the $r-1$ floors from $\sum_{i<j}(r-d_i)(r-d_j)-T$ to obtain (13). Füredi's theorem in the complement of hue $a$ provides $r$ parts with at most $s_a$ missing internal hue edges. Remove one endpoint of each such pair, losing at most $s_a$ vertices. Every surviving part is an $a$-clique of size at most $b$, with at most one point in each target row. Its deficit from $b$, summed over the $r$ parts, is at most $D_b+s_a$. Each incomplete part uses at least one unit. This proves the family bound for every hue simultaneously.

For three 18-cliques at 19, (13) gives $\sum s_a=54-T$. Thus at least $18\cdot16-(54-T)=234+T$ transversal triangles can be selected across the 18 hues, vertex-disjoint within each hue. In the full-row branch of Section 7 choose that row and trim two other private rows of size at least 17 to size 17. The sizes $(19,17,17)$ give $\sum s_a=53-T$, and at least $18\cdot15-(53-T)=217+T$ transversal triangles. In either branch some nontarget hue supplies at least 13 vertex-disjoint triangles. This finishes Theorem 2.

**An exact test on exterior sets.** When $s_a=0$, the $a$-graph on $U$ is exactly the disjoint union of $r$ balanced cliques. This is the equality case of the Turán floor. Call these cliques blocks. For any $a$-independent exterior set $S$, let $c_a(S)$ count blocks whose every vertex has an $a$-neighbor in $S$. The largest $a$-independent set obtained by extending $S$ into $U$ has exactly $|S|+r-c_a(S)$ vertices. Each block that has a surviving vertex supplies one, and distinct blocks have no $a$-edges between them. Thus $c_a(S)\ge|S|$ is necessary and sufficient for this particular $S$ to pass the test. In particular, if a pair $x,y$ covers at most one block for each of two distinct zero-surplus hues, one of the hues differs from the label of $xy$ and the test supplies a witness.

When all $r-1$ nontarget hues have zero surplus on three rows of size $r-1$, this test already gives a simultaneous restriction on each exterior vertex $x$. Each hue must have an entire block adjacent to $x$, and every block has at least two points. If $k_x$ hues have just one entire adjacent block, the $3(r-1)-d_J(x,U)$ nontarget edges from $x$ include at least $2[k_x+2(r-1-k_x)]$ edges. Hence $k_x\ge\lceil(r-1+d_J(x,U))/2\rceil$, at least nine at order 19. Two vertices can cover another block jointly even if neither covers it alone.

**An exact pair test with positive surplus.** Use any of the partitions from Füredi's theorem above, before removing points. If it has $\mu\le s_a$ missing internal hue edges, its number of cross hue edges is
$$
 e_{\rm cross}=s_a+\mu-\big(\textstyle\sum_i B(|R_i|)-p_r(|U|)\big)\le2s_a.
$$
For two exterior points $x,y$ form $L_i=R_i\setminus(N_a(x)\cup N_a(y))$. For each cross hue edge select one endpoint, collecting the selected endpoints in a set $D$. Then
$$
 M_a(x,y)=\alpha_a\!\left(\textstyle\bigcup L_i\right)
     =\max_D\sum_i\alpha_a(L_i\setminus D).                              \tag{14}
$$
For any selection all surviving cross hue edges disappear. Conversely an independent set omits at least one endpoint of every cross edge, so some selection preserves all of it. If $M_a(x,y)\ge r-1$, the pair $xy$ must have hue $a$. Two hues imposing this on the same pair prove the conjectured conclusion for that coloring.

In both size profiles at 19 the total surplus is at most 54. At least five of the 18 hues therefore have $s_a\le3$. For each such hue (14) requires at most $2^6=64$ endpoint selections. Within a part at most three pairs miss the hue, so the largest independent subset is found by checking singletons, missing pairs and triangles of missing pairs. This gives an exact small computation per hue and pair if the coloring is supplied. A proof at 19 must still force a witness for every possible coloring.

**A square where every cut attains equality.** Take a prime $r\ge7$ and give every nonvertical edge of $\mathbb F_r^2$ its finite slope as color. Let $J$ be slope zero. In each of the three rows $y=0,1,2$, omit the point at abscissa zero from the chosen row. Give the $3r$ vertical pairs between the three original rows color $J$. Distribute all other vertical pairs among the $r-1$ nontarget hues as evenly as possible. Before coloring the verticals all finite slopes have equal size. Since $3r\le B(r)$ and there are $rB(r)$ vertical pairs, each nontarget hue can receive at least $3r$. Thus $J$ is sparsest. Every $(r+1)$-set on this square sees all hues by the pigeonhole principle on each slope's $r$ parallel lines.

On the three trimmed rows every target cut is a matching of size $r-1$. Each other hue has exactly $r-2$ edges per cut. Its parallel lines induce $r-3$ triangle blocks and three edge blocks, since the three omitted points lie on distinct lines of every nonzero finite slope. This realizes exact alignment for all $r-1$ hues at once.

Keep this entire square and duplicate $v=(0,3)$. Copy its labels to the other old points and give the edge between the twins any nontarget hue. Each nontarget hue gains at least $r-1$ edges at the copy, and $J$ gains exactly $r-1$, so $J$ is still sparsest. Every $(r+1)$-set avoiding at least one twin projects injectively to the balanced square. For each nonzero finite slope differing from the twins' mutual label, the twins together cover just the one triangle block on their common line through $v$. All other blocks retain every point, because the strip omits abscissa zero. The preceding test gives an explicit $(r+1)$-set missing that hue. At 19 this exhibits 17 different missing hues, each witnessed by the two twins and 18 points in the three rows.

## 9. Forcing an edge-label conflict for an arbitrary new star

We prove Theorem 3 for any affine plane of order $r\ge7$. This includes the planes over finite fields of prime-power order. Designate two parallel classes as horizontal and vertical. Give horizontal pairs color $J$ and give each of the remaining nonvertical directions its own hue. Choose three horizontal lines and omit their points on one fixed vertical line. Their trimmed union is $U$. In the coordinate example these are the rows used in Section 8. At every admissible $r\ge11$ the target can be sparsest on the original square.

Give the $3r$ vertical pairs between the three original rows hue $J$. Designate one nontarget direction $a_0$ and give it every vertical pair from an old exterior point into $U$. These prescriptions are disjoint. The remaining vertical pairs may have any nontarget hues. The square is balanced by the parallel-line argument. For the optional sparsity assertion, the number forced to $a_0$ is $3(r-1)(r-3)$, already at least $3r$. After reserving $3r$ for $J$, enough vertical pairs remain to give each of the other $r-2$ hues at least $3r$, because the excess is $(r-1)(r^2/2-6r+9)\ge0$ for $r\ge11$.

Every nontarget hue has its $r$ blocks on $U$ as in Section 8. A nontarget line meets each original row once and at most one of the three omitted points, so its block has size two or three. For any old exterior point $x$ and any nontarget direction $a\ne a_0$, its neighbors in hue $a$ on $U$ are precisely the block on its line of direction $a$. Assume first that $z$ passes every test with $U$ alone. At least $\lceil(r-1)/2\rceil$ hues have just one entire block adjacent to $z$. Discard $a_0$. At least two of the remaining directions $a,b$ have this property. Their selected blocks are disjoint in $U$, since an edge from $z$ cannot have both colors. Their two lines have different directions and meet in a unique old point $x$, necessarily outside $U$. In each of the two hues, $x$ adds no neighbors outside the single block already covered by $z$. Hence $x,z$ cover exactly one block in hue $a$ and exactly one in hue $b$. The edge $xz$ cannot supply both. Choose a point in every other block avoiding both in the missing hue. With $x,z$ this gives the claimed $(r+1)$-set. If $z$ failed the first test, Section 8 already supplies a witness with $z$ alone.

This also bounds the amount of recoloring needed to evade this particular certificate. Keep all edges within $U$ fixed, and allow changes on old exterior-to-$U$ pairs as well. Let $k\ge\lceil(r-1)/2\rceil-1$ be the number of single-block hues at $z$ after discarding $a_0$. If two of these hues gain no new old exterior-to-$U$ edge, their two selected lines still give a witness. Removing an old neighbor can only make extension easier. Thus at least $k-1$ distinct hues must gain a new such edge. Each recolored edge introduces one label, so at least $\lceil(r-1)/2\rceil-2$ old exterior-to-$U$ edges must change. This is seven edges at $r=19$, even with complete freedom on old pairs outside $U$.

**Why two rows give a different answer.** Keep the old balanced square and use only the first two trimmed rows as $U'$. Each nonzero slope has a matching of size $r-2$ and two isolated points on $U'$, one in each row. Every point of $U'$ is isolated for exactly one such slope, the slope of its line to the omitted point in the opposite row. Give its edge to $z$ that slope. In each nontarget hue $z$ now covers the two singleton blocks. At most $r-2$ mutually independent points of $U'$ in that hue can accompany $z$, so even a second exterior point cannot give $r+1$. Any tested set of size $r+1$ has at least $r-1$ points in the two rows and hence a target edge. Sets of old points are already balanced. Thus all tests using at most two exterior points pass on these two rows simultaneously. The proof with three rows uses line intersection outside the rows. For an arbitrary coloring the missing statement is how to recover enough such intersections, or find a different witness when (13) has positive surplus.

## Verification and the remaining problem

The manuscript gives a human-readable proof. The accompanying Python checkers verify rational constants, the integral bounds, finite arc counts, sampling formulas on examples, the seven deficit profiles in Section 7, and the actual edge labels and witnesses in the square construction. The Lean 4 files cover the cardinality and collision bounds for individual circular arcs and the capacity of disjoint arcs, the exact cut inequality for a nonnegative sample shortage, and an outside-degree bound used in the separate finite descent. The signed-shortage extension, global sampling argument, and both headline theorems are proved in the text. Independent mathematical review of this version is pending.

The power $483$ comes from $r\ge2^{23}s^4$ and the existence of a width $s<2^{115}$. The fourth power enters when the $3993s^2r$ error in (9) is divided by $\rho^2r^2$ in Section 6. For the smaller orders, one possible route is to derive a violation of the exterior-set test from (13), allowing positive surpluses and exploiting the extra vertex. Even at 19 the triangle families alone leave this unresolved. The separate descent on 115 points still permits a sparsest nontarget hue with 296 edges, a minimum independent-six-set weight of 11, and a packing of two, three, or four independent six-sets on the 97 points outside an 18-clique.
