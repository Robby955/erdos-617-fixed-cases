# The smaller mixed profile and a cutoff of $2^{190}$

Robert Sneiderman’s research notes · 22 November 2026

**Theorem 1.** For every integer $r\ge2^{190}$, every $r$-edge-coloring of $K_{r^2+1}$ contains $r+1$ vertices missing a color.

**Theorem 2.** Put $m=2^{24}$. In the packing of the 218 supplement, the proposed mixed profile is impossible in a counterexample for every $r\ge2^{53}$. With a new packing in the same sparsest color, it can be excluded for every $r\ge2^{27}$. Allowing a choice of color as well gives a packing excluding it for every $r\ge m$. Section 5 specifies all three choices.

For the profile, in row $i\le m$ the deficit is between the floor and ceiling of $r/[5(i+3)]$, and the foreign target-edge count is at most the ceiling of $r^2/[100(i+3)]$. Both quantities vanish after $m$. Zero entries may pad the sequence of rows. For the fixed packing the proof needs only the zero tail. For the two new packings the small *positive* cross counts are important.

The fixed packing for $2^{24}\le r<2^{53}$, the general conjecture for all $r\ge3$, and the project's $r=19$ case remain open here. The text uses the sampling and signed cut arguments of the preceding manuscripts. Independent mathematical review of the combined argument is pending. [218 supplement](cutoff-218.md) · [Exact arithmetic](verify_cutoff_190.py) · [Local Lean lemmas](Profile24.lean) · [Original conjecture](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf)

## 1. Distinct sources of large stars

Assume a counterexample. Fix a sparsest color $J$. Every color has independence number at most $r$ and every monochromatic clique has size at most $r$. Use the partition $R_i$ and qualifying destinations from §1 of [Appendix D](cutoff-218.md), including its first pruning stage at $r/4$. For each first-stage deletion record its source, one qualifying destination, and the *current* edges from that source into that destination. All recorded edge sets are disjoint. There are $pr$ sources. The preceding star bound gives at most
$$
 \omega r=\frac{5}{1464}r
$$
recorded sources per qualifying destination. Indeed its budget $U_i\le r^2/1200$ pays more than $(61/250)r$ per source. The upper bound on $p$ is $p_*=125/61$.

Use total interpart degree threshold $\tau r$, $\tau=99/200$, in the second pruning stage, with $tr$ deletions. Put $Z=1-p/4-\tau t\ge0$. Trim oversized parts to $r$, take a maximal family of $q$ jointly independent pairs in different parts, one pair per chosen part, and remove their neighbors in the unchosen parts. Each remaining list in an unchosen part is a clique. Use the two independent representative draws in [Appendix D](cutoff-218.md) with short-list cutoff $Lr$, $L=497/500$. Omit chosen parts, short lists and unqualified destinations.

Write $d_i=r-|C_i|,\ x_i=d_i/r$. Let $y_i' r^2$ count the edges of $J$ from $C_i$ outside $R_i$ after excluding the recorded edges. This discount is used only for bounding degrees and numbers of heavy senders. Write $b_i=|R_i|-r$. The budgets are
$$
 \sum x_i\le D_*=\tfrac12+p+t+2\tau Z/L^2,\qquad
 \sum y_i'\le Y_*=2-p/2-\tau t.                                      \tag{1}
$$
Indeed the original interpart edges have at most $2r^2$ endpoint incidences. Each fresh recorded edge loses **both** incidences in this count. Its source was deleted, and its other endpoint was either removed or discounted. Every fresh edge spent in the second stage loses at least one incidence. Inter-clique edges lose neither incidence through the discount.

For the first budget the padded draws give $q\le(1/2+p+t+Z)/(1-2\tau)$. In a short list of length $zr$, $0\le z<L$, the excess after paying $2\tau(1-z/L)r$ is at least $r\min(1-2\tau,1-L)$, by linearity in $z$. Thus the number of short lists is at most $D_*/\min(1-2\tau,1-L)$. On the trapezoid $0\le p\le p_*,\ t\ge0,\ Z\ge0$, the four corners give $D_*<18/5$ and fewer than $2399$ omitted parts, including the at most 728 unqualified ones. Let $e_0$ be the actual omission count.

For the width, use the threshold proof of [Appendix D](cutoff-218.md) with $y_i'$ replacing $y_i$. Give row $i$ weight $\max(y_i',\alpha x_i/(2\beta))$. With $s(z)=\max(K,e_0+1+\#\{\text{weights}>z\})$, integrate as in its §2. The integral costs at most $1+Y_*/\alpha+D_*/\beta$. In the following table $\alpha,\beta$ are displayed in thousandths. Choose a band containing $Y_*$.

| Band for $Y_*$ | $K$ | $b$ | $1000\alpha$ | $1000\beta$ |
| --- | ---: | ---: | ---: | ---: |
| $[0,5/8]$ | 2400 | 15 | 155 | 200 |
| $[5/8,7/8]$ | 2600 | 16 | 165 | 198 |
| $[7/8,9/8]$ | 2600 | 18 | 170 | 200 |
| $[9/8,11/8]$ | 2600 | 18 | 170 | 198 |
| $[11/8,13/8]$ | 2600 | 18 | 170 | 198 |
| $[13/8,2]$ | 2600 | 19 | 170 | 198 |

Set $R=2^b,\ S=2^{(190-b)/4}$. In each band the integral bound is strictly below $\log(S/K)$. Its maximum occurs at a vertex of the clipped trapezoid. The checker bounds the logarithms by the positive series for $2\operatorname{arctanh}$. As in the 218 proof, there is a width $K\le s<S$ and $0<v<1$ such that on the $r-h$ retained rows, $h=s-1$,
$$
 s\max y_i'\le\alpha v,\qquad s\max x_i\le2\beta v,\qquad
 s\sum x_i^2\le4\beta^2v(1-v),\qquad r\ge R s^4.                       \tag{2}
$$
For verification use upper bounds $A,X,B$ on the first three left sides. Split $v$ into 96 equal intervals, maximizing each right side separately on that interval.

## 2. Filling the auxiliary rows using their remaining edges

Write $f=7/30,\ \rho=f/s,\ \rho_0=f/K,\ \gamma=A/f,\ g=X/f,\ \kappa=B/f$. Let $G$ consist of exterior vertices with at most $\rho r$ target neighbors in each retained row, and let $\Delta=hr-|G|$. We prove
$$
                         \Delta>r/8.                                    \tag{3}
$$
The same argument gives a separate restriction theorem. If $1\le h\le r,\ r\ge2^{20}$ and $h^2/r\le100/3199$, no set of $hr+1$ vertices can have target independence at most $h$ and independence at most $r$ in every other color in a counterexample.

Inter-clique edges are undiscounted, so $4\cdot61^2A/K<1$ supplies independent representatives on arbitrary ordinary lists of size at least $r/61$, by the counting lemma in [Appendix E](cutoff-289.md). In particular independent $h+1$ vertices of $G$ would extend. For the later temporary ordinary restriction remove the vertices whose foreign degree from unrecorded edges exceeds $r/44$. At most $44y_i'r$ points are removed from $C_i$. Each surviving point has at most $\omega r$ incident recorded edges, since each recorded source offers it one edge. Thus the temporary rows have size at least $255r/256$ and degree from each survivor outside its original clique at most $r/32$. The two numerical inequalities are $(g+44\gamma)\rho_0<1/256$ and $1/44+g\rho_0+1/256+\omega<1/32$.

For (3), suppose $\Delta\le cr$, $c=1/8$. Take $hr+1$ points of $G$ if available and otherwise take $G$. The target independence cap there is $h$. In the restriction theorem take the given $hr+1$ points instead. Apply the stability calculation of base §3 on these auxiliary points. Normalize edge counts by $r^2$ and lengths by $r$. Write $u_i=(r-|R_i^{a}|)_+/r$ for raw positive deficits of the auxiliary parts and $x$ for their total interpart edge count in these units. With $I=2^{-20}$ we have
$$
 x\le \xi,\qquad \sum u_i\le D,\qquad 2x+\sum u_i^2\le T .
$$
For (3) use $\xi=c^2+I,\ D=c+\xi/[2(1-I)],\ T=(2+1/799)c^2+3I$. These are [Appendix E](cutoff-289.md)'s estimates using $h\ge799,\ h^2/r<I$. The sum bound follows by charging the overfull parts to the other colors and adding the net deficit. For the restriction theorem use $\xi=100/3199,\ D=\xi/[2(1-I)],\ T=2\xi+I$. In fact the target excess over the balanced $h$-part floor on $hr+1$ is at most $r\binom h2-(r-h)$, by the other $r-1$ Turán floors. The balanced sum of squared deviations from $r$ is one, and the net deficit is negative. These facts give the displayed bounds also when $h=1$.

Prune auxiliary vertices of current interpart degree above $\tau_a r$. If the number pruned is $zr$, then $0\le z\le x/\tau_a$ and the remaining interpart edge count is at most $x-\tau_a z$. The final normalized positive deficits have sum at most $D'=D+\xi/\tau_a$, and each is at most
$$
     \delta=D+(T-D^2)/(2\tau_a).
$$
Indeed $u_i+x/\tau_a\le u_i+(T-u_i^2)/(2\tau_a)$, increasing up to $D<\tau_a$. For (3) take $(\tau_a,\theta_a,k)=(206/1000,411/1000,72/100)$. For the restriction take $(216/1000,406/1000,77/100)$. The surviving auxiliary parts are cliques. A nonedge in one would leave lists of fraction $1-\delta-2\tau_a>0$ in the others, whose square exceeds $\xi$. Uniform choices therefore extend the pair to $h+1$ independent vertices.

Call an attachment large above $\theta_a r$ in an auxiliary row or above $\theta_o r$, $\theta_o=369/1000$, in an ordinary row. We need extensions with one exterior point and at most **two** compatible prescribed representatives in distinct rows, or with two independent exterior points and no representatives. The rows to be filled have only small attachments from these exterior points. Some rows may be omitted.

Fill auxiliary rows first. Fix two unfilled auxiliary rows with raw deficits $u_1,u_2$. For two exterior points put $w=1-2\theta_a$. The initial lower bounds on their list fractions are $w-u_1,w-u_2$. Their product exceeds $x$, since
$$
 2(w-u_1)(w-u_2)+u_1^2+u_2^2
       = w^2+(w-u_1-u_2)^2\ge w^2+(w-D)^2>T .
$$
Here $w>D$. For one exterior point put $w=1-\theta_a$. The prescribed representatives can delete in total at most $2\tau_a r$ points across the auxiliary rows, since each auxiliary representative has this total interpart degree bound with factor $\tau_a$, and an ordinary one has the smaller $r/32$ bound. In either case write $b_1\le b_2$ for the sorted numbers $w-u_i$, and set $t=0$ in the two-exterior case and $t=2\tau_a$ in the one-exterior case. The final product is at least $b_2(b_1-t-z)$. This bound follows by charging both losses against the larger factor. At $z=0$ it exceeds $x$, using $(1-\theta_a-D-2\tau_a)(1-\theta_a-D)>\xi$ in the second case. At $z=x/\tau_a$ it is positive, since $w-t>\delta$ and $u_i+x/\tau_a\le\delta$. Linearity now gives a product greater than $x-\tau_a z$ at the actual pruning count. Each individual list is nonempty by the same endpoint bound. Consequently the expected number of target edges among independent uniform choices from the lists is less than one. This uses the total *remaining* edges just once. For ordinary rows, all the auxiliary choices cost at most $h\rho r\le fr$, because they lie in $G$. Both $255/256-2\theta_o-f$ and $255/256-\theta_o-f-2/32$ exceed $1/61$. In the restriction theorem and in the $hr+1$ case only auxiliary rows are needed.

As in base §3, every exterior point must have a large row. Points with a unique large row join it completely, and two such points for the same row are adjacent. Otherwise the preceding extension produces one too many independent vertices. Adjoin these points to their rows; the enlarged rows remain cliques. For $P$ remaining exterior vertices the enlarged deficits add to $P-1$, since the order is exactly one more than the number of rows times $r$. Each remaining point has at least two large rows before enlargement.

## 3. Edge counts at the destination row

Set $q_0=1/10000$. In an enlarged row with deficit $dr$, price a large arrival at $(kd+q_0)r$. Write $a=kd+q_0$ and $\theta=\theta_a$ or $\theta_o$ according to the row. If the row has $n>0$ large arrivals, then $(n+1)/(2r)-d\le a$. To see this let $t=2(d+a)<1$. With at least $\lfloor tr\rfloor$ arrivals, the one-clique capacity (base (4)) on that many actual vertices requires $\theta u<(1-u)d+u^2/2+u/(2r)$, $u=\lfloor tr\rfloor/r$. At $t$ the difference before rounding is
$$
    [2(\theta-a)(1+k)-1]d+2(\theta-a)q_0 .
$$
The bracket is positive and the second term exceeds $(\theta+d+1/2)/r$, even at the maximum allowed deficit. This rules out the stated count and proves the price bound.

For a point with precisely two large rows let $d_1,d_2$ be their deficits **before** enlargement, in units of $r$. Write $D_2$ for an upper bound on $d_1+d_2$. Use the individual caps $\delta$ for an auxiliary and $o=1/256$ for an ordinary, and cap the sum over auxiliary rows by $D'$. If the two degrees together were at most $(1+kD_2+2q_0)r$, the product of the two nonneighbor-list sizes would exceed their entire target cut, bounded by $r+d_1d_2r^2$. Explicitly, if $d,e$ are the individual upper bounds, the two endpoint tests, with either row placed first, are
$$
 (1-d-\theta)(\theta-e-kD_2-2q_0)>
                         \min(de,D_2^2/4)+I .
$$
Each factor is positive. The minimum at fixed total degree is at an endpoint by concavity. A compatible pair would extend with the point. For three or more large rows, any three already contribute more than $r$ net, without prescribing representatives. For $j$ ordinary rows among the three the numerical comparison is
$$
 j\theta_o+(3-j)\theta_a-k\{jo+\min(D',(3-j)\delta)\}-3q_0>1 .
$$
Each further arrival has positive net charge. The checker tests every ordered row type in both applications. The prices used in these tests dominate the prices after enlargement. Summing the one-clique capacities gives $rP\le(r-1)(P-1)$, impossible. When $P=0$ the nonnegative deficits already contradict their sum. This proves (3) and the restriction theorem.

## 4. The edge bound for uniquely assigned senders

Use the marks, retries and circular arcs of [Appendix D](cutoff-218.md), with their original target edges. Its symbols $N_i,n_i,E_i,F_i,Q,T_1,H_E$ denote respectively the number of uniquely strong senders at a row, its expected heavy-load count, its expected exterior cut, the incidences from foreign representatives, and the three quantities in its repair bound $\mathcal R=(4/3)Q+jT_1+H_E$. Here $j=(1+80\rho_0)/(1-g\rho_0)$. Write $\sigma=\sum d_i^2,\ w=\sigma/r,\ l=(\Delta-m)/(\rho r)$, where $m$ is the expected number of marks. Thus $w\le\kappa\rho r$. Retained vertices have degree at most $r/4$ into every other retained clique, as required by the arcs.

In counting $n_i$, allow one sender for each recorded source at destination $i$. There are at most $\omega r$ there and $pr$ in total. The represented points lie in true cliques, so all their inter-clique edges are charged in $y_i'$. Thus $F_i\le(2jg\rho_0)y_i'r^2\le y_i'r^2/512$. The heavy-load bound in the 218 proof becomes
$$
 \frac{n_i}{r}\le x_i+(b_i)_+/r+\omega+\frac{513y_i'}{512\rho},
 \qquad \sum_i n_i\le M_0sr,\qquad
 M_0=\frac{513Y_{\rm hi}}{512f}+\frac7K,
$$
where $Y_{\rm hi}$ is the band's upper endpoint. The first inequality counts all own-part senders separately. For each other sender outside the recorded group its heavy indicator is at most its load divided by $\rho r$. In summing, use $18/5+1/2+p_*<7$. The repair inequality itself still uses the full actual $E_i$.

Here are the constants needed to replay the signed cut. Put $\eta=1/(Rf^2)$, $z=513\gamma/512+1/256+g\rho_0+\omega$, and
$$
 \begin{aligned}
 a&=\min(7/2,(249/250)/z),&
 Y&=(a-4/3-a^2\kappa/2)/2,\\
 k_1&=(4/3)/Y,& b_1&=j(1+1/k_1),\qquad V=aM_0+9b_1/K .
 \end{aligned}
$$
For any upper bound $W$ with $\sum_i N_i d_i/r\le W\rho r$, [Appendix D](cutoff-218.md)'s tested-edge inequality gives $\mathcal R\le P(W,l)\rho^2r^2$, where
$$
 P(W,l)=k_1(b_1W+l)^2\left(\tfrac12+\frac{a^2\kappa}{4Y}\right)
 +k_1\eta\left(\frac{(1+V)^2+V/K}{2}+\frac1{2K}\right).
$$
Indeed $B_\pi+(\Delta-m)\le a\sqrt{\kappa Q}+(b_1W+l)\rho r$ for the test $\pi_i=(a n_i+b_1N_i)/r$. Here $az+2b_1g\rho_0<1$. The same-edge term pays for representative conflicts exactly as in (5)–(6) of that supplement. This estimate itself uses no assumption that the subsequent one-row bound is less than one.

The first pass uses $W=2\kappa$, since $N_i\le2d_i$. Set $Z_1=8P(2\kappa,0)+2\eta$. Let $A_0$ denote expected eligibility and $L_0=\sum d_i+\Delta+1-A_0$ expected failures before thinning. When $A_0>\Delta$, the base oversampling bound gives $\sum d_i-L_0\le Z_1\rho^2r$, since $l=0$ and $Z_1\rho_0^2<\min(c/128,1/16)$. When $A_0\le\Delta$, $L_0\ge\sum d_i+1$.

For a unique sender let $q_y$ be its neighbor fraction in the assigned row. At zero moderate assignments, [Appendix E](cutoff-289.md)'s row calculation keeps an extra $37\rho r\sum_y(1-q_y)$ on the left of its capacity bound. With $\lambda=501/1000$, that left side, including $rL_0$, is at most $r\sum d_i+\lambda\sigma$. Also $\sum_{y\ {\rm unique\ at}\ i}q_y\le d_i/(1-g\rho_0)$ and $d_i\le g\rho r$. Consequently
$$
 \frac1r\sum_i N_i d_i
 \le \frac{w}{1-g\rho_0}+
            \frac{g}{37}\{\lambda w+\sum d_i-L_0\}
 \le W_1\rho r,
 \qquad
 W_1=\left(\frac1{1-g\rho_0}+\frac{\lambda g}{37}\right)\kappa
                +\frac{gZ_1\rho_0}{37}.
$$
This uses the actual missing target edges that make retries succeed. A large number of successful retries would contradict the first oversampling bound.

Repeat the signed cut with $W_1$. Put $Z_2=8P(W_1,0)+2\eta$ and $\epsilon(l)=P(W_1,l)+gl+l^2/2+\eta(1/2+1/(2K))$. Discarding the extra retry charge in the last capacity inequality gives $0\le l\le\lambda\kappa$. By the one-row and oversampling comparisons of [Appendix D](cutoff-218.md) the required inequality is
$$
 (1-\epsilon(l))(c-\lambda\kappa\rho_0)+l-\lambda\kappa
                 -Z_2\rho_0-\frac1{fRK^2}\le0 .
$$
The checker verifies positive $Y$, both oversampling caps, the list and degree bounds, and $\epsilon<1$. The displayed left side is concave in $l$, so its minimum occurs at an endpoint. All $6\cdot96\cdot2=1152$ exact endpoint values exceed $1/2000$. This contradiction proves Theorem 1. [Rational certificates and small-graph enumeration](verify_cutoff_190.py)

## 5. Three tests on the specified profile

**Keeping the 218 rows.** At most 1988 original slots were omitted before width selection there. Set $H=m+1988$. For $r\ge2^{53}$ keep aside exactly $r-H$ full cliques from the zero tail. Each has no target edge to another such clique. The remaining set $U$ has $Hr+1$ points. Each exterior vertex has at most one target neighbor in any full clique, since the $r-1$ other colors must occur on its $r$ edges to that clique. An independent $H+1<r$ points in $U$ could therefore extend through every set-aside clique. Hence $\alpha_J(U)\le H$. Since $H^2/2^{53}<100/3199$, the restriction theorem of §2 rules this out. Any placement of the positive cuts within the first $m$ rows is covered.

**Keeping a sparsest color and choosing the rows again.** For this part and the next, $y_i$ counts *all* target edges from $C_i$ outside its original part, in units of $r^2$. Impose the per-destination degree bound at the **end**. Whenever a surviving vertex sends more than $r/4$ edges into another retained clique, record that destination and delete the source. If the final deficit there is $x_i r$, this source still has at least $(1/4-x_i)r$ edges to the final clique. Distinct sources give distinct edges into their recorded destinations; a deleted source belongs to none of the final cliques. Thus the normalized number $p$ of these deletions satisfies
$$
                p\le\sum_i\frac{y_i}{1/4-x_i}<16/25                    \tag{4}
$$
under the profile's upper bounds, for $r\ge m$. In fact $(1/4-x_i)^{-1}\le4+21x_i$ when $x_i\le1/20+1/m$. Put $H_0=(45/2)\log 2$. Integral comparison gives $\sum_{j=4}^{m+3}1/j\le\log((m+3)/3)<H_0$ and $\sum_{j=4}^\infty j^{-2}\le1/3$. Including both upward roundings yields
$$
 \sum y_i\le H_0/100+1/m,\qquad
 \sum x_i y_i\le1/1500+H_0/(100m)+H_0/(5m^2)+1/m^2 .
$$
These give (4). This is where the positive target edges and the deficits at their specific destinations interact.

Start from the same stability partition of the sparsest color. Prune only total interpart degrees above $\tau r$, now $\tau=499/1000$, say $tr$ vertices. Trim and take maximal independent pairs and short lists as in §1 with $L=999/1000$. Set aside chosen, short and unqualified parts. Also set aside any preliminary clique meeting more than $r^2/16$ edges to other preliminary cliques. There are at most 32 of these since all interpart edges together number at most $r^2$. At most $r/4$ vertices can subsequently be removed from any remaining source clique, as each such source spends more than $r/4$ of its own distinct incident edges. The final cliques all have more than $0.74r$ vertices. Before the final single-destination deletions the total normalized deficit is at most $1/2+t+2\tau(1-\tau t)/L^2$. The bounds on chosen and short slots from §1, with $p=0$, give fewer than 4600 exceptions including the additional 32. Keep every retained slot through the final deletions. All surviving vertices then have degree at most $r/4$ into each other retained clique. The two pruning stages spent disjoint edges, so $\tau t+p/4\le1$. Since $1-2\tau^2/L^2>0$, substitution and (4) give
$$
 \sum_i x_i\le\tfrac12+\frac1\tau+
                  \left(1-\frac1{4\tau}+\frac{\tau}{2L^2}\right)p<2.984. \tag{5}
$$

For $r\ge2^{27}$ the lower rounded deficits exceed (5). Here are the details near the endpoint. Put $a=r/5,\ U=m+4$, and count the first 252 floors using $\lfloor a/j\rfloor\ge a/j-1$ for $4\le j\le255$. On the tail use $\int_{256}^{U}\lfloor a/u\rfloor\,du$. The integral of the discarded fractional parts is at most $2U/3$. Indeed, after substituting $v=a/u$, the weight $a/v^2$ decreases. On each full integer interval, or on the final interval starting at an integer, the weighted mean of the fractional part is at most $1/2$, by pairing opposite points of that interval. For the initial incomplete interval bound it by one. Its length in the original coordinate is at most $U/3$, since with $b=a/U>4/3$, $1-b/\lceil b\rceil\le1/3$. Consequently the normalized total is at least
$$
 \tfrac15\left(\sum_{j=4}^{255}1/j+16\log 2\right)
                   -\frac{252+2U/3}{2^{27}}>2.984 .
$$
The stated lower bound assumes the indicated entries exist. If zero padding is needed, a positive lower-rounded entry in a padded slot already rules out the profile.

**Allowing a choice of color at every feasible order.** Start with a family of $r$ private cliques as specified below. Assign the initial exterior vertices to the original parts so their sizes are $r,\ldots,r,r+1$. There is one more exterior vertex than the sum of the initial deficits. Write $D_0$ for this unnormalized sum and $\eta_a=e_a(V)-r\binom r2-r$ for the target hue's excess. We will have $D_0/r\le5/2$ and $D_0/r+\eta_a/r^2\le3$. By subtracting the interiors of the cliques, all target edges outside those interiors number at most $3r^2+r$. Omit initially any clique of size less than $3r/4$ or meeting more than $r^2/16$ target edges to the other cliques. This costs fewer than 110 slots. Apply the final deletion rule above, keeping all remaining slots. Each loses at most $r/4$ points, so the retained cliques all have size at least $r/2$ and satisfy the per-destination degree bound. Removed sources retain their original part labels. Equation (4) applies to the resulting rows whenever the profile holds.

If a full monochromatic clique exists, use it as an independent reference row for each other hue. For each vertex outside, every other hue occurs into the reference, and at most one hue occurs twice. For a fixed other hue $a$, its private cliques consist of each reference vertex and the outside vertices seeing it alone in color $a$. Two private vertices at the same root must be joined in $a$, by adjoining the other $r-1$ roots. Its initial deficit sum $D_0(a)$ is the number of vertices doubled in $a$ minus one. Across the $r-1$ hues there are at most $r^2-r+1$ double occurrences. The total excess over the Turán floors across all colors is $r\binom r2$, and each excess is nonnegative. Averaging the sum $D_0(a)/r+\eta_a/r^2$ gives a hue for which it is at most $3/2$. Thus the final normalized deficit would be at most $3/2+16/25$. But the first $m/8$ lower-rounded terms alone contribute more than $(19/5)\log 2-1/8$, by integrating $1/u$ from $4$ to $m/8+4$.

If no hue has a full clique, the private-neighborhood lemma for a sparsest hue gives $r$ disjoint initial cliques with total deficit at most $(5r-7)/2$, and sparsity gives $\eta_a\le\binom r2$. Every final deficit is at least one. The first $m/8$ floors above, together with one vertex of deficit in every remaining slot, give normalized total greater than $1-110/m+(19/5)\log 2-1/4>5/2+16/25$, contradicting (4). The private-neighborhood lemma is reproduced in the PDF appendix. This completes Theorem 2. [Private-neighborhood lemma, §3](rooted-rows.md)

The fixed-row interval below $2^{53}$ still permits a positive part of the profile supported on more rows than the restriction theorem can handle. A necessary condition for leaving $H$ rows after peeling a mutually target-disconnected family of full rows is $H^2/r>100/3199$, provided $H+1<r$ and $r\ge2^{20}$. A further fixed-row improvement must also use information inside the positive part or improve this restriction. [Current research handoff](../README.md)
