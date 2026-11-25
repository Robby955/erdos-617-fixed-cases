# Fixed rows, excess loads, and a cutoff of $2^{165}$

Robert Sneiderman’s research notes · 22 November 2026

**Theorem 1.** For every integer $r\ge2^{165}$, every coloring of the edges of $K_{r^2+1}$ with $r$ colors has $r+1$ vertices missing a color.

**Theorem 2.** Fix the original rows of §1 of the 218 supplement, before its width selection, in any hypothetical counterexample. Put $m=2^{24}$. Suppose the ordinary rows can be indexed so that their deficits are between the floor and ceiling of $r/[5(i+3)]$ and their foreign target-edge counts are at most $\lceil r^2/[100(i+3)]\rceil$, for $1\le i\le m$. Both quantities vanish later. Zero entries may pad the sequence. This profile is impossible for every $r\ge43{,}000{,}000$, for every allowed choice of the original pruning order and maximal pair family.

For $m\le r<43{,}000{,}000$, a surviving profile would have one to four chosen pairs. Their target neighborhoods must remove more than $9r/50$ distinct vertices from at least six retained original parts during the pair step. For $33{,}000{,}000\le r<43{,}000{,}000$ a single pair must meet at least fourteen ordinary parts. Existence in the remaining interval is open. The all-order conjecture and the project's case $r=19$ remain open. The proof of Theorem 1 is human-readable and awaits independent review. [Previous supplement](cutoff-190.md) · [Fixed extraction](cutoff-218.md) · [Exact checker](verify_cutoff_165.py) · [Local Lean lemmas](FixedRowCharges.lean) · [Original conjecture](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf)

## 1. Where the stars in the original extraction can end

Assume a counterexample. Fix its sparsest color $J$. Every color has independence number at most $r$. In the stability partition $R_i$, put $b_i=|R_i|-r$, and let $\mu_i$ be the number of internal pairs missing $J$. Write $X$ for the number of interpart edges of $J$, and $\eta$ for its excess over the complementary Turán floor $p_r(r^2+1)$. The base manuscript gives $\mu=\sum\mu_i\le\eta\le\binom r2$, $\sum b_i=1$, $\sum(b_i)_+\le r/2$, and $X=\eta+\mu-(\sum b_i^2-1)/2$. A destination qualifies when $b_i\le r/256$ and $U_i=\mu_i-(r-1)b_i\le r^2/1200$. At most 728 parts fail. At most $\omega r$ exterior vertices originally have more than $r/4$ target neighbors in any given qualifying part, where $\omega=5/1464$. These are the estimates of §1 of the 218 supplement.

Keep that extraction unchanged. A first-stage removal has more than $r/4$ current edges to a qualifying foreign part. A second-stage removal has current total interpart degree above $\tau r$, with $\tau=47/100$. Put $pr,tr$ for the numbers removed and $Z=1-p/4-\tau t$. Trim parts to $r$, select the original maximal family of $q$ jointly target-independent pairs in distinct parts, and delete their neighbors in unchosen parts. Ordinary cliques $C_i$ come from qualifying unchosen lists of size at least $Lr$, $L=19/20$. Write $x_i=1-|C_i|/r$, $y_i=e_J(C_i,V\setminus R_i)/r^2$ and $D=\sum x_i$.

Record one destination of each first-stage removal. A source recorded at an ordinary destination $i$ has more than $(1/4-x_i-b_i/r)r$ edges into its **final** clique, since initially $|R_i\setminus C_i|=x_i r+b_i$. These are foreign edges counted by $y_i$. Distinct sources at the destination give different edges. For all $r\ge m$ the number of sources recorded at ordinary destinations, divided by $r$, is thus at most
$$
 P=\sum_i\min\!\left(\omega,\frac{y_i}{1/4-1/256-x_i}\right)<609/1000.
$$
For $j=i+3=4,\ldots,255$ the checker sums the rational bounds using $x_i\le1/(5j)+1/m$, $y_i\le1/(100j)+1/m^2$. For $j\ge256$ use the common denominator $1/4-1/256-1/1280-1/m$. The sum of the numerators is at most $\log((m+3)/255)/100+1/m$. No positive lower bound on a foreign edge count is needed.

Let $F$ be the number of short unchosen lists and $W=\sum_{\rm short}(1-|C_i^{\rm list}|/(Lr))$, using all unchosen lists at this point. A qualifying recorded destination omitted from the ordinary rows is chosen or short. Therefore
$$
 p\le P+\omega(q+F),\qquad q\le W+Z/L^2,\qquad W\le F.
$$
The middle inequality is the second representative draw in §1 of the 218 supplement. The deficit of each short list in units of $r$ is exactly $1-L+L(1-|C_i^{\rm list}|/(Lr))$. Subtracting these deficits from $1/2+p+t+2\tau q$ pays for their omission. With $c=1-1/(4\tau)$, $C_0=1/2+1/\tau+c(609/1000)$, and $e=1/\tau-2\tau/L^2$, this gives
$$
 D\le C_0+c\omega q-(1-L-c\omega)F-(L-2\tau)W-eZ
 \le C_0-(1-2\tau-2c\omega)q.                                      \tag{1}
$$
For the last step, $1-L-c\omega>0$, $L>2\tau$, and $e>(1-2\tau-c\omega)/L^2$. The certificate in §2 gives $D>8/3$ throughout the feasible range. Equation (1) implies $q\le4$, then $F\le5$ by its first inequality, and consequently $p<16/25$.

## 2. The pair neighborhoods must remove vertices from ordinary parts

Let $S$ consist of the first- and second-stage sources in the original parts that eventually yield ordinary rows. Write $a_i r=|S\cap R_i|$ there and $p_Rr,t_Rr$ for the two removal counts in $S$. Let $B_Rr=\sum_{\rm ordinary}(b_i-a_i r)_+$ count subsequent trims there and $O_Er=\sum_{\rm omitted}(b_i)_+$. Write $U$ for the number of vertices removed from ordinary parts by the pair neighborhoods alone, in units of $r$.

The actual target edges lost when deleting $S$ include at least $(p_R/4+\tau t_R)r^2$ fresh interpart edges spent by its sources. They also include the same-part edges from $S\cap R_i$ to $C_i$. The number of missing pairs on those cuts is at most
$$
 \sum_{\rm ordinary}\mu_i-(r-1)B_Rr.
$$
Indeed, the raw parts remaining after the first two stages still contain at least $(r-1)(b_i-a_i r)_+$ nontarget pairs. Each of the other colors needs at least $(b_i-a_i r)_+$ internal edges by its independence cap. These pairs avoid $S$. In the omitted raw parts the same argument before pruning reserves at least $(r-1)O_E r$ missing pairs.

On the other hand, deleting $S$ loses at most $r|S|+\eta$ target edges. The surviving graph has independence at most $r$, and each decrement of $p_r(n)$ for $n\le r^2+1$ is at most $r$. Comparing both estimates and using $\eta+\mu\le r^2$ yields
$$
 p_R/4+\tau t_R\le 1-(1-1/r)(B_R+O_E)+\sum a_i x_i.
$$
The exact count of vacancies in ordinary parts gives $D=p_R+t_R+B_R-\sum_{\rm ordinary}b_i/r+U$. Here $-\sum_{\rm ordinary}b_i/r\le O_E$. Since $1-(1-1/r)/\tau<0$, elimination of $t_R$ gives
$$
 D\le 1/\tau+c p_R+\frac{1}{\tau}\sum a_i x_i+U.                     \tag{2}
$$
Each $a_i\le x_i+(b_i)_+/r\le x_i+1/256$. The ceilings give $\sum x_i^2<14/1000$, by $\sum_{j=4}^\infty j^{-2}\le1/3$ and $\sum_{j=4}^{m+3}1/j<16$. Use $p_R\le p<16/25$, $D\le C_0$ inside the error term, and $D>8/3$ on the left of (2). We get $U>9/50$. Even the five largest allowed deficits sum to less than $9/50$. Thus at least six ordinary parts lose neighbors and $q\ge1$. Every chosen endpoint misses every final ordinary clique in color $J$.

For clarity, the arithmetic uses the reduction in the next table. Put $T(r)=\sum_{j=4}^{m+3}\lfloor r/(5j)\rfloor$, so that $D\ge T(r)/r$.

| Range of $r$, left endpoint included | Certified lower bound on $T(r)/r$ | Possible $q$ from (1) and (2) |
| --- | ---: | --- |
| $2^{24}$ to $19{,}000{,}000$ | $8/3$ | 1 through 4 |
| $19{,}000{,}000$ to $25{,}000{,}000$ | 2.690 | 1 through 3 |
| $25{,}000{,}000$ to $33{,}000{,}000$ | 2.745 | 1 or 2 |
| $33{,}000{,}000$ to $40{,}000{,}000$ | 2.800 | 1 |
| $40{,}000{,}000$ to $43{,}000{,}000$ | 2.840 | 1 |
| $43{,}000{,}000$ and above | 2.856 | none |

In the two upper surviving bands, substituting 2.800 and 2.840 on the left of (2) requires the single pair's neighbors to meet at least fourteen and eighteen ordinary parts respectively, by summing the largest allowed deficits. Above forty million, including the endpoint, (1) also gives exactly one short list. Two short lists would give $D<2.840$; zero would require $Z\ge L^2$, also impossible there. With $q=F=1$, (1) gives $Z/L<13/500$. The unique short list has length $(1-W)Lr\le Zr/L<13r/500$. The other ordinary parts keep their original clique memberships throughout this argument.

For each integer interval $[a,b]$ in the certificate, $T(r)/r\ge T(a)/b$. The checker calculates $T(a)$ by grouping identical integer quotients. The blocks cover every integer through $8m-1$. For $r\ge8m$, $T(r)/r\ge(\sum_{j=4}^{255}1/j+16\log2)/5-1/8>2.856$. This proves Theorem 2 without a monotonicity assumption on the normalized sum. [Floor certificate and fixed-row inequalities](verify_cutoff_165.py)

## 3. Choose pairs before trimming for the general theorem

We may now choose rows for an arbitrary counterexample. Use the same first-stage pruning of the sparsest color. Write $pr$ for the count and keep the recorded stars of §1 of the 190 supplement. Prune next at total interpart degree $\tau r$, now $\tau=43/100$, with $tr$ removals. Write $Z=1-p/4-\tau t$, $V_2=\sum(b_i/r)^2$ and $Y_*=2-p/2-\tau t$. The actual remaining interpart count in units of $r^2$ is at most $z=Z-V_2/2$ by the stability identity. Choose a maximal family of $q$ jointly independent pairs in distinct surviving parts **before trimming any part**. Remove their neighbors from the unchosen parts. Each resulting list is a clique by maximality and already has size at most $r$.

Put $L=124/125$ and $O_Q=\sum_{\rm chosen}(b_i)_+/r$. The total deficit across unchosen lists in units of $r$ is at most $p+t+O_Q+2\tau q$. Indeed deleting a whole chosen *surviving* part costs at most $r+(b_i)_+$, the original order is $r^2+1$, and the pair endpoints have remaining interpart degree at most $\tau r$. Use the two padded draws from the 218 supplement. The first gives $q\le(1/2+p+t+Z)/(1-2\tau)$. In the second, $q\le W+z/L^2$, with $W$ defined as in §1. Omit chosen, short and unqualified parts. For ordinary deficits $D=\sum x_i$ and discounted foreign counts $Y=\sum y_i'$ of the 190 supplement we obtain
$$
 D\le p+t+O_Q-(1-2\tau)q+z/L^2,\qquad Y\le Y_*-V_2.              \tag{3}
$$
Indeed each short list pays at least its contribution to $W$. Each first-stage recorded edge is absent from the discounted incidence count at both ends and each edge spent by a second-stage removal is absent at at least one end. The original interpart incidence budget is at most $(2-V_2)r^2$. The per-destination degree bound $r/4$ still holds for surviving points in other retained cliques.

For width parameters $\alpha,\beta$ from §5 put $g_0=1/(2L^2)+\beta/\alpha$. Cauchy gives $O_Q^2\le qV_2$, including $q=0$. Since $4(1-2\tau)g_0\ge1$, the arithmetic-geometric mean inequality gives $O_Q\le(1-2\tau)q+g_0 V_2$. Hence
$$
 \frac Y\alpha+\frac D\beta
 \le\frac{Y_*}{\alpha}+\frac{p+t+Z/L^2}{\beta}.                      \tag{4}
$$
For a separate unweighted bound, each short list pays its $2\tau$ multiple in the second draw with at least $\min(1-L,1-2\tau)$ left. Thus $D\le D_*=1/2+p+t+2\tau Z/L^2<3.7$, and the number of short lists is at most $D_*/\min(1-L,1-2\tau)$. With the chosen and unqualified parts this gives $e_0+1<K/2$ for the total omission count $e_0$ and $K=2560$. The four corners of the trapezoid $0\le p\le125/61,\ t\ge0,\ Z\ge0$ suffice for both checks.

## 4. Use the rows omitted at the minimum width

Give each ordinary row weight $a_i=\max(y_i',\alpha x_i/(2\beta))$. Set aside the $K-e_0-1$ heaviest ordinary rows. For the rest put $s(z)=K+\#\{i:a_i>z\}$ and $C(z)=\sum_{a_i\le z}x_i^2/z$. If $s(z)z/\alpha+\alpha C(z)/(4\beta^2)<1$, the width proof of the 218 supplement gives $h=s(z)-1$ omitted slots and $v=s(z)z/\alpha$, with
$$
 s\max y_i'\le\alpha v,\qquad s\max x_i\le2\beta v,\qquad
 s\sum x_i^2\le4\beta^2v(1-v).                                      \tag{5}
$$
Here $s=s(z)$. For $R=2^b$ set $S=2^{(165-b)/4}>2K$ and integrate the left side of the test against $dz/z$ from $\alpha/S$ to $\alpha/K$. The constant $K$ costs less than one. Each row's full cost, integrating its two terms on the positive line, is $a_i/\alpha+\alpha x_i^2/(4\beta^2a_i)\le y_i'/\alpha+x_i/\beta$. A zero-weight row costs zero.

There is a saving of at least $1/4$ unless (5) already holds at $z_0=\alpha/(2K)$. If any remaining weight exceeds $z_0$, each of the rows set aside costs at least $1/(2K)$ in the full bound. There are at least $K/2$ such rows. Otherwise $s(z_0)=K$; failure of the test there implies $K\sum x_i^2\ge\beta^2$ on the remaining rows. The omitted part of their square integral above $\alpha/K$ then costs at least $K\sum x_i^2/(4\beta^2)\ge1/4$. Thus a sufficient condition for (5) at some $K\le s<S$ is
$$
 \frac34 + \frac{Y_*}{\alpha}+\frac{p+t+Z/L^2}{\beta}<\log(S/K).
$$
It follows that $r\ge Rs^4$ throughout the claimed range.

## 5. Charge only the excess of a heavy load

Use the actual target edges, exterior set $G$, unique-sender trials and marked vertices of the 190 supplement. Set $f=7/30,\ \rho=f/s,\ \rho_0=f/K$ and $c=1/8$. Its auxiliary argument gives $\Delta=hr-|G|>cr$ under (5) and the list checks below. The new extraction has the same per-destination degree and recorded-star bounds needed there. The untrimmed deficit bound gives $\sum x_i+1/2+p<7$ and $2\sum x_i<9$, as needed in its estimates of sender counts.

In an unrepresented row the original load $t_{xi}$ of a marked vertex $x$ is its own target degree into that row plus the degree of its representative there, if present. It is zero in its represented row or when unmarked, and at most $3r/4$. Place an arc of length $(t_{xi}-\rho r)_+$, for positive lengths only, on a circle of circumference $3r/4$, with independent uniform starts. In an independent set of $h+1$ exterior points of the repaired graph, the excess arcs in an unrepresented row are disjoint and have total length at most $3r/4$. The baseline loads of all these points cost at most $(h+1)\rho r=fr$, including the points of $G$. Exactly the same ordinary lists can therefore be filled as in the 190 proof. Real half-open arcs allow nonintegral lengths.

Write $E_i$ for the expected true cut from the sampled exterior set to row $i$, $F_i$ for expected loads from representatives in other rows, $n_i$ for the expected number of heavy loads and $N_i$ for the number of unique strong senders. With the notation of §4 of the 218 supplement set
$$
 Q=\sum n_i(E_i+F_i)/r,\quad H=\rho\sum n_i^2,\quad
 T=\sum N_iE_i/r,\quad H_E=j^2\sum_{i<k}N_iN_k e_J(C_i,C_k)/r^2.
$$
Two arcs intersect with probability at most the sum of their lengths divided by the circumference. In the ordered-pair sum, each sender's heavy indicator is independent of each distinct sender's excess. The total expected excess at row $i$ is at most $E_i+F_i-\rho r n_i$. Extending the sum of the nonnegative products to all indices therefore bounds the arc conflicts by $4(Q-H)/3$. The representative conflicts from the 218 proof are unchanged. The repair bound is now
$$
 \mathcal R=\tfrac43(Q-H)+jT+H_E.
$$
This bound scales by at most four when the thinning probability increases from $p_0$ to $p_1\le2p_0$. Indeed $n_i$ is linear in the probability. The other factor $E_i+F_i-\rho r n_i$ is a nonnegative constant from $G$ plus the probability times a nonnegative coefficient, since each marked trial's counted incidences dominate $\rho r$ times its heavy indicator. Thus $Q-H$ scales by at most four, $T$ by two and $H_E$ stays fixed.

For bounds $A,X_0,B$ on the three left sides of (5), put $\gamma=A/f,\ g=X_0/f,\ \kappa=B/f$, $j=(1+80\rho_0)/(1-g\rho_0)$, and $\eta_0=1/(Rf^2)$. The 190 supplement gives
$$
 n_i/r\le z_*=513\gamma/512+1/256+g\rho_0+\omega,\qquad
 \sum n_i\le M_0 sr,\quad M_0=513Y_{\rm hi}/(512 f)+7/K .
$$
Use a band containing $Y_*$ and write $Y_{\rm hi}$ for its upper end. In the tested-row inequality use
$$
 a=\min(5/2,(249/250)/z_*),\quad k=(4/3)/(a-4/3),\quad
 b_1=j(1+1/k),\quad V=aM_0+9b_1/K.
$$
All tested probabilities $(a n_i+b_1N_i)/r$ are at most one. Suppose $\sum N_i d_i/r\le W\rho r$, where $d_i=x_i r$, and put $l=(\Delta-m_0)/(\rho r)$ for expected mark count $m_0$. By Cauchy, $\sum n_i d_i/r\le\sqrt{\kappa H}$. The tested cut pays $aQ+b_1T+(b_1/j)^2H_E$ in actual edges as in (5)–(6) of the 218 supplement. After deducting repairs, it leaves $(a-4/3)(Q-H)+aH$, together with $(b_1-j)T+((b_1/j)^2-1)H_E$, on the left. On the right the squared term is at most $(a\sqrt{\kappa H}+(b_1 W+l)\rho r)^2/2$. For $a\kappa<2$, completing the square gives
$$
 \tfrac12(a\sqrt\kappa\,x+z)^2-a x^2\le z^2/(2-a\kappa).
$$
Multiplication by $k$ now pays the three repair terms. The remaining height and mean terms from the tested cut give $\mathcal R\le P(W,l)\rho^2r^2$, where
$$
 P(W,l)=\frac{k(b_1W+l)^2}{2-a\kappa}
       +k\eta_0\left(\frac{(1+V)^2+V/K}{2}+\frac1{2K}\right).
$$
All other steps in the two applications of the signed cut in §4 of the 190 supplement use only this repair bound, its oversampling version and the unchanged one-row capacities.

The table uses $K=2560$ throughout; $b$ is the exponent of $R$.

| Band for $Y_*$ | $b$ | $4000\alpha$ | $4000\beta$ |
| --- | ---: | ---: | ---: |
| 0 to 5/8 | 14 | 676 | 880 |
| 5/8 to 3/4 | 15 | 680 | 884 |
| 3/4 to 7/8 | 15 | 680 | 880 |
| 7/8 to 1 | 15 | 676 | 878 |
| 1 to 9/8 | 16 | 680 | 885 |
| 9/8 to 5/4 | 16 | 680 | 880 |
| 5/4 to 11/8 | 16 | 680 | 880 |
| 11/8 to 13/8 | 16 | 676 | 872 |
| 13/8 to 2 | 17 | 680 | 880 |

The width cost is affine on each clipped trapezoid, so its vertices suffice. In each band divide $v\in[0,1]$ into 96 equal intervals, bounding the three quantities in (5) separately by their maxima on each interval. For completeness write $\lambda=501/1000$, $Z_1=8P(2\kappa,0)+2\eta_0$, and use the 190 supplement's retry estimate
$$
 W_1=\left((1-g\rho_0)^{-1}+\lambda g/37\right)\kappa
       +g Z_1\rho_0/37 .
$$
Put $Z_2=8P(W_1,0)+2\eta_0$, and $\epsilon(l)=P(W_1,l)+gl+l^2/2+\eta_0(1/2+1/(2K))$. At each endpoint of $0\le l\le\lambda\kappa$, the checker gives
$$
 (1-\epsilon(l))(c-\lambda\kappa\rho_0)+l-\lambda\kappa
                     -Z_2\rho_0-1/(fRK^2)>1/2000 .
$$
This expression is concave in $l$. The one-row and oversampling inequality requires it to be nonpositive. All 1,728 endpoints pass, as do the ordinary and auxiliary list conditions, the two oversampling caps, and the height bounds. Together with the earlier sampling bounds, this proves Theorem 1. The [Lean proof guide](formal-cutoff.md) gives the formal argument for the sharper cutoff. [Arithmetic and arc checks](verify_cutoff_165.py) · [Combined manuscript](../paper.pdf)
