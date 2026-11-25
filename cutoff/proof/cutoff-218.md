# Mixed harmonic rows and a cutoff of $2^{218}$

Robert Sneiderman research project · Private proof supplement · 22 November 2026

**Theorem 1.** For every integer $r\ge2^{218}$, every $r$-edge-coloring of $K_{r^2+1}$ has $r+1$ vertices whose induced edges omit a color.

**Theorem 2.** For $r\ge2^{36}$, in a hypothetical counterexample one can choose ordinary cliques with total deficit less than $18r/5$, omitting fewer than 2,000 original parts. Every retained vertex has at most $r/4$ target neighbors in each other retained clique. The proposed $4/(25i)$ deficits over $2^{36}$ rows exceed this total even when rounded down to whole vertices.

**Theorem 3.** For $r\ge2^{50}$, the earlier total-degree extraction itself cannot have the proposed joint profile on all the retained rows of a counterexample. More generally it cannot have deficits and foreign edge counts bounded above by the upward-rounded profiles $4r/(25i)$ and $r^2/(100i)$, with both zero after the $2^{36}$-th row.

The second theorem permits a change of rows. The third keeps the earlier extraction. A given earlier extraction with rounded mixed data at $2^{36}\le r<2^{50}$ remains unresolved. The three underlying manuscripts follow this supplement in the PDF. Their combined proof awaits independent mathematical review. [Previous supplement](cutoff-289.md) · [320 supplement](cutoff-320.md) · [Base manuscript](balanced-coloring.md) · [Exact checker](verify_cutoff_218.py) · [Local Lean lemmas](MixedRowCut.lean)

## 1. Choosing rows with less total deficit

Assume a counterexample and choose a sparsest color $J$. Each color has independence number at most $r$. Use the stability partition $R_1,\ldots,R_r$ of base §1. Throughout, edges and neighborhoods without a color specified refer to $J$. Let $b_i=|R_i|-r$, let $\mu_i$ count internal pairs missing $J$, and let $X$ count edges between parts. The base gives $\sum b_i=1,\ \sum (b_i)_+\le r/2,\ \sum\mu_i\le\binom r2,\ X\le r(r-1)$.

Put $U_i=\mu_i-(r-1)b_i$. Each of the other $r-1$ colors needs at least $b_i$ edges inside $R_i$, since deleting one endpoint per edge leaves an independent set. Thus $U_i\ge0$ and $\sum U_i\le r^2/2$. For any $z$ exterior points $Z_i$, the same count in $R_i\cup Z_i$ gives
$$
 e_J(Z_i,R_i)\le U_i+(1+b_i)z+\binom z2.                              \tag{1}
$$
Indeed all edges of the other colors must fit among the $\mu_i$ internal pairs, the nontarget cross pairs and the pairs of $Z_i$.

A part qualifies as a destination if $b_i\le r/256$ and $U_i\le r^2/1200$. At most $128+600$ parts fail. In a qualifying part, $z\le\lfloor r/256\rfloor$ exterior points each sending more than $r/4$ edges into it would cost $U_i> (61/250)zr$, by (1). At $z=\lfloor r/256\rfloor$ this exceeds the qualifying budget for $r\ge2^{20}$. Hence the total number of such exterior points is at most $U_i/((61/250)r)$.

First delete a vertex while it has current degree above $r/4$ into a single qualifying foreign part. Then delete a vertex while its total current interpart degree exceeds $\tau r$, where $\tau=47/100$. This changes the thresholds of the earlier two-stage pruning argument. Let $pr,tr$ be the two removal counts. Each removal destroys fresh edges, and every first-stage removal spent an original star counted by (1). [Earlier pruning argument](rooted-rows.md#1-selecting-and-restoring-cliques-on-the-full-vertex-set)

Consequently
$$
 0\le p\le125/61,\quad t\ge0,\quad p/4+\tau t\le1,\qquad Z=1-p/4-\tau t .
$$
There are at most $Zr^2$ cross edges left. Trim oversized parts to $r$. The total deficit before selecting pairs is $D_0\le(1/2+p+t)r$, by the bound on $\sum(b_i)_+$.

Take a maximal family of $q$ pairs in distinct parts, with all $2q$ endpoints jointly independent. In every unchosen part remove the neighbors of these endpoints. At most $2\tau qr$ vertices are lost. Each unchosen survivor list is a clique by maximality. Write $m_i$ for its size. In both experiments the draws in distinct lists are independent. First select one point uniformly from $r$ positions in each unchosen list, putting empty positions after its $m_i$ points. Keep the real selections and delete one endpoint per conflicting edge. The expected number of conflicts is at most $Z$. The selected survivors and the $2q$ fixed endpoints are independent, so
$$
 q\le\sum_{\rm unchosen}(1-m_i/r)+Z\le D_0/r+2\tau q+Z .
$$
This holds for every maximal family, including one chosen without optimizing its size.

Set $\ell_0=19/20$ and omit the unchosen lists of size below $\ell_0r$. In a second experiment select a uniform point from each long list. In a short list select with probability $m_i/(\ell_0 r)$, uniformly when nonempty. Every individual point now has selection probability at most $1/(\ell_0r)$. The same conflict deletion proves
$$
 q\le\sum_{\rm short}(1-m_i/(\ell_0r))+Z/\ell_0^2 .
$$
Each omitted short list accounts for a deficit $r-m_i\ge 2\tau r(1-m_i/(\ell_0r))$. Subtract these deficits from $D_0+2\tau qr$. Omit the chosen parts and every unqualified destination as well. For the remaining cliques $C_i$, write $d_i=r-|C_i|,\ x_i=d_i/r,\ y_i=e_J(C_i,V\setminus R_i)/r^2$. We have
$$
 \sum x_i\le L_x=\tfrac12+p+t+2\tau Z/\ell_0^2,\qquad
 \sum y_i\le L_y=2-p/4-\tau t .                                        \tag{2}
$$
The second bound subtracts the spent incidences at deleted endpoints from the original $2X$. First-stage pruning bounds the degree of each survivor into each other retained clique by $r/4$. This per-destination bound suffices for the circular arcs of base §4: a sender has at most one representative, and its load is tested in one destination at a time.

The domain of $p,t$ is a trapezoid. Writing $p_*=125/61$, its corners are $(0,0),(p_*,0),(0,1/\tau),(p_*,(1-p_*/4)/\tau)$. At all four, $L_x<18/5$, $(1/2+p+t+Z)/(1-2\tau)<60$, and $(1/2+p+t+2\tau\cdot60)/(1-\ell_0)<1200$. These affine bounds hold throughout, giving fewer than 60 chosen slots and 1,200 short ones. Thus the initial number $e$ omitted is at most $1988$.

For $r\ge2^{36}$, even the first $n=2^{33}$ entries of the proposed profile have total normalized deficit at least
$$
 \sum_{i=1}^n \frac{\lfloor4r/(25i)\rfloor}{r}
 \ \ge\ \frac4{25}H_n-\frac18
 \ >\ \frac4{25}(33\log 2+49/100)-\frac18
 \ >\ \frac{18}{5}.
$$
Here $H_n\ge\log(n+1)+(1-1/(n+1))/2$, by the trapezoid bound for the integral of $1/x$. This proves Theorem 2.

## 2. Choosing the width

Put $K=2500,\ R=2^{19},\ f=7/30,\ \alpha=1/6,\ \beta=11/60,\ S=2^{199/4}$. As in the 320 supplement, give a row weight $a_i=\max(y_i,\alpha x_i/(2\beta))$. Set
$$
 s(z)=\max\{K,e+1+\#\{a_i>z\}\},\qquad C(z)=\sum_{a_i\le z} x_i^2/z .
$$
Integrating $s(z)z/\alpha+\alpha C(z)/(4\beta^2)$ against $dz/z$ from $\alpha/S$ to $\alpha/K$ costs at most $1+L_y/\alpha+L_x/\beta$. The constant $K$ costs at most one; each row costs at most $y_i/\alpha+x_i/\beta$ by integration on either side of its weight. At the four corners of §1 this upper bound is at most $12887461/484462<\log(S/K)$. For the strict comparison use $(155/4)\log 2-\log(625/512)>(155/4)(6931/10000)-113/512$.

Choose a level at which the integrand is below one. Omit the rows above it and enough additional slots to omit exactly $h=s-1$, where $s=s(z)$. With $v=sz/\alpha\in(0,1)$, the simultaneous bounds on the retained rows are
$$
 s\max y_i\le\alpha v,\qquad s\max x_i\le2\beta v,\qquad
 s\sum x_i^2\le4\beta^2v(1-v).                                        \tag{3}
$$
The last bound follows by multiplying $C(z)<4\beta^2(1-v)/\alpha$ by $sz$. In particular $K\le s<S$ and $r\ge Rs^4$ when $r\ge2^{218}$. Keeping $v$ in (3) means a large pointwise cut bound and the largest possible squared deficit cannot both occur at the chosen level.

## 3. The exterior shortage

In §§3–4 let $s\ge s_0\ge800,\ \rho=f/s,\ \rho_0=f/s_0$, and suppose $r\ge R_0s^4$. Write $G$ for the exterior points sending at most $\rho r$ edges to every ordinary clique. Put $\Delta=hr-|G|$. In the two applications below, the ordinary lists, temporary outside-degree bounds and arc extensions of the 289 supplement hold. Section 5 supplies their exact numerical checks. We strengthen its shortage to
$$
                              \Delta> c r,\qquad c=89/1000 .              \tag{4}
$$

Suppose $\Delta\le cr$. The auxiliary construction in §2 of the 289 supplement applies to a subset of $G$ of size $hr+1$ if available, and to $G$ otherwise. In either case $h\ge799,\ h^2/r<2^{-20},\ r\ge2^{20}$. Put $\xi=c^2+2^{-20}$. A raw auxiliary deficit divided by $r$ is bounded above by $d_*=c+\xi/(2(1-2^{-20}))$, since the other colors pay for the oversized auxiliary parts. For a raw positive deficit $d$ in units of $r$, twice the auxiliary cross edge count divided by $r^2$ is at most $M_*-d^2$, where $M_*=(2+1/799)c^2+3\cdot2^{-20}$. Prune at interpart degree $\tau_a r$, with $\tau_a=27/200$. The final normalized deficit is at most $d_*+(M_*-d_*^2)/(2\tau_a)<\delta=3/25$, since $d_*<\tau_a$. The auxiliary rows are cliques and their $r/10$ lists have independent representatives by $1-\delta-2\tau_a>1/2,\ 100\xi<1$.

Use the ordinary temporary restriction of the 289 supplement, of size at least $255r/256$ and outside-clique degree at most $r/32$. Set $\theta=93/250$ for a large attachment. In the extension from base §3 we need at most **three** prescribed representatives, or two independent exterior points. Indeed the auxiliary fractions $1-\delta-\theta-3\tau_a$ and $1-\delta-2\theta$ exceed $1/10$. The ordinary fractions $255/256-\theta-f-3/32$ and $255/256-2\theta-f$ exceed $1/61$. As in the base proof, every exterior point has a large attachment. Those having a unique one form a clique with their respective row and may be adjoined there. The remaining $P_0$ exterior points each have at least two large attachments before enlargement, and the enlarged row deficits sum to $P_0-1$.

For an enlarged row with normalized deficit $d\in[0,\delta]$, let $z$ count assigned large arrivals (one per large attachment). Retain the $dr$ contribution per arrival in the other-color capacity inequality (base (4)). We claim $(z+1)/(2r)-d\le a_0=53/500$ whenever $z>0$. Otherwise there are at least $\lfloor tr\rfloor$ arrivals with $t=2(d+a_0)$. For $u=\lfloor tr\rfloor/r$, their degrees exceed $\theta r$ and capacity would give $\theta u<(1-u)d+u^2/2+u/(2r)$. But
$$
  \theta t-(1-t)d-t^2/2=2(\theta-a_0)(d+a_0)-d
  \ \ge\ 2(\theta-a_0)(\delta+a_0)-\delta .
$$
The right side exceeds $(\theta+2\delta+a_0)2^{-20}$, covering the rounding and linear term. Thus $z<\lfloor tr\rfloor$, which gives the claim. The net cost per arrival on the capacity side, after using its own deficit, is at most $a_0r$.

For a point with two large attachments, if their normalized degree sum before enlargement is at most $1+2a_0$, its two nonneighbor lists have product at least $r^2(1-\delta-\theta)(\theta-\delta-2a_0)>r+\delta^2r^2$. This is the concave-product endpoint bound of base §3; it exceeds the actual two-clique cut, so a compatible pair would extend. With three large attachments, if all three lists have size at least $21r/100$, the expected number of conflicts is below one by $3(1/r+\delta^2)<(21/100)^2$. Otherwise the normalized net charge exceeds $1-\delta-21/100+2\theta-3a_0>1$. Four or more pay at least $4(\theta-a_0)>1$. Summing the row capacities would now give $rP_0\le(r-1)(P_0-1)$. This proves (4), including the case $P_0=0$ which already contradicts the deficit sum.

## 4. Pay for conflicts with the same tested edges

We give the changed part of the sampling proof. Write $s\max y_i\le A,\ s\max x_i\le X_0,\ s\sum x_i^2\le B,\ \sum y_i\le Y_0$. Put $\gamma=A/f,\ g=X_0/f,\ \kappa=B/f,\ w=\sum d_i^2/r$. Then $w\le\kappa\rho r$. In both applications $\sum d_i\le9r/2,\ \sum(b_i)_+\le r/2$. All definitions of marks, loads and arcs are as in §§3–4 of the 289 supplement. We recall those needed here.

The strong senders have degree greater than $r/2$ in a row. Those with a unique strong row get one uniform draw there and may retry with probability $80\rho$ after drawing a neighbor. Let $N_i$ count unique strong senders in row $i$. Write $m$ for the expected number of marks, $u=\Delta-m$, and $l=u/(\rho r)$. The two cases of the 289 supplement use
$$
 (U_*,\lambda_*)=(41/40,501/1000)\ \text{or}\ (2,0).
$$
They give $\sum N_i d_i\le U_*\sum d_i^2,\ 0\le l\le\lambda_*\kappa,\ m\ge(c-\lambda_*\kappa\rho_0)r,\ m\le sr$. The second case uses the retry surplus when $\sum N_i d_i>(41/40)\sum d_i^2$. The checks on $g,\rho_0$ in §5 ensure that surplus pays the strong-row cost.

For the marked exterior set together with $G$, let $E_i$ be its expected cut into $C_i$, $F_i$ the expected incidences from representatives in other rows, and $n_i$ the expected count of loads above $\rho r$. Put
$$
 Q=\sum n_i(E_i+F_i)/r,\quad Q_F=\sum n_iF_i/r,\quad T=\sum N_i E_i/r.
$$
A specified vertex has representative probability at most $j/r$ per unique sender in its row, with $j=(1+80\rho_0)/(1-g\rho_0)$. Put $M=(513/512)Y_0/f+5/s_0$. As before,
$$
 n_i/r\le x_i+(b_i)_+/r+513y_i/(512\rho),\qquad
 \sum n_i\le Msr,\qquad
 \sum n_i d_i/r\le\sqrt{\kappa Q}.
$$
These follow respectively from $2jg\rho_0\le1/512$, summation, and Cauchy–Schwarz.

Let $e_{ik}=e_J(C_i,C_k)$ for $i\ne k$. Define $H_E=j^2\sum_{i<k}N_iN_k e_{ik}/r^2$. This bounds distinct-row representative conflicts by independence. The within-row conflict count and circular arcs from the 320 supplement give an upper bound
$$
                       \mathcal R=(4/3)Q+jT+H_E
$$
for the expected repair cost. Counting each possible representative endpoint on the very same cross edges also gives
$$
 Q_F\le\frac{j}{r^2}\sum_{i<k}(n_iN_k+n_kN_i)e_{ik}.                  \tag{5}
$$

Test rows independently with probabilities $\pi_i=(a n_i+bN_i)/r$, independently of the sample. The signed cut identity in base §5 has the actual target edges **between** tested rows on its right side. Keeping their expectation there gives
$$
 \sum_i\pi_i E_i+\sum_{i<k}\pi_i\pi_k e_{ik}
 \le \mathcal R+r\,\mathbb E\binom H2+
        (B_\pi+u)^2/2+m/2 ,
$$
where $H=h+\#\{\text{tested rows}\}$ and $B_\pi=\sum\pi_i d_i$. The first sum equals $a(Q-Q_F)+bT$. For $b\ge j$, expansion on each edge and (5) give
$$
       \sum_{i<k}\pi_i\pi_k e_{ik}\ge a Q_F+(b/j)^2 H_E .
$$
Thus both the representative loads and representative-pair conflicts can be paid on their actual edges. Combined, these estimates yield
$$
 (a-4/3)Q+(b-j)T+\big((b/j)^2-1\big)H_E
 \le r\,\mathbb E\binom H2+(B_\pi+u)^2/2+m/2 .                        \tag{6}
$$

For the finite numerical certificate put $\eta=1/(R_0f^2)$ and choose
$$
\begin{aligned}
 a&=\min\!\left(\tfrac72,\frac{249/250}{513\gamma/512+1/256+g\rho_0}\right),
 &D_a&=a-4/3-a^2\kappa/2,\\
 Y&=9D_a/20,\qquad k=(4/3)/(D_a-Y),& b&=j(1+1/k),\\
 V&=aM+9b/s_0,& B_0&=((1+V)^2+V/s_0)/2 .
\end{aligned}
$$
Section 5 checks $D_a>0$ and $a(513\gamma/512+1/256+g\rho_0)+2bg\rho_0<1$; hence the testing probabilities are valid. We have $\mathbb E\binom H2\le B_0s^2$ and $B_\pi+u\le a\sqrt{\kappa Q}+(bU_*\kappa+l)\rho r$. Use Young's inequality on the mixed term with coefficient $Y$ on $Q$, then multiply (6) by $k$. The resulting coefficients dominate $4/3,j,1$ on $Q,T,H_E$, respectively. Since $s^2r\le\eta\rho^2r^2$, this gives
$$
\begin{aligned}
 \mathcal R&\le P(l)\rho^2r^2,\\
 P(l)&=k(bU_*\kappa+l)^2\!\left(\tfrac12+\frac{a^2\kappa}{4Y}\right)
       + k\left(B_0+\frac1{2s_0}\right)\eta .
\end{aligned}
$$

For one tested row, the signed cut adds at most $ud_i+u^2/2+m/2+r\binom{s}{2}$ beyond repairs. Therefore its expected moderate assignment count is at most $\epsilon(l)\rho r$, where
$$
 \epsilon(l)=P(l)+gl+l^2/2+\eta(1/2+1/(2s_0)).
$$
When oversampling is necessary $l=0$. At up to twice the original thinning probability the same three conflict terms are bounded by $4\mathcal R$, since $Q'\le4Q,\ T'\le2T$, and $H_E$ bounds representative-pair conflicts at either probability. The oversampling floor of base §5 and the final row inequality of the 289 supplement now require
$$
 (1-\epsilon(l))(c-\lambda_*\kappa\rho_0)+l-\lambda_*\kappa
       -(8P(0)+2\eta)\rho_0-\frac1{fR_0s_0^2}\le0.                    \tag{7}
$$
Specifically $Z_0=8P(0)+2\eta$ bounds the oversampling excess divided by $\rho^2r$, since $Z_0\rho_0^2<\min(c/128,1/16)$. The lower bound on failed senders retains $u$ and the moderate quadratic sum is at most $\epsilon(l)\rho r m$, as in (6) of the 289 supplement. The left side of (7) is concave in $l$; it suffices to check $0,\lambda_*\kappa$ in the first branch and $0$ in the second.

## 5. Exact certificates and the earlier mixed profile

For Theorem 1 use $s_0=2500,\ R_0=2^{19},\ Y_0=2$. For each $i=0,\ldots,63$, bound the level parameter $v$ from (3) on $[i/64,(i+1)/64]=[v_-,v_+]$. Set
$$
 u_*=\max(v_-,\min(1/2,v_+)),\qquad
 A=\alpha v_+,\quad X_0=2\beta v_+,\quad B=4\beta^2u_*(1-u_*).
$$
These upper bounds apply throughout the interval, including when $\kappa$ is small. The checker verifies the ordinary transversal test $4\cdot61^2\gamma\rho_0<1$, temporary row sizes and outside degrees, the circular-arc list fraction, both retry bounds, validity of the row tests, $\epsilon<1$, the oversampling cap, and (7). Every one of the 192 rational endpoint values on the left of (7) exceeds $1/1000$. This contradiction proves Theorem 1. [Exact arithmetic](verify_cutoff_218.py)

For Theorem 3 use the *original* total-degree pruning threshold $r/4$ in the 320 supplement and keep its original cut and deficit definitions. With $P$ deletions, its normalized residual interpart edge count is at most $1-P/(4r)$. The padded draw with $r$ positions in §1 shows
$$
 q/2\le P/r+1/2+1-P/(4r)\le9/2 .
$$
Thus $q\le9$. At most $2(9/2+q/2)\le18$ lists fall below $r/2$, giving at most $9+18+128=155$ original exceptions. This strengthens the old count for every choice of maximal pairs.

Suppose the ordinary rows can be indexed so that $d_i\le\lceil(4/25)r/i\rceil$ and $e_J(C_i,V\setminus R_i)\le\lceil r^2/(100i)\rceil$ up to $i=2^{36}$, with zero thereafter. Discard the first 644 ordinary rows and add exceptions or further rows to omit exactly 799 slots in total. Write $q_0=4/25$. At $r\ge2^{50}$, $s=s_0=800$, the following bounds hold:
$$
 s\max y_i<13/1000,\quad s\max x_i<1/5,\quad
 s\sum x_i^2<4/125,\quad \sum y_i<19/100 .
$$
Indeed $\sum_{i>644}i^{-2}\le1/644$, $H_{2^{36}}<27$, and the rounding adds at most $54q_0/r+2^{36}/r^2$ to the squared-deficit sum. The foreign count costs at most $\log(2^{36}/644)/100+2^{36}/r^2$. The earlier family retains the per-destination degree bound and its total deficit is at most $9r/2$. With $R_0=2^{50}/800^4$, the same checker verifies all three endpoints of (7) exceed $1/1000$. This proves Theorem 3. It uses the small foreign counts together with the deficits in the original rows; the separate deficit bound of Theorem 2 applies to the newly chosen rows.

The uniform argument still needs a width with simultaneous control in (3). For example, the numerical arrays $x_i=1/(5(i+3)),\ y_i=1/(100(i+3))$ for $1\le i\le2^{24}$, zero thereafter, obey (2) at $p=2,t=4/5$ and have $x_i\le1/20$. After deleting the largest $h$ entries, $2500\le h\le2^{19}$, the squared tail times $h+1$ is at least
$$
 \frac1{25}\left(\frac{h+1}{h+4}-\frac{h+1}{2^{24}+4}\right)>\beta^2 .
$$
This follows by integrating $1/(x+3)^2$. It identifies a limitation of the aggregate width estimates. Realization by actual edge labels is open here, as is the conjecture for every $r\ge3$. [Research handoff](../README.md)
