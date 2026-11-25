# Harmonic row deficits and a cutoff of $2^{289}$

Robert Sneiderman’s research notes · 22 November 2026

**Theorem 1.** For every integer $r\ge 2^{289}$, every $r$-coloring of the edges of $K_{r^2+1}$ has $r+1$ vertices whose induced edges omit a color.

**Theorem 2.** Suppose $r\ge2^{44}$ and a counterexample exists. For a sparsest color $J$, choose the original parts by the minimum-degree rule in §5. After setting aside 4,095 parts as specified there, the sum of the numbers of $J$-edges from each retained clique to other original parts exceeds $r^2/320{,}000$. This excludes the previously proposed zero-cross-edge profile across $2^{44}$ rows for this choice of parts. A harmonic deficit profile with positive cross counts is a separate question.

The two preceding manuscripts follow this supplement in the PDF. References to the **320 supplement** and the **base** mean those manuscripts. The full argument awaits independent mathematical review. [320 supplement](cutoff-320.md) · [Base manuscript](balanced-coloring.md) · [Exact checks](verify_cutoff_289.py)

## 1. Parameters and a count of independent transversals

Assume every color graph has independence number at most $r$. Use the notation of [Appendix F](cutoff-320.md). The ordinary cliques $C_i$ lie in original parts $R_i$. Write $b_i=|R_i|-r,\ d_i=r-|C_i|,\ x_i=d_i/r,\ y_i=e_J(C_i,V\setminus R_i)/r^2$. Before the width selection, at most 1,777 parts have been omitted. All remaining $b_i\le r/256$. Write
$$
 K=1800,\quad R=2^{19},\quad f=7/30,\quad
 \alpha=29/250,\quad\beta=19/125,\quad S=2^{135/2}.
$$
Use the level selection in §1 of [Appendix F](cutoff-320.md) with these $\alpha,\beta,K,S$. Its integral bound is $1+1/\alpha+9/(2\beta)<\log(S/K)$. Indeed $1/\beta>1/(4\alpha)$ and $\log(S/K)=(113/2)\log 2+\log(256/225)>(113/2)(6931/10000)+31/256$. We obtain $K\le s<S,\ h=s-1,\ \rho=f/s,\ \rho_0=f/K$. For the $r-h$ remaining rows, put $D=\sum d_i,\ \sigma=\sum d_i^2,\ w=\sigma/r$. The guarantees are
$$
 \gamma=\alpha/f,\quad g=2\beta/f,\quad \kappa=\beta^2/f,\qquad
 y_i\le\gamma\rho,\quad d_i\le g\rho r,\quad
 w\le\kappa\rho r,\quad D\le 9r/2,\quad r\ge Rs^4 .                 \tag{1}
$$
The last bound uses $19+4(135/2)=289$.

For lists of size at least $L$, suppose each list meets at most $L^2/4$ forbidden pairs to the other lists, counted in total. Any subfamily has independent representatives. In fact its number $Z(T)$ of independent transversals is at least $(L/2)Z(T\setminus\{i\})$ for each $i\in T$. Induct on $|T|$, starting with $Z(\varnothing)=1$. Of at least $LZ(T\setminus\{i\})$ extensions, a forbidden pair to row $j$ rules out at most $Z(T\setminus\{i,j\})\le(2/L)Z(T\setminus\{i\})$. Summation proves the claim, also for a real lower bound $L$. We use $L=r/61$, since $4\cdot61^2\alpha/K<1$.

## 2. A stronger shortage of exterior points

Let $G$ be the exterior points sending at most $\rho r$ edges of $J$ to each ordinary row and put $\Delta=hr-|G|$. We claim
$$
                         \Delta>cr,\qquad c=13/200.                  \tag{2}
$$
We detail the changes to base §3. Its proof also gives (2) for the rows of Theorem 2 under the list and size conditions checked in §5. In both applications $h\ge1799,\ r\ge2^{20},\ h^2/r<2^{-20}$. Independent $h+1$ points of $G$ leave lists of size $r/61$ and would extend. If $\Delta\le cr$, take $X_0\subseteq G$ of size $hr+1$ when possible and otherwise take $X_0=G$. Write $|X_0|=hr+b$. Either $b=1$ or $b=-\Delta$ with $0\le\Delta\le cr$.

For the $h$ auxiliary parts on $X_0$, let $\eta_0$ be its target edge excess over the Turán floor and $\mu_0\le\eta_0$ the number of internal pairs missing $J$. As in base §3, $2\eta_0/r^2\le\xi=c^2+2^{-20}$. Each of the other $r-1$ colors needs at least $(|B|-r)_+$ edges in each auxiliary part $B$, by deleting an endpoint per edge. Consequently $\sum_B(|B|-r)_+\le\eta_0/(r-1)$. Adding the net deficit $-b$, every raw positive deficit divided by $r$ is at most
$$
 d_* = c+\frac{\xi}{2(1-2^{-20})}<0.06712.
$$
If $X_a$ counts interpart target edges and $d=(r-|B|)_+/r$, the stability calculation gives
$$
  2X_a/r^2+d^2\le M_*=(2+1/1799)c^2+3\cdot2^{-20},\qquad X_a/r^2\le\xi.
$$
Indeed the sum of squared deviations of the actual parts plus $2X_a$ is at most $4\eta_0$ plus the balanced sum of squared deviations, at most $b^2/h+h/4$. Delete vertices of current interpart degree above $\tau r$, where $\tau=27/250$. A part's final normalized deficit is at most $d+(M_*-d^2)/(2\tau)$. This expression is increasing on $[0,d_*]$, and its value at $d_*$ is below $\delta=43/500$.

Base §3 now gives auxiliary cliques with arbitrary lists of size $r/10$ admitting independent representatives. Its two tests are $1-\delta-2\tau>1/2$ and $100\xi<1$. In the temporary ordinary restriction, the minimum surviving size is $255r/256$ and each survivor has degree at most $r/32$ outside its original clique. For (1) these follow from $1/40+g\rho_0+1/256<1/32$ and $(g+40\gamma)\rho_0<1/256$. For the prescribed representatives the auxiliary test is $1-\delta-93/250-4\tau>1/10$. The other list bounds and the attachment comparisons in base §3 keep their parameters $\theta=93/250,\ t=133/500$; the exact checker includes each. The resulting attachment contradiction proves (2). For the circular-arc argument with (1) we also have $1-g\rho_0-3/4-f>1/61$.

## 3. Using the labels of edges into a row

The other colors constrain every set of $z$ exterior vertices of target degrees $j_y$ into a clique of deficit $d$. [Appendix F](cutoff-320.md), (4)–(5), gives
$$
 \sum_y(j_y+d)\le(r-1)d+z(z+1)/2,\qquad
 b^2/2+(b-d)v_0-J_d\le\lambda d^2+v_0^2/2,                         \tag{3}
$$
where $\lambda=501/1000,\ b$ is the number of strong assignments, $q=j_y/(r-d)$, $J_d=\sum_{\rm strong}2d(1-q)$, and $v_0\ge0$. Here a vertex with degree greater than $r/2$ in more than one row is assigned to two of them. A vertex with exactly one such row is assigned there. The first inequality gives $b\le2d,\ \sum_{\rm strong}j_y\le rd$; the second uses $2g\rho_0/(1-g\rho_0)<1/1000$.

For each uniquely assigned sender, if a first uniform draw in its row hits a target neighbor, retry with probability $80\rho$ using an independent uniform draw. Accept the first nonneighbor. The success probability is $v=(1-q)(1+80\rho q)$. After paying $r(1-v)+\rho r v+2d(1-q)$ from $j_y+d$, the amount left is
$$
 (1-q)\big\{r\rho[80q(1-\rho)-1]-d\big\}\ \ge\ 37\rho r(1-q).
$$
This uses $q>1/2$ and $40(1-\rho_0)-1-g>37$. Each assignment of a multiply strong sender still pays at least $r/2+2d(1-q)$. [Lean proof of the retry calculation](HarmonicRow.lean)

Let $N_i$ be the number of uniquely assigned senders in row $i$, and let $M_i$ be the sum of their $1-q$. Put $U=\sum N_i d_i/\sigma$, taking $U=0$ if $\sigma=0$. Thus $0\le U\le2$. Since the sum of the $q$'s of the unique assignments in row $i$ is at most $d_i/(1-g\rho_0)$, the total extra charge satisfies
$$
 37\rho r\sum_iM_i \ \ge\ \frac{37}{g}\sum_i d_iM_i
 \ \ge\ \frac{37}{g}\big(U-1/(1-g\rho_0)\big)\sigma .
$$
When $U>41/40$ this pays the entire $\lambda\sigma$ in the sum of (3). Use the bounds $(U_*,\ell)=(41/40,\lambda)$ for $U\le41/40$, and $(U_*,\ell)=(2,0)$ otherwise. In both cases $\sum N_i d_i\le U_*\sigma$.

All successful uniques and all moderate senders are eligible. Let $A$ be their expected count and $L_0=D+\Delta+1-A$. Applying (3) at $v_0=0$ gives $rL_0\le rD+\ell\sigma$. Mark eligible senders independently with probability $\min(1,\Delta/A)$, with all draws independent across senders. Here $A\ge\Delta+1-\ell w>0$. For the expected number of marks $m$, put $u=\Delta-m=(\Delta-A)_+$ and $\vartheta=u/(\rho r)$. Then
$$
       0\le\vartheta\le\ell\kappa,\qquad (c-\ell\kappa\rho_0)r\le m\le sr .
$$
Let $v_i$ be the expected number of marks from moderate senders assigned in advance to row $i$ of degree above $\rho r$. Applying (3) to the strong senders and the marked moderates gives, as in §5 of [Appendix F](cutoff-320.md),
$$
                  rL_0+\rho r m\le rD+\ell\sigma+\sum_i v_i^2+m.       \tag{4}
$$
Indeed the extra charge just proved is available also at $v_0=v_i$. The variance and linear cost of the moderate count sum to at most $m$.

## 4. Counting repairs and retaining the unsampled shortage

Write $W=G\cup\{\text{marked senders}\}$. Use $E_i,F_i,n_i,Q,Q_F,T$ from §4 of [Appendix F](cutoff-320.md). Thus $E_i$ counts expected target edges between $C_i$ and $W$, $F_i$ counts expected target incidences from other rows' representatives, and $n_i$ counts expected loads exceeding $\rho r$. In particular
$$
 Q=\sum n_i(E_i+F_i)/r,\quad Q_F=\sum n_iF_i/r,\quad T=\sum N_iE_i/r.
$$
At any thinning probability the chance of a specific representative point for one sender is at most $j/r$, where $j=1011/1000>(1+80\rho_0)/(1-g\rho_0)$. Put $M=2(513/512)/f+5/K$, $\chi=j^2U_*^2/2$. The bounds on heavy loads and on the number $P_*$ of added repair edges are
$$
\begin{aligned}
 n_i/r &\le x_i+(b_i)_+/r+513y_i/(512\rho),& \sum n_i&\le Msr,\\
 B_n=\sum n_i d_i/r&\le\sqrt{\kappa Q},&
 Q_F&\le 10Msr+jU_*w\sqrt{\kappa Q},\\
 \mathbb E P_*&\le (4/3)Q+jT+\chi w^2+243r. &&
\end{aligned}                                                        \tag{5}
$$
For the first line $F_i\le y_i r^2/512$ follows from $2jg\rho_0<1/512$. For the second, $\rho r n_i\le E_i+F_i$ gives Cauchy–Schwarz, and $e_J(C_i,C_k)\le r+d_i d_k$ gives $F_i\le10r+jU_*wd_i$, since $\sum N_i\le9r$. The same two-clique bound on distinct-row representative pairs contributes at most $243r+\chi w^2$. Same-row and representative-to-exterior conflicts together contribute $jT$ by the same-row count in [Appendix F](cutoff-320.md). The $4Q/3$ comes from intersecting arcs. Thus the right side of (5) bounds repairs at the base probability and the corresponding expression at each new thinning probability.

Test rows independently with probabilities $\pi_i=(a n_i+bN_i)/r$, where $a=199/100,\ b=1217/1000$. These are at most one by (5) and $a(513\gamma/512+1/256+g\rho_0)+2bg\rho_0<1$. Put
$$
 V=aM+9b/K,\quad B_0=((1+V)^2+V/K)/2,\quad Y=19/100,\quad k=99/20.
$$
In the expected signed cut inequality (base §5), the left side is $a(Q-Q_F)+bT$, the tested-row binomial costs at most $B_0s^2r$, and the quadratic cost is at most $(B_\pi+u)^2/2$ with a further $m/2$. Here $B_\pi=\sum\pi_i d_i\le a\sqrt{\kappa Q}+bU_*w$.

For $0\le\vartheta\le\ell\kappa$ write $t=bU_*+\vartheta/\kappa$, $\eta=1/(Rf^2)$, and define
$$
\begin{aligned}
 C_w(t)&=k\left(\chi+t^2/2+\frac{a^2(t+jU_*)^2\kappa}{4Y}\right)+\chi,\\
 C_s&=k\left(B_0+(10Ma+1/2)/K+243/K^2\right)+243/K^2,\\
 P(\vartheta)&=C_w(t)\kappa^2+C_s\eta,\\
 \epsilon(\vartheta)&=P(\vartheta)+g\vartheta+\vartheta^2/2+
                         \eta(1/2+1/(2K)).
\end{aligned}
$$
To verify these expressions when $w$ is small, use $w\le\kappa\rho r$ **before** combining it with $u=\vartheta\rho r$. Thus $B_\pi+u\le a\sqrt{\kappa Q}+t\kappa\rho r$. Young's inequality bounds the resulting mixed term from the cut and $aQ_F$ by $YQ+a^2(t+jU_*)^2\kappa(\kappa\rho r)^2/(4Y)$. The remaining coefficients of $Q,T$ are $a-4/3-a^2\kappa/2-Y,\ b-j$; after multiplication by $k$ they exceed $4/3,j$. Using $s^2r\le\eta\rho^2r^2$ gives
$$
 (4/3)Q+jT+\chi w^2+243r\le P(\vartheta)\rho^2r^2 .
$$
For a single tested row the cut costs $ud_i+u^2/2+m/2+r\binom{s}{2}$ beyond the repairs. Hence $E_i\le\epsilon(\vartheta)\rho^2r^2$ and $v_i\le\epsilon(\vartheta)\rho r$.

Put $Z=8P(0)+2\eta$, using the branch's $U_*$. If $A>\Delta$, then $u=0$. Oversample as in base §5 by $z'=\min(A-\Delta,\Delta/128,r/16)$. The doubled thinning bound $Q'\le4Q,\ T'\le2T$ and the floor $rz'/2-rs^2$ give $z'/r\le Z\rho^2<\min(c/128,1/16)$, forcing $z'=A-\Delta$. If $A\le\Delta$, the identity $L_0=D+1+u$ holds. Combining the two cases retains the full linear term
$$
                           L_0\ge D+u-Z\rho^2r .
$$
Since $\sum v_i^2\le\epsilon(\vartheta)\rho r m$, (4) now requires
$$
 (1-\epsilon(\vartheta))(c-\ell\kappa\rho_0)+\vartheta
   -\ell\kappa-Z\rho_0-\frac1{fRK^2}\ \le\ 0 .                        \tag{6}
$$
The function $\epsilon$ is increasing, convex and less than one throughout each interval by the endpoint bounds below. Therefore the left side of (6) is concave and takes its minimum at an endpoint. All entries below are strict rational comparisons. [Checker for (1)–(6)](verify_cutoff_289.py)

| $U_*$ | $\vartheta$ | Upper bound on $\epsilon$ | Lower bound on the left side of (6) |
| --- | --- | --- | --- |
| $41/40$ | $0$ | $229/1000$ | $3/10000$ |
| $41/40$ | $\lambda\kappa$ | $395/1000$ | $39/1000$ |
| $2$ | $0$ | $789/1000$ | $12/1000$ |

Each lower bound contradicts (6). This proves Theorem 1.

## 5. Can the proposed rows occur?

There is a choice of the initial stability partition retaining local edge information. On the residual target graph choose a vertex of minimum degree and take its closed neighborhood as the next part $R_i$. Repeat, filling any unused slots with empty parts. The chosen vertices are independent, so there are at most $r$ nonempty parts. Every $v\in R_i$ has residual degree at least $|R_i|-1$. Consequently each missing internal neighbor of $v$ is paid for by an edge from $v$ to a later part. If $\mu$ counts internal missing pairs and $X$ counts cross edges, summing gives $2\mu\le X$. The identity $X=\eta_J+\mu-(\sum b_i^2-1)/2$ of base §1 gives $\mu\le\eta_J$. Thus this is a permissible initial partition for the extraction.

For any extracted clique $C_i$, sum the local degree inequality over its vertices. The internal missing pairs incident to the clique number at most $y_i r^2$. All other internal missing pairs lie among the $d_i+b_i$ points of $R_i\setminus C_i$. The $r-1$ other colors therefore require, when $b_i>0$,
$$
 (r-1)b_i\le y_i r^2+\binom{d_i+b_i}{2}.                             \tag{7}
$$
For $r\ge2^{44}$, set aside the original exceptions and every retained row with $d_i>r/512$. There are at most $1777+2304=4081$ such parts by $D\le9r/2$ before width selection. Add arbitrary parts to make $h=4095,\ s=4096$. Put $Y_0=\sum y_i$ over the remaining rows and $\rho=f/s$. The sum counts incidences; an edge between two retained cores contributes twice.

If $Y_0>1/32768$, Theorem 2 follows. Otherwise each ordinary list of size $r/61$ passes the transversal test of §1, since $4\cdot61^2Y_0<1$. Removing vertices of degree above $r/40$ outside their part leaves row size at least $(1-1/512-40Y_0)r\ge255r/256$ and outside-clique degree at most $(1/40+1/512+1/256)r<r/32$. Independent $h+1$ points of $G$ leave fraction at least $1-1/512-f>1/61$ in each row. Since $h^2/r<2^{-20}$, §2 applies and gives $\Delta>cr$.

In (7), $r-1-d_i-b_i/2\ge r/2$. Expansion gives $(b_i)_+\le 2r y_i+d_i^2/r$. The union of the omitted original parts has at least $hr+1-\sum (b_i)_+$ vertices, with the sum taken over retained rows. Among those omitted vertices, fewer than or equal to $Y_0r/\rho$ can each send more than $\rho r$ target edges into some retained row. All the others belong to $G$. Combining these counts yields
$$
 cr<\Delta\le (2+1/\rho)Y_0r+\sum_i d_i^2/r-1,\qquad
 \sum_i d_i^2/r\le D/512\le 9r/1024.
$$
Thus $Y_0>(c-9/1024)/(2+4096/f)>1/320000$, proving Theorem 2. The same lower bound holds for any allowed padding of the omitted parts. For the earlier $11/(80i)$ profile, even rounded up, only the first 70 rows can have $d_i>r/512$. One may therefore omit **any additional 2,248 rows** along with those 70 and the original exceptions. The remaining cores still obey the incidence bound. [Lean proof of the overfull-part calculation](HarmonicRow.lean)

There is a separate numerical check on the size of the old obstruction. Write $q=11/80,\ m_0=2^{44}$. For its profile $x_i=q/i$, deleting the largest $k_0=8192$ deficit rows in addition to the original exceptions leaves width $s\le9970$. Even rounding each nonzero deficit up to $\lceil qr/i\rceil/r$, for $r\ge m_0$ we have
$$
 s\sum_{i>k_0}x_i^2\le9970\big(q^2/k_0+(64q+1)/2^{44}\big)<\beta^2 .
$$
Here $\sum_{i>k_0} i^{-2}\le 1/k_0$ and $\sum_{i\le m_0}1/i<32$. Also $s\max_{i>k_0}x_i\le9970(q/(k_0+1)+2^{-44})<2\beta$. Thus these deficits pass both updated deficit tests by that width.

For a remaining numerical obstruction take $x_i=4/(25i)$ and $y_i=1/(100i)$ on $1\le i\le2^{36}$, zero elsewhere. These arrays obey the two aggregate budgets in [Appendix F](cutoff-320.md) with $P/r=39/10$. After any 4,095 deletions the remaining $y_i$ still sum to at least $\log((2^{36}+1)/4096)/100>1/320000$. Nevertheless after any $h\le2^{32}$ deletions the squared tail times $h+1$ is at least $(4/25)^2(1-(h+1)/(2^{36}+1))>(4/25)^2(14/15)>\beta^2$. This follows by integrating $t^{-2}$ after deleting the largest terms. Realizability of this joint profile under the full coloring constraints is open here. So are the general conjecture and the project's remaining $r=19$ case. [Research handoff](../README.md)
