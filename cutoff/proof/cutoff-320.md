# A cutoff of $2^{320}$ for the balanced coloring conjecture

Robert Sneiderman research project · Private proof supplement · 22 November 2026

**Theorem.** For every integer $r\ge 2^{320}$, every $r$-edge-coloring of $K_{r^2+1}$ has $r+1$ vertices whose induced edges omit a color.

The base manuscript, *A large-order bound for the Erdős–Gyárfás balanced coloring conjecture*, follows this supplement in the PDF. Its cutoff is $2^{483}$. We use its §1 clique extraction, §3 exterior-shortage argument, §4 circular-arc construction and §5 signed cut identity. We verify the estimates depending on the new parameters below. In particular, the cut into a row from its own original part and the cut from the other parts play different roles in the sampling calculation. Independent review of the combined proof is pending. [Base manuscript](balanced-coloring.md) · [Base proof source](balanced-coloring.md) · [Original conjecture](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf)

## 1. Selecting the ordinary rows

Assume a counterexample and fix a sparsest hue $J$. All degrees and cuts below count $J$-edges. Every color has independence number at most $r$. By §1 of the base manuscript, on all $r^2+1$ vertices there are $r$ original parts $R_i$, with $b_i=|R_i|-r$, $O=\sum (b_i)_+\le r/2$ and at most $X\le r(r-1)$ edges between parts. In the pruning step $P\le4X/r$ vertices are removed at current cross degree greater than $r/4$. Outside at most 1,649 omitted parts one obtains cliques $C_i\subset R_i$. Set $d_i=r-|C_i|$, $x_i=d_i/r$ and $y_i=e_J(C_i,V\setminus R_i)/r^2$. The extraction gives
$$
 \sum x_i\le P/r+1/2,\qquad
 \sum y_i\le 2X/r^2-P/(4r)\le2-P/(4r).                       \tag{1}
$$
For the first bound, §1 pays for the neighbors of the independent pairs by omitting the short slots, leaving total deficit at most $P+O-1$. For the second, at least $rP/4$ of the original $2X$ cross incidences belong to removed vertices. Each retained vertex has at most $r/4$ neighbors in the other retained cliques together. Omit also the parts with $b_i>r/256$. There are at most 128 of these, so the total omitted count $e$ is at most 1,777.

Fix the constants
$$
 \begin{gathered}
 K=2160,\quad R=2^{19},\quad f=7/30,\quad
 \alpha=8/75,\quad \beta=33/250,\\
 \gamma=\alpha/f,\qquad g=2\beta/f,\qquad \kappa=\beta^2/f .
 \end{gathered}
$$
Assign each retained row weight $a_i=\max\{y_i,\alpha x_i/(2\beta)\}$. For $z>0$, put
$$
 s(z)=\max\{K,e+1+\#\{i:a_i>z\}\},\quad
 A(z)=s(z)z,\qquad C(z)=\sum_{a_i\le z}x_i^2/z .
$$
Integrate $A/\alpha+\alpha C/(4\beta^2)$ with measure $dz/z$ from $\alpha/S$ to $\alpha/K$, where $S=2^{301/4}$. Since $e+1\le K$, the constant $K$ contributes at most one. A row contributes at most $a_i/\alpha+\alpha x_i^2/(4\beta^2a_i)$, with zero contribution for $a_i=0$. This follows by integrating the count below $a_i$ and the squared term above $a_i$. If $a_i=\alpha x_i/(2\beta)$, the displayed cost is $x_i/\beta$. Otherwise the first term is $y_i/\alpha$ and the second is at most $x_i/(2\beta)$. By (1), $P/r\le4$, and $1/\beta>1/(4\alpha)$, the integral is at most
$$
 1+\frac{2-P/(4r)}{\alpha}+\frac{P/r+1/2}{\beta}
 \le 1+\frac1\alpha+\frac{9}{2\beta}<\log(S/K).                 \tag{2}
$$
Indeed $K=2^{11}(135/128)$, $\log2>6931/10000$, and $\log(135/128)<7/128$. Thus at some level the integrand is below one. There $A<\alpha$ and $AC<\beta^2$ by the arithmetic–geometric mean inequality, so $s=s(z)<S$.

Omit the rows above the level and enough additional rows to omit exactly $h=s-1$ parts in total. There are enough since $s<r$. Write $\rho=f/s$, $\rho_0=f/K$, $D=\sum d_i$, $\sigma=\sum d_i^2$, $w=\sigma/r$ over the remaining ordinary rows. We have
$$
 y_i\le\gamma\rho,\qquad x_i\le g\rho,\qquad
 w\le\kappa\rho r,\qquad D\le9r/2,\qquad r\ge Rs^4.             \tag{3}
$$
The last inequality follows from $19+4(301/4)=320$.

## 2. Lists and exterior shortage

Arbitrary lists of size at least $r/61$ in any subset of the ordinary rows admit independent representatives. Draw one point per list uniformly and independently. An edge event has probability at most $61^2/r^2$ and shares a row with at most $2\gamma\rho r^2+1$ events including itself, by the outside-part cut in (3). The symmetric Lovász local lemma applies since
$$
 (2719/1000)\,61^2(2\gamma\rho_0+2^{-40})<1,\qquad
 \exp(1)<2719/1000,\quad r\ge2^{20}.
$$

Let $G$ consist of the exterior points of degree at most $\rho r$ in every ordinary row and let $\Delta=hr-|G|$. We claim $\Delta>cr$ for $c=121/2000$. The reduction in §3 of the base manuscript applies with the following verifications. First, $h+1$ independent points of $G$ leave fraction at least $1-g\rho-f>1/61$ in each row. Second, $h\ge K-1$, $h^2/r<1/(RK^2)<2^{-40}$. Thus the auxiliary part bound in that section is
$$
 (2+1/(K-1))c^2+3\cdot2^{-40}<(43/500)^2 .
$$
The auxiliary cliques, their $r/10$ lists and the attachment calculations in §3 use these bounds and $r\ge2^{20}$.

For the temporary restriction of each ordinary clique, remove vertices of degree greater than $r/40$ to $V\setminus R_i$. At most $40y_i r$ vertices are lost. The number of points in $R_i\setminus C_i$ is $d_i+b_i\le(g\rho+1/256)r$. Hence the survivors have degree at most $r/32$ outside the original clique, and the surviving size is at least $255r/256$, since
$$
 1/40+g\rho_0+1/256<1/32,\qquad (g+40\gamma)\rho_0<1/256.
$$
With $\theta=93/250$, both $255/256-\theta-f-4/32$ and $255/256-2\theta-f$ exceed $1/61$. These are the two ordinary list sizes used by the extension in §3. Its contradiction gives the claimed shortage. For the circular-arc extension in §4, the available fraction is $1-g\rho-3/4-f>1/61$. This verifies the ordinary list condition at every use.

## 3. What a strong assignment pays

Return to the original ordinary cliques. There are $D+\Delta+1$ exterior vertices outside $G$. As in the base manuscript, assign a vertex with degree greater than $r/2$ in at least two ordinary rows to two such rows. Assign a vertex with just one such row to it. The remaining vertices outside $G$ are called moderate. In a row of deficit $d$, write $b$ for the count of strong assignments. For any $z$ exterior points of row degrees $j_y$, the original colors give
$$
 \sum_y(j_y+d)\le(r-1)d+z(z+1)/2 .                             \tag{4}
$$
Indeed each of the $r-1$ other colors needs at least $z-d$ edges on the points and the clique together. Applying (4) to $2d+1$ strong assignments would give $r/2<d+1$, excluded by (3). Thus $b\le2d$. With $z=b$, (4) also gives $\sum j_y\le rd$, because $b(b+1)/2-bd\le b/2\le d$.

For a uniquely assigned vertex, write $q=j_y/(r-d)>1/2$. Draw uniformly in the clique. If the first point is a neighbor, retry once with probability $6\rho$, independently and uniformly. A nonneighbor is obtained with probability $v=(1-q)(1+6\rho q)$. Use independent trials for the different senders. The degree plus deficit pays
$$
 j_y+d\ \ge\ r(1-v)+\rho rv+2d(1-q).
$$
The difference is $(1-q)\{r[6\rho q(1-\rho)-\rho]-d\}\ge0$, since $3(1-\rho_0)-1>g$. Each assignment of a doubly assigned vertex pays at least $r/2+2d(1-q)$. Denote the sum of these last $2d(1-q)$ contributions in one row by $J_d$. It is nonnegative and $J_d\ge2d(b-d/(1-d/r))$ by the bound on $\sum j_y$.

For **every** $v_0\ge0$, with $\lambda=501/1000$, we have the row inequality
$$
             b^2/2+(b-d)v_0-J_d\le \lambda d^2+v_0^2/2 .        \tag{5}
$$
For $b\le d$ this follows immediately. Otherwise write $b=(1+t)d$, $0<t\le1$. The left side is at most
$$
 (1-t)^2d^2/2+t d v_0+\frac{2(d/r)}{1-d/r}\,d^2 .
$$
The first two terms are bounded by $(1-t)d^2/2+t(d^2+v_0^2)/2$. The last coefficient is below $1/1000$ by (3). This proves (5), including $d=0$ in the first branch. Lean checks the retry inequality and (5) for real parameters under the stated bounds. [Lean source](StrongRowCharge.lean)

All moderate vertices and all successful unique senders are eligible. Let $A$ be their expected count and $L=D+\Delta+1-A$. Apply (4) to the strong assignments, sum (5) with $v_0=0$, and use $\sum b/2\le D$. This gives $rL\le rD+\lambda\sigma$. Mark eligible vertices independently with probability $p=\min(1,\Delta/A)$, which is defined since $A\ge\Delta+1-\lambda w>0$. Write $W=G\cup Z$ for $G$ and the marks, $m=\mathbb E|Z|$, $u=\Delta-m$. Then
$$
 0\le u\le\lambda w,\qquad (c-\lambda\kappa\rho)r\le m\le sr . \tag{6}
$$

## 4. Counting the repairs

Use the three representative conflicts and the circular arcs of §4 of the base manuscript. The arcs still have length four times the load on $3r$ positions. Loads are at most $3r/4$, and §2 above verifies that the repaired graph on $W$ has independence at most $h$. Write $E_i=\mathbb E e_J(C_i,W)$, $F_i$ for the expected incidences into $C_i$ from representatives in other rows with multiplicity, $n_i$ for the expected count of loads greater than $\rho r$ in row $i$, and $N_i$ for the number of uniquely assigned strong senders there. Put
$$
 Q=\sum n_i(E_i+F_i)/r,\quad Q_F=\sum n_iF_i/r,\quad
 T=\sum N_iE_i/r,\quad B_n=\sum n_i d_i/r .
$$
At every thinning probability a particular point has representative probability at most $j/r$ per sender in its row, with $j=1001/1000$, because $(1+6\rho_0)/(1-g\rho_0)<j$. Since $N_k\le2d_k$ and $2jg\rho_0<1/512$, we get $F_i\le y_i r^2/512$.

A marked sender from $R_i\setminus C_i$ counts at most once towards $n_i$. For the senders outside $R_i$, their own degrees into $C_i$ sum to at most $y_i r^2$, and their representatives add at most $F_i$ in expectation. Consequently, for $M=8591/1000$,
$$
 \frac{n_i}{r}\le x_i+(b_i)_+/r+\frac{513y_i}{512\rho},
 \qquad \sum n_i\le Msr.
$$
Here $\sum(x_i+(b_i)_+/r)\le5$ and $\sum y_i\le2$. Also $\sum N_i\le9r$, $\sum N_i d_i\le2\sigma$, and $\rho r n_i\le E_i+F_i$, so $B_n\le\sqrt{\kappa Q}$. The two-clique bound $e_J(C_i,C_k)\le r+d_id_k$ now gives $F_i\le10r+2.01wd_i$ and $Q_F\le10Msr+2.01w\sqrt{\kappa Q}$.

To count representative conflicts, remove from $E_i$ the contribution $E_i^0$ of the marked unique senders of this same row. If their expected number is $t_i$, then $E_i^0\ge rt_i/2$. Their mutual conflicts cost at most $t_i^2/2$ by independence. Representative hits on exterior points outside this group cost at most $jN_i(E_i-E_i^0)/r$, by independence across senders. Since $t_i\le N_i$, the sum of these two costs is at most $jN_iE_i/r$. Different-row representative pairs cost at most $243r+2.01w^2$, by the two-clique bound and the two sums for $N_i$ above. The arc-pair bound from the base manuscript is $4Q/3$. For the total count $P_*$ of distinct added edges this proves
$$
 \mathbb E P_*\le (4/3)Q+jT+2.01w^2+243r .                    \tag{7}
$$

## 5. The expected cut and the contradiction

The signed cut identity in §5 of the base manuscript gives, for rows tested independently of the repairs with probabilities $\pi_i$,
$$
 \sum\pi_iE_i\le\mathbb E P_*+r\mathbb E\binom H2+
              \tfrac12(B_\pi+u)^2+m/2 ,
$$
where $H=h+\#\{\text{tested rows}\}$, $B_\pi=\sum\pi_i d_i$. Take
$a=54/25,\ b=13/10,\ Y=13/50$ and $\pi_i=(a n_i+bN_i)/r$.
The pointwise bound from §4 gives
$\pi_i\le a(513\gamma/512+1/256+g\rho_0)+2bg\rho_0<1$.
Set $V=aM+9b/K$ and $B_0=((1+V)^2+V/K)/2$. Then
$\sum\pi_i\le Vs$, $\mathbb E\binom H2\le B_0s^2$, and
$B_\pi\le a\sqrt{\kappa Q}+2bw$.

For reproducibility, put $t=2b+\lambda,\ \chi=2.01,\ k=17/5$. The left side of the cut bound is $a(Q-Q_F)+bT$. Substitute (6), (7) and the bound on $Q_F$, and bound the resulting mixed term by
$$
 a(t+\chi)w\sqrt{\kappa Q}
 \le YQ+\frac{a^2(t+\chi)^2\kappa}{4Y}w^2 .
$$
The coefficients remaining on the left are $a-4/3-a^2\kappa/2-Y$ for $Q$ and $b-j$ for $T$. Multiplication by $k$ makes them at least $4/3$ and $j$ respectively. Adding the two direct terms of (7) gives
$$
 (4/3)Q+jT+\chi w^2+243r \le 55w^2+651s^2r .                 \tag{8}
$$
The two coefficient bounds used here are
$$
 \begin{aligned}
 k\big(\chi+t^2/2+a^2(t+\chi)^2\kappa/(4Y)\big)+\chi &<55,\\
 k\big(B_0+(10Ma+1/2)/K+243/K^2\big)+243/K^2 &<651 .
 \end{aligned}
$$
Let $\eta=1/(Rf^2)$. By (3), $s^2r\le\eta\rho^2r^2$ and $55\kappa^2+651\eta<33/100$. For a single tested row the last two terms of the signed cut estimate sharpen to $ud_i+u^2/2+m/2$, since no pair of rows is tested. Here $H=h+1=s$. Hence
$$
 \frac{E_i}{\rho^2r^2}
 \le 33/100+\lambda\kappa g+(\lambda\kappa)^2/2+
                 \eta(1/2+1/(2K))<3/8 .                       \tag{9}
$$

If $A>\Delta$, oversample using $z'=\min(A-\Delta,\Delta/128,r/16)$ and $p'=(\Delta+z')/A<2p$. The heavy counts and representative incidences scale linearly, $G$ is fixed, and therefore $Q'\le4Q,\ T'\le2T$. By (7)–(8), the expected repair cost is at most $4(33/100)\rho^2r^2$. The oversampling Turán floor from §5 of the base manuscript gives at least $rz'/2-rs^2$, using $h\le r/4$, $z'\le r/16$, and variance at most $sr$. It follows that $z'/r\le(8\cdot33/100+2\eta)\rho^2<(8/3)\rho^2$. This is below both $c/128$ and $1/16$, so $z'=A-\Delta$. Including $A\le\Delta$, we have $L\ge D-(8/3)\rho^2r$.

Assign each moderate sender in advance to a row of degree above $\rho r$. The count $V_i$ of its marked assignments there has mean $v_i$, variance at most $v_i$, and $\sum v_i\le m$. Since $\rho r v_i\le E_i$, (9) gives $v_i\le(3/8)\rho r$. Apply (4) to the $b_i'$ strong assignments and the $V_i$ marked moderate assignments in each row. On the left the strong senders supply $rL$, the marks supply $\rho r m$, and the moderate deficits supply $\sum d_i v_i$, in addition to the strong surplus $J_{d_i}$. On the right $\sum b_i'/2\le D$ absorbs the subtraction of $D$ from $(r-1)D$. Moving the deficits and surplus across and applying (5) with $v_0=v_i$ gives
$$
 rL+\rho r m\le rD+\lambda\sigma+\sum v_i^2+m .
$$
Indeed the variance and the linear moderate term cost at most $v_i$ per row. The moderate square contributes $v_i^2/2$ directly and (5) contributes at most another $v_i^2/2$.

Using $\sum v_i^2\le(3/8)\rho r m$, (6) and $m\le sr$, this would imply
$$
 (1-3/8)(c-\lambda\kappa\rho)
       \le\lambda\kappa+(8/3)\rho+1/(fRs^2).
$$
At $s=K$ the left side exceeds the right side by more than $1/10000$. For larger $s$ the left side increases and the right side decreases. This contradiction proves the theorem.

## What further reduction requires

The two aggregate inequalities (1) still permit a long tail. Set $y_i=0$ and $x_i=11/(80i)$ for $1\le i\le2^{44}$. These data satisfy (1) with $P/r=39/10$, since $\sum x_i\le(11/80)(1+44\log2)<4.4$. After omitting any $h\le2^{40}$ rows, the least possible squared tail comes from omitting the largest $x_i$. Integration gives
$$
 (h+1)\sum_{i=h+1}^{2^{44}}x_i^2
 \ge (11/80)^2\left(1-\frac{h+1}{2^{44}+1}\right)
 > (11/80)^2(14/15) > \beta^2 .
$$
Thus (1) alone cannot guarantee the squared-deficit bound in (3) at such a width. Whether actual colors admit these data is open here. The $r=19$ case and the conjecture for all $r\ge3$ remain open in this project. [Arithmetic checker](verify_cutoff_320.py) · [Research handoff](../README.md)
