# A cutoff of $2^{144}$ for Erdős 617

Robert Sneiderman research project · Private proof supplement · 24 November 2026

**Theorem.** For every integer $r\ge2^{144}$, every $r$-coloring of the edges of $K_{r^2+1}$ contains $r+1$ vertices missing a color.

This supplement strengthens the width estimate in the [preceding manuscript](weighted-width.md). All five bands, their sampling constants and the final signed-cut argument are inherited from that manuscript. A first-stage deletion spends part of the very budget used to count unqualified destinations. Keeping both uses in the same inequality allows more rows to contribute at the upper endpoint of the width integral. The combined argument awaits independent review. [Exact checker](verify_retained_width.py)

Lean proves that every feasible pair of real pruning parameters belongs to a band with width margin greater than $7/10000$. It also checks the reserved-row endpoint inequality. The derivation of the width integral and the extraction of rows from an arbitrary coloring are in the written proof. [Formal width comparisons](RetainedWidth.lean)

## 1. Count the destinations still available to omit

Retain the preceding notation. The raw parts $R_i$ have size $r+b_i$. Let $U_i$ be the number of their internal nontarget pairs minus $(r-1)b_i$. Then $U_i\ge0$, $\sum U_i\le r^2/2$, and $\sum(b_i)_+\le r/2$. A destination qualifies when $b_i\le r/256$ and $U_i\le r^2/1200$. In the first stage, exactly $pr$ vertices are deleted. Assign each to its recorded qualifying destination. At one such destination the preceding star count bounds the number of assigned sources by $U_i/((61/250)r)$. Summing only over qualifying destinations shows that they consume at least $(61/250)pr^2$ of the total $U_i$.

Consequently at most $600-(1464/5)p$ destinations fail the $U_i$ test. At most 128 fail the size test. With $n$ the combined number of short and chosen lists, the initial number $e_0$ of omitted slots satisfies
$$
 e_0+1\le729-(1464/5)p+n .
$$
Here $0\le p\le125/61$, $n\le1411$, $K=1120$, $K'=K+2n$. In the previous width argument set aside the $K'-e_0-1$ heaviest rows. Their number, divided by $K'$, is at least
$$
 \lambda_n=\frac{K\lambda+n}{K+2n},\qquad
 \lambda=\frac{391+(1464/5)p}{K}.
$$
In particular $0<\lambda<1$, $\lambda_n\ge\lambda-n/K$, and $\lambda_n\ge\min(\lambda,1/2)$.

## 2. Integrate the excess at the upper endpoint

In one of the five preceding bands let $b,\alpha,\beta$ be its constants. Set $S=2^{(144-b)/4}$, $\ell=\alpha/S$, and $H=\alpha/K'$. The checker verifies $S>8K'$ throughout. Retain the row weights $a_i$, the nonnegative coefficients $Q_i\le a_i^2/\alpha$ and the function $F(z)$ of Section 3 of the preceding proof. Assume $F(z)\ge1$ on $[\ell,H]$. Put $u=\max a_i/H$ over the rows still in the integral, with value zero for an empty family. The rows set aside contribute at least $\lambda_n u$ to the available budget, since each has weight at least $uH$ and costs at least $uH/\alpha$.

Write $A=\sum_iQ_i/H$ for the remaining rows. For $t\ge u$ and $t\le1$, the formula for the integral gives $F(tH)=t+A/t$. If $u\le1$, the integral of the remaining row terms above $H$, with respect to $dz/z$, is $A$. The integral below $\ell$ is at least one by the previous lower-endpoint argument. That unit pays exactly for the base term's integral on $[0,H]$. For any $h\in[\max(u,\ell/H),1]$ we can now count both the tail $A$ and the excess over one on $[hH,H]$. The additional saving, beyond the rows set aside, is at least
$$
 A+\int_h^1 (t+A/t-1)\frac{dt}{t}
     =1-h+A/h+\log h .                                           \tag{1}
$$
When $u>1$ the reserved rows alone still give $\lambda_n u$.

Write $Y,D$ for the sums of the normalized row incidence and deficit bounds before choosing the width. The original estimate (3) gives
$$
 Y/\alpha+D/\beta \le C-\gamma n,\quad
 C=Y_*/\alpha+(p+t_0)/\beta,\quad
 \gamma=\frac{1-2\tau-1/256}{2\beta},
$$
where $t_0r$ is the second-stage deletion count, $\tau=199/400$ and $Y_*=2-p/2-\tau t_0$. Switching from $\log(S/K')$ to $\log(S/K)$ uses at most $2n/K$. Thus every saving above is supplemented by at least $\epsilon n=(\gamma-2/K)n$, where $K\epsilon\ge3/5$ in every band.

We claim that failure throughout $[\ell,H]$ implies
$$
 \log(S/K)\le C-L(p),\qquad
 L(p)=\min\!\left(\lambda,\frac{4333+737p}{10000}\right).           \tag{2}
$$

* If $u\le1/8$, failure at $H/2$ requires $A\ge1/4$. With $h=1/8$, (1) exceeds $3/4$, which is larger than $L(p)$.
* If $1/8\le u\le1/2$, use $h=u$ and $A\ge1/4$. Since $K\epsilon\ge1/2$, the reserved rows and $\epsilon n$ contribute at least $\lambda u$. The total saving is at least $1-u+1/(4u)+\log u+\lambda u$. Its minimum on $(0,1/2]$ occurs at $u=1/(2(1+\sqrt\lambda))$, by differentiation, and equals
$$
 G(\lambda)=1+\sqrt\lambda-\log(2(1+\sqrt\lambda)).
$$
Its derivative in $\lambda$ is $1/(2(1+\sqrt\lambda))$, so $G$ is concave. Exact bounds at $p=0,125/61$ give $G(\lambda)>(4333+737p)/10000$ throughout.
* If $1/2\le u\le1$, failure at $uH$ gives $A\ge u(1-u)$. Using (1) and the reserved rows gives $2(1-u)+\log u+\lambda_n u+\epsilon n$, a concave function of $u$. At $1/2$ it agrees with the preceding lower bound before amortizing $n$. At 1 it equals $\lambda_n+\epsilon n$. The latter bound also applies when $u\ge1$.
* To check this last endpoint, for $\lambda\le1/2$ use $\lambda_n\ge\lambda$. Otherwise $\lambda_n\ge\max(1/2,\lambda-n/K)$, and minimizing these two affine bounds after adding $3n/(5K)$ gives $\lambda_n+\epsilon n\ge1/2+(3/5)(\lambda-1/2)$. This exceeds the affine term in (2) at both ends of the interval $1/2\le\lambda\le\lambda(125/61)$, and hence throughout.

## 3. The five comparisons

The pruning domain is $0\le p\le125/61$, $t_0\ge0$, $p/4+\tau t_0\le1$. Clip it by each of the five band intervals for $Y_*$. For each of the two affine terms in (2), $\log(S/K)-C+L$ with that term substituted for $L$ is affine on the clipped polygon. Testing all its vertices gives the following strict lower bounds for the minimum of the two comparisons.

| Band for $Y_*$ | $b$ | Certified margin exceeds |
| --- | ---: | ---: |
| 0 to 0.50 | 14 | 0.002030 |
| 0.50 to 0.55 | 14 | 0.001133 |
| 0.55 to 0.68 | 14 | 0.010032 |
| 0.68 to 1 | 15 | 0.130541 |
| 1 to 2 | 17 | 0.460849 |

Thus (2) fails in every band. Some width succeeds, giving precisely the normalized cut and deficit bounds (4) of the preceding proof with $K\le s<S$ and $2^b s^4<2^{144}\le r$. The shortage argument and the signed cut then apply. All 1,280 exact signed-cut endpoints exceed $0.0003327$ with their original parameters. The earlier first-band obstruction at $2^{145}$ applied to a coarser budget. The proof here covers the same boundary by accounting for the rows kept and the endpoint excess even at that boundary. $\square$

At exponent 143 the present sufficient comparison at $p=125/61,\ p/4+\tau t_0=1$ has margin below $-0.17125$ in the first band. Improving the constants, the saving in (2), or the feasible domain could change this comparison. Whether a coloring realizes that boundary is open. [Rational endpoint check](verify_retained_width.py)
