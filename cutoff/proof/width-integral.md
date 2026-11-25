# One threshold for the three row bounds

Robert Sneiderman and OpenAI GPT‑6.2 Astra · 25 November 2026

Appendix A, §3 needs one choice of rows for three different estimates. The Lean theorem starts with a finite family of ordinary rows, the raw parts’ individual pruning charges, the deficit count from (2) after the chosen parts are bounded by $O-a+q/256$, and the corrected incidence count. It returns a threshold, the retained rows, an integer $s$ and a weight $w$. Every retained row satisfies the incidence and deficit bounds, and the sum of their squared deficits satisfies the third bound. It also proves that exactly $s-1$ slots were omitted and that $2^b s^4$ lies below the cutoff. [Statement at the paper’s cutoff](CommonWidth.lean) · [The three inequalities](RowWidth.lean) · [Manuscript, equation (4)](weighted-width.md#3-endpoint-bounds-for-the-width-integral)

## How many rows can be omitted?

In the raw partition, the normalized positive size surpluses sum to at most $1/2$. Each part failing the size test spends more than $1/256$, so there are at most 128. The unused incidence budgets $U_i$ also sum to at most $1/2$. If a part fails the $U_i$ test it spends more than $1/1200$ and receives no first-stage sources. The other parts must pay at least $61/250$ per unit of assigned first-stage load. If the total load is $p$, the number failing the second test is at most $600-(1464/5)p$. Taking the union and adding the $n$ chosen or short rows gives $e_0+1\le729-(1464/5)p+n$. The formal theorem derives this bound before reserving any additional rows. [Individual row charges](RowWidth.lean)

## Where the common threshold comes from

Write $m=1120+2n$, $H=\alpha/m$, and measure the test level $z$ by $t=z/H$. A row with incidence $y_i$ and deficit $x_i$ has normalized breakpoint and square coefficient

$$
 a_i=m\max\!\left(\frac{y_i}{\alpha},\frac{x_i}{2\beta}\right),
 \qquad q_i=m\left(\frac{x_i}{2\beta}\right)^2.
$$

The proof sets aside the $m-e_0-1$ heaviest rows. In the remaining family a row contributes $f_i(t)=t/m$ when $t<a_i$, and $f_i(t)=q_i/t$ when $a_i\le t$. This choice keeps a row whose breakpoint equals the threshold. The test succeeds at $t$ if $t+\sum_i f_i(t)<1$.

To see why some test must succeed, consider the remaining integral of one row above $t>0$,

$$
 P_i(t)=\frac{\max(a_i,t)-t}{m}+\frac{q_i}{\max(a_i,t)}.
$$

This function is continuous even at the breakpoint and has right derivative $-f_i(t)/t$. The row budget pays for $P_i(t)+f_i(t)$, including when $a_i=q_i=0$. If every test fails between $\ell=m/S$ and $h$, the function $t-\log t-\sum_iP_i(t)$ has nonnegative right derivative throughout that interval. Comparing its values at the two ends, and using the failed test at $\ell$, gives

$$
 -\log\ell\ \le\
 \sum_i\left(\frac{a_i}{m}+\frac{q_i}{a_i}\right)
 -\left(1-h+\sum_i P_i(h)+\log h\right).
$$

The summand for a zero-weight row is zero. This proof evaluates the width integral without interchanging a limit and a finite sum. [Right-derivative proof](WidthIntegral.lean)

Let $u$ be the largest remaining breakpoint. For $h\ge u$ the sum of the remaining integrals is exactly $\sum_i q_i/h$. In the middle range $1/8\le u\le1/2$, failure at $1/2$ forces $\sum_iq_i\ge1/4$. The resulting lower bound on the saving is affine in the pruning parameter $p$ at each fixed $u$. Lean verifies the two endpoints of the allowed $p$ interval using rational lower bounds for the square roots and eight terms of the exponential series. It interpolates between them at that same $u$. The other ranges use failure at $u$ or $1/2$, the concavity of the logarithm, and the cost of the reserved rows. In each band the saving contradicts the width comparison. [Endpoint estimates](WidthEndpoint.lean) · [Five comparisons](RetainedWidth.lean)

At the successful level let $s=m+\#\{i:a_i>t\}$ and $w=st/m$. The two individual bounds follow directly from $a_i\le t$ on the retained rows. The remaining term of the same successful test is $\sum_{a_i\le t}q_i/t<1-w$. Multiplying by $4\beta^2st/m$ gives the square-sum bound. The smaller scale in the working supplement gives the same three inequalities and $2^bs^4<255\cdot2^{136}$. [Selection in the original units](RowWidth.lean) · [Both cutoff theorems](CommonWidth.lean)

## What the coloring still has to supply

The row theorem takes a pruning domain, a row count and two aggregate counts. A subsequent formalization constructs the ordinary lists from the original coloring and a stopped pruning history. It proves $q\le W$, equation (2) and the bound of 1,411 on short and chosen rows, then applies the integral to the actual lists. The subsequent graph proof constructs the two-stage pruning history and verifies the raw estimates on a sparsest color, then carries (4) through the construction of the auxiliary cliques in §4. [Actual auxiliary cliques](coloring-to-exterior.md) · [Strict shortage and the remaining signed cut](exterior-shortage.md)

From the cutoff directory, run this command to compile the component and check the same exported proof with Lean’s kernel, Lean4Lean and Nanoda. The script also prints the axioms of the named declarations and the SHA‑256 digest of the export. Add `--lean-only` to compile the sources and print their axioms without the independent replays.

```sh
lake env python3 -B proof/replay_pruning_kernels.py width
```

On 25 November 2026 all three kernels accepted the same export of ten named width theorems. Lean4Lean checked 27,291 declarations including dependencies. The ten theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. The export SHA-256 is `38342d706135834108928b8166d7b97134d98cf09982a67fe205d09bffcc26b8`.
