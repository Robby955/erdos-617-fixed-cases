# A cutoff of $15\cdot 2^{140}$ for Erdős 617

Robert Sneiderman and OpenAI GPT-6.2 Astra · 27 November 2026 · Local research note

**Theorem.** Let $r\ge15\cdot2^{140}$ be an integer. In every $r$-coloring of the edges of $K_{r^2+1}$ there are $r+1$ vertices whose induced edges omit a color. This cutoff is $16/17$ of the cutoff in the [25 November release](https://github.com/Robby955/erdos-617-fixed-cases/releases/tag/cutoff-2026-11-25-v3).

## The five width comparisons

Use the ordered partition, pruning, and shortage estimate of the released proof. In the notation of its [cutoff chapter](retained-width.md), set $K=1120$, $\tau=199/400$, $Y_*=2-p/2-\tau t$, and $S=((15/16)2^{144-b})^{1/4}$. In place of the previous five bands use the following. Each interval starts at the previous right endpoint, with the first starting at zero. Both adjacent sets of constants work at a shared endpoint.

| Upper $Y_*$ | $b$ | $4000\alpha$ | $4000\beta$ | Width margin exceeds | Signed-cut margin exceeds |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0.501 | 14 | 656 | 925 | 0.0000741 | 0.0000298 |
| 0.55 | 14 | 656 | 923 | 0.0013549 | 0.0000352 |
| 0.65 | 14 | 653 | 918 | 0.0267077 | 0.0001997 |
| 1 | 15 | 652 | 916 | 0.0466079 | 0.0004340 |
| 2 | 17 | 654 | 918 | 0.4447146 | 0.0003327 |

The width margin is $\log(S/K)-Y_*/\alpha-(p+t)/\beta+L(p)$, where $L(p)$ is the minimum of the two affine savings in (2) of the cutoff chapter. Substitution of the new $S$ subtracts $\log(16/15)/4$ from the comparison at $2^{144}$. Each of the two affine expressions in the remaining variables attains its minimum at a vertex of the clipped pruning polygon. Testing both expressions gives the width column. The inequality $S>8(K+2\cdot1411)$ and the required reserved-row rebate hold in every band. The resulting integer width satisfies $K\le s<S$, hence $2^b s^4<15\cdot2^{140}\le r$.

The signed-cut column uses the 128 subintervals of normalized width in each band, testing both shortage endpoints. The other estimates use the new maximum $\beta=925/4000$. The Lean sources carry this bound through row selection, trimming, the two sampling passes and the contradiction for an arbitrary coloring. Lean uses its own nine-cell partition in each band. [Width comparisons](RetainedWidth.lean) · [45-cell certificate](CutoffCells.lean) · [Theorem from the coloring](BalancedColoringCutoff.lean) · [Rational replay](verify_fifteen_sixteenths.py)

## A limit on retuning these comparisons

**Proposition.** Keep $K=1120$, $f=9/40$, $c=3/20$, the released saving $L$ and the signed cut with its current coefficients. Allow any $0<\alpha\le656/4000$, $0<\beta\le1/4$, and any real $R>0$ (the scale written $2^b$ in the paper). At order $r\le2^{143+2/5}$, the width comparison at the following pruning corner and the signed-cut test at normalized width $1/2$ and shortage zero cannot both pass. This is an obstruction to those uniform sufficient tests. Realization of the corner and half-width by a coloring is not assumed.

Take $p=125/61$, $y=1-p/4=119/244$, $t=y/\tau$, so that $p/4+\tau t=1$ and $Y_*=y$. The width test requires
$$
\log r>\log R+4\log K+4\bigl(y/\alpha+(p+t)/\beta-L(p)\bigr).
$$
At half-width the exact envelopes have $A=\alpha/2$, $X=\beta$, $\kappa=\beta^2/f$. The load cap gives $a=5/2$ throughout the stated rectangle, since even its largest denominator is smaller than $(249/250)/(5/2)$. Put $k=8/7$, $b_0=(3/4)a(1+100f/K)$ and $M=k(1+a y/f)^2/(2f^2)$. In the notation of the [signed-cut calculation](verify_weighted_width.py), its coefficient $b$ is at least $b_0$, $W\ge\kappa$, $V\ge ay/f$ and $\eta=1/(Rf^2)$. These inequalities also hold for any band upper endpoint greater than $y$. At shortage zero, discarding nonnegative terms gives
$$
\epsilon\ge E_0(\kappa)+M/R,\qquad
E_0(\kappa)= k(b_0\kappa)^2/(2-a\kappa).
$$
Both $\epsilon<1$ and a positive signed margin are necessary for this test. The signed margin is at most $c(1-\epsilon)-(501/1000)\kappa$. Thus the quantity $d=c-(501/1000)\kappa-cE_0(\kappa)$ must be positive, and $R>cM/d$.

On $0\le\beta\le1/4$, $2-a\kappa>0$ and $E_0$ increases with $\kappa$. For a closed interval of $\beta$, its lower endpoint therefore supplies an upper bound on $d$. If this is positive it gives a lower bound on $R$. The upper endpoint gives a lower bound on $(p+t)/\beta$, and $y/\alpha\ge y/(656/4000)$. The interval $[0,1/5]$ and the 500 successive intervals of length $1/10000$ through $1/4$ cover the domain. On 151 intervals the bound on $d$ is nonpositive. On the other 350, the lower bound on $\log r$ exceeds $(143+2/5)\log2$ by more than $0.01738$. The checker uses rational enclosures of the logarithms. [Interval proof](verify_retuning_obstruction.py)

At the revised first-band parameters themselves, the width margin at $2^{143}$ is below $-0.1570780$. To reach that order, one possible improvement is to rule out a neighborhood of the pruning corner using the colors of the recorded edges. Another is to strengthen the signed-cut estimate where the width is near $1/2$.

## Reproduction

From the checkout's `cutoff` directory, run

```sh
python3 -B proof/verify_fifteen_sixteenths.py
python3 -B proof/verify_retuning_obstruction.py
lake env python3 -B proof/replay_pruning_kernels.py cutoff
```

The separate retuning obstruction has a written proof and a rational Python certificate. Its interval enumeration is outside the Lean cutoff theorem.
