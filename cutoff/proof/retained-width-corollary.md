# A sharper cutoff within the final power-of-two interval

**Corollary.** For every integer $r\ge R_* = 255\cdot 2^{136}$, every $r$-coloring of the edges of $K_{r^2+1}$ has $r+1$ vertices whose induced edges miss a color.

For a band with exponent $b$, replace $S$ by $S'=S(255/256)^{1/4}$. Each band has $K'\le3942$ and $b\le17$. Hence $R_*>2^{17}(8\cdot3942)^4$, giving $S'>8K'$ as required in Section 2. Replacing the lower endpoint by $\ell'=\alpha/S'$ therefore preserves the endpoint argument. The five comparisons lose the same amount,
$$
 \log(S/K)-\log(S'/K)=\tfrac14\log(1+1/255)<1/1020.
$$
Each previous certified margin was greater than $1/1000$. In fact the original rational certificates give a remaining margin greater than $0.00015316$ in every band. The same successful-width argument now produces $K\le s<S'$, so $2^b s^4<2^b(S')^4=R_*\le r$. The signed cut uses that inequality together with the same normalized bounds and the same 1,280 endpoints. This proves the corollary under the preceding combinatorial argument in the [cutoff chapter](retained-width.md).

Lean verifies a uniform reduced margin above $1/10000$ for every feasible pair of real pruning parameters and the identity for the fourth power of $S'$. Since $R_*=(255/256)2^{144}$, the cutoff decreases by about 0.39 percent. The first power of two covered is $2^{144}$. [Lean width proof](RetainedWidth.lean) · [Rational replay](verify_retained_width.py)
