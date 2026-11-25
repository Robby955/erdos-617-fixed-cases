# From the colored edges to one common threshold

Robert Sneiderman and OpenAI GPT‑6.2 Astra · 25 November 2026

The missing-color conjecture asks for a set of $r+1$ vertices that omits some color. Fix a color $J$. In a coloring with no such set, an independent set in the graph of $J$ has at most $r$ vertices. A clique in that graph also has at most $r$ vertices, since it misses every other color. This observation lets us use a single graph for both counts in Appendix A. [Coloring and clique bounds](ColoringLists.lean) · [Statement of the conjecture](CutoffStatement.lean)

## Why each chosen pair costs a missing representative

Suppose the two pruning stages have ended. Each surviving vertex has at most $\Delta=\lfloor199r/400\rfloor$ neighbors of color $J$ outside its row. Choose a largest family of pairs with all endpoints independent, using two vertices from each of $q$ different rows. Write $E$ for the $2q$ endpoints. In each unchosen row, keep every survivor with no neighbor in $E$ of color $J$. This gives a list of size $m_i$. Two nonadjacent vertices on the same list would extend the family, so each list is a clique. Empty rows count as lists of size zero. [Construction and maximality](PackingLists.lean)

Set $b=\lfloor399r/400\rfloor$. Truncate each list to $\min(b,m_i)$ real vertices. On their union $A$, keep just the edges of color $J$ between different rows. There is an independent set $R$ meeting each row at most once and satisfying $|A|\le b|R|$. Here $2\Delta\le b$. The manuscript uses the zero–one case of a weighted independent transversal theorem. The Lean file proves the required partial transversal bound directly. [Partial transversal proof](PartialTransversal.lean) · [Graf, Harris and Haxell, Theorem 7](https://arxiv.org/abs/1907.00033)

The representatives in $R$ remain independent in the original graph, since they lie in distinct rows. They also avoid every endpoint in $E$. Thus $2q+|R|\le r$. The $r-q$ unchosen rows have $b(r-q)$ slots, of which $|A|$ are filled. Subtracting gives

$$
 bq\le b(r-q)-|A|=\sum_i (b-m_i)_+,
 \qquad
 q\le W=\sum_{m_i<b}(1-m_i/b).
$$

Every unchosen row contributes to this calculation, including rows dropped by the later qualification test. The general bound can attain equality. At $r=4,b=2,\Delta=1$, take two isolated vertices as the chosen pair. Give the three remaining rows sizes $2,1,1$, join the two vertices of the size-two row and join the singleton vertices to each other. The independence number is four and $q=W=1$. This example tests the representative lemma with its own block size. [Proof of the inequality](PackingLists.lean)

### Why the representatives exist

Take a largest independent partial transversal and fix the set of rows it represents. Among transversals $R$ on exactly those rows, consider an auxiliary set $X\subseteq A$ and the neighborhoods $N(z)\cap R$ for $z\in X$. Call this collection minimal if every transversal that shrinks any one of these neighborhoods must enlarge another beyond its current set. Write $Y=\bigcup_{z\in X}(N(z)\cap R)$. Choose a minimal collection with $|X|\le |Y|$ and with $|X|$ as large as possible. The empty collection is a starting choice. [Exchange argument](PartialTransversal.lean) · [King’s neighborhood-minimization argument](https://arxiv.org/abs/0911.1741)

Every vertex lies in a row represented by $R\setminus Y$ or has a neighbor in $X\cup Y$. To see why, suppose $x$ escapes both. Among transversals preserving the neighborhoods of $X$, minimize the neighborhood of $x$ by inclusion. If it is empty, we can add $x$ in a new row or replace its row representative. In the latter case the old representative belongs to $Y$ and its removal strictly shrinks a previously minimal neighborhood. If the neighborhood of $x$ is nonempty, it supplies a new witness outside $Y$. Adjoining $x$ to $X$ preserves minimality and increases $|X|$, another contradiction. The asserted cover gives

$$
 |A|\le (|R|-|Y|)b+(|X|+|Y|)\Delta\le b|R|.
$$

This also handles a graph with no available vertices. [Finite proof](PartialTransversal.lean)

## The extra vertex and the deficit

Let $F$ count all unchosen lists shorter than $b$. An ordinary list is an unchosen list of size at least $b$ in a qualifying row. Let $D$ be the sum of $1-m_i/r$ on the ordinary lists. Each survivor lies in a chosen row, on an unchosen list, or next to a chosen endpoint in a different row. The last group has at most $2q\Delta$ vertices. A short list contributes at least $1/400+(399/400)(1-m_i/b)$ to its deficit. Count all $r^2+1$ original vertices, use $q\le W$, and divide by $r$. If $d$ vertices were deleted by pruning and $c$ survivors belong to chosen rows, the result is

$$
 D+\frac{F+q}{400}\ \le\ \frac d r+\left(\frac c r-q\right)-\frac1r.
$$

This is equation (2) with the favorable last term retained. The raw row-size and pruning budgets then give $F+q\le1411$. The incidence count sums actual edge ends on precisely these ordinary lists. A source charges an undirected edge only before its other endpoint disappears, which also gives $p/4+(199/400)t\le1$ for the two deletion rates. [Survivor count](ListDeficit.lean) · [Chosen-row and omission counts](ChosenRows.lean) · [Edge charges](PruningOverlap.lean)

## Where the raw rows come from

Choose a color with the fewest edges. In the graph of the other colors, choose a maximum-degree pivot among the vertices still present. Its neighbors remain for the next step and the other vertices form the current row. Every clique of remaining vertices extends by the pivot, so the clique cap drops by one at each step. Starting with the cap $r$ therefore constructs all the rows in at most $r$ steps. Pad the end with empty slots. At every step the pivot inequality bounds twice the number of internal nontarget edges by the number of target edges going from that row to later rows. Both the row labels and the per-row inequalities now follow from the original coloring. [Recursive partition](OrderedRows.lean) · [Choice of a sparsest color and its rows](RawColorRows.lean)

There is a second use of the actual edge labels. In a row of size $s>r$, choose one endpoint of each edge of a given color. Deleting those endpoints leaves a set missing that color and hence of size at most $r$. Each of the other $r-1$ colors must therefore supply at least $s-r$ edges. They occupy disjoint edge sets. Writing $\mu_i$ for the total nontarget count gives $\mu_i\ge(r-1)(s-r)$. For any chosen family of oversized rows, combine this floor with the pivot inequalities and sum. A forward edge has just one earlier endpoint, so the resulting charge is paid by actual distinct forward edges. This discharges the forward-count hypothesis used in the pruning overlap. [Counting the other colors](RawColorBudget.lean) · [Forward-edge identity and bound](RawColorRows.lean)

## What the combined theorem certifies

At $r\ge255\cdot2^{136}$, supply the ordered raw rows and a legal, stopped deletion history of the given coloring. The raw estimates specify the total positive row surplus, unused internal-edge allowance, inter-row edge cap, forward count on oversized rows, cost of each destination’s assigned sources and the qualification of each first-stage destination. The definitions compute these quantities from the coloring, row labels and deletion times. [Input hypotheses and theorem](PrunedWidth.lean)

Under those hypotheses, Lean gives either the original missing-color set or actual clique lists and one common threshold. On the retained rows it proves both individual bounds and the square-sum bound in (4), as well as $2^b s^4<255\cdot2^{136}\le r$, where $b$ in this last expression is the band exponent. The subsequent graph proof constructs the two-stage pruning history and verifies the raw estimates on a sparsest color, then carries (4) through the construction of the auxiliary cliques in §4. [Proof and remaining steps](coloring-to-exterior.md) The later proof establishes the strict shortage on this selection. The global signed cut in §5 remains to be formalized. [Exterior shortage](exterior-shortage.md) [Three conclusions on the retained rows](RowWidth.lean) · [Width proof](width-integral.md) · [Manuscript argument after the threshold](weighted-width.md#4-a-shortage-of-at-least-3r20)

The printed paper uses $2^{144}$. At the working cutoff the width scale in each band is multiplied by $(255/256)^{1/4}$. This uses $\tfrac14\log(256/255)<1/1020$ of each comparison’s margin. Each of the five margins exceeds that amount. The fourth power of the new scale, multiplied by $2^b$, is exactly $255\cdot2^{136}$. [Five reduced comparisons](RetainedWidth.lean)

## Replay

From the directory with the pinned Lake environment, run

```sh
lake env python3 -B proof/replay_pruning_kernels.py lists
```

The command compiles the source modules afresh, prints the axioms of the named results and replays a single export with Lean’s kernel, Lean4Lean and Nanoda. With the standard Lean toolchain alone, add `--lean-only` to compile and print the axioms. A full replay also requires `leanexport`, `leanchecker`, `lean4lean` and `nanoda_bin` on the Lake environment’s search path. [Replay script](replay_pruning_kernels.py)

On 25 November 2026 all three kernels accepted the same export of 25 named theorems. Lean4Lean checked 27,971 declarations including dependencies. The axiom audit found only `propext`, `Classical.choice` and `Quot.sound`. The export SHA-256 is `1e3ad3c29102cd939d9b82805ae835ddd1b928898aad7c23181b925e39fbf2e4`.
