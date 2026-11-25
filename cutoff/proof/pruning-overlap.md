# Which edge ends are counted twice in Appendix A?

The two counts in Appendix A, §2 can overlap only at a deleted vertex of a chosen oversized row. Each such vertex contributes at most $r/4$ in the first pruning stage or $199r/400$ in the second. This proves the paper’s allowance and gives a smaller one whenever the first stage deletes a vertex in those rows. [Appendix A, §2](weighted-width.md#2-give-missing-representatives-to-the-short-lists) · [Lean proof](PruningOverlap.lean)

### Reconstructing the counts

Fix the original coloring, the target color, the ordered raw rows and a legal deletion history. Lean uses two properties of the history. Each deleted source has enough current edges for its quota, and each first-stage destination passes the raw row size test. The retained vertices can be any surviving subset outside the chosen rows. Write $X$ for the number of target edges between raw rows. An edge $\{x,y\}$ contributes two distinct incidences to $2X$, one at $x$ and one at $y$.

At the deletion of $x$, recover its star from the coloring. Use target edges to vertices still present in the recorded foreign row in stage one, and to vertices still present in any other row in stage two. Distribute the source’s quota evenly over these edges. The deletion rule requires more edges than the quota, so each edge receives at most one unit. An edge used when its first endpoint disappears is unavailable when its other endpoint disappears. These statements hold for every legal choice of source and destination.

Let $F$ contain the earlier-row end of each forward target edge out of a chosen oversized row. Write $Y_{\rm raw}$ for the number of incidences at ordinary retained vertices after excluding the recorded first-stage stars. The pruning charge at an end in $F$ has four possibilities.

| Role of that end | Charge that can also belong to $F$ |
|---|---|
| First-stage source | Its share of $r/4$ over the current star. |
| First-stage destination | Zero. Its row would have to be both qualifying and oversized. |
| Second-stage source | Its share of $199r/400$ over the current star. |
| Second-stage destination | Zero. Stage two charges only the source end. |

Every end counted by $Y_{\rm raw}$ lies outside $F$ because its row is unchosen. Its vertex survives both deletion stages. A first-stage charge arriving there belongs to a recorded edge, which $Y_{\rm raw}$ excludes. Thus adding $Y_{\rm raw}$, the pruning charge and $|F|$ can exceed $2X$ only by the pruning weight on $F$. With $f$ and $s$ the numbers of first- and second-stage deletions, and $\Omega$ that duplicated weight, this gives

$$
Y_{\rm raw}+\tfrac r2 f+\tfrac{199}{400}r s+|F|\ \le\ 2X+\Omega.
$$

The factor $r/2$ counts both ends of each first-stage payment. Let $E_1,E_2$ be the deleted sources in the chosen oversized rows in the two stages. Put $a=(|E_1|+|E_2|)/r$, $a_1=|E_1|/r$ and $\tau=199/400$. The table gives

$$
\Omega\le\tfrac r4|E_1|+\tau r|E_2|
       =\tau a r^2-\tfrac{99}{400}a_1 r^2.
$$

Using the separate graph estimates $X\le(1-v)r^2$ and $|F|\ge2(r-1)Or$ in the first display, then dividing by $r^2$, gives

$$
Y\le Y_*-2v-2(1-1/r)O+\tau a-\tfrac{99}{400}a_1,
\qquad Y_*=2-\tfrac{f}{2r}-\tau\tfrac{s}{r}.
$$

Lean's `overlap_pos_iff` identifies every positive duplicate. It is exactly the end at $x$ of an edge in $F$ whose other endpoint was in the deletion star of $x$. The declaration `incidence_budget` sums these charges. The normalized corollary takes the cross-edge upper bound and the forward-edge lower bound as explicit inputs. The overlap theorem itself needs neither input. The first-stage saving can vanish, so a lower cutoff would require further information about the coloring. [Graph inputs in Appendix A, §1](weighted-width.md#1-count-the-unused-part-of-the-stability-bound) · [Formal declarations](PruningOverlap.lean)

### A trace with positive overlap in both stages

Take four colors and 17 vertices. The rows in order are $\{0,\ldots,4\}$, $\{5,\ldots,8\}$, $\{9,\ldots,12\}$ and $\{13,\ldots,16\}$. Choose the first row. Give the other three rows target-colored internal edges. The only target edges crossing rows are $\{0,5\},\{0,6\},\{1,9\},\{1,13\},\{2,5\},\{5,14\},\{10,15\}$. Give all other cross edges any nontarget color.

Delete vertex 0 toward the second row in stage one. Delete vertices 5 and 1 in stage two. Keep the surviving vertices outside the first row. There are 14 original ends, five forward ends and five retained ends after the first-stage discount. The overlap is exactly $299/100$, against the paper’s allowance of $398/100$. In particular, the forward end at vertex 2 of $\{2,5\}$ receives zero pruning charge when vertex 5 is deleted. This example checks the distinction between the ends of the same edge. [Exact fractional replay](verify_weighted_width.py)
