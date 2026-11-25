# Off-grid edges and competing color demands in Erdős 617

Robert Sneiderman research project · Private proof supplement · 22 November 2026

Let $r\ge3$. Call a coloring **balanced** if every set of $r+1$ vertices sees all $r$ colors. Delete $z$ from a coloring on $r^2+1$ vertices and arrange the remaining set $Q$ in an $r\times r$ grid. An edge is **off-grid** if its endpoints differ in both coordinates. Each hue $a$ may use its own grid, with $E_a$ off-grid edges of that hue. A hue **demands** $zx$ if some $(r+1)$-set through $z,x$ has no other edge of that hue. Two demands of distinct hues on one edge prove the conjectured conclusion. [Erdős and Gyárfás, Conjecture 1](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf)

* For every prime power $r\ge11$, there is a balanced old square with an extension whose **unique sparsest hue** has independence number $r$. Even removing any one of its edges increases that number. Over all deletions of degree at most $r$ in this hue and all grids, the exact minimum off-grid count is $(k-1)(r-3)$, where $k$ is the largest odd integer at most $r/2$. The other $r-1$ hues demand every edge at the added vertex.
* In any hypothetical balanced extension, for every hue at or below the mean and every deletion of degree at most $r$ in it, every grid has at least $\max(r-1,2r-7)$ off-grid edges of that hue for $r\ge5$. For a deletion of degree at most $r-1$, the bound also includes $3r-12$.
* For every $r\ge3$, if a balanced old square admits a grid with **at most $r-2$ off-grid edges per hue**, every new star forces an actual double demand. Section 3 gives a separate test when the exceptions are much larger or concentrated in particular hues. For $r\ge17$, just **two** hues with at most $r-4$ exceptions apiece already suffice for the missing-color conclusion.

The first construction tests what can be inferred from the sparsest hue and a balanced old square. The full conjecture requires control of the other hues in an arbitrary coloring.

## 1. The exact minimum in an edge-critical example

Use the affine plane over the field of order $r$, with the horizontal direction designated hue $a$. Any odd $5\le k\le r/2$ works. Color the nonvertical old pairs by their finite slope, one hue per slope. Each hue contains a partition into $r$ monochromatic lines, so all old $(r+1)$-sets see all hues. Write $B(s)=\binom s2$.

Select $k$ horizontal rows in a cyclic order and two columns. In each of those columns give hue $a$ to the edges joining cyclically consecutive selected rows. Distribute the other vertical edges as evenly as possible among the other $r-1$ hues. Add one vertex $v$. Its $a$-neighbors are precisely the $D=k(r-2)$ points in the selected rows outside the two columns. Distribute its other edges as evenly as possible among the other hues.

Each hue starts with $rB(r)$ edges. Hue $a$ gains $2k+D=kr$. The other hues share $rB(r)+r^2-kr$ additional edges, each within two of their average. This average exceeds $kr$ by $r^2((r+1)/2-k)/(r-1)>2$. Thus $a$ is uniquely sparsest. Since $D\ge3r-2$, every other hue has star degree at most $r-2$.

An $a$-independent set of $r+1$ points would use $v$ and exactly one point in each horizontal row. In the selected rows it would have to choose one of the two designated columns. Consecutive rows must choose opposite columns, which would two-color an odd cycle. An old transversal in a third column gives independence exactly $r$. No hue has a clique of size $r+1$. For $a$, any old $r$-clique must lie in a horizontal row because the only vertical target graphs are cycles. The star misses points in every row. Each other hue lies in the rows and columns of its own old grid and has fewer than $r$ neighbors at $v$.

Every $a$-edge is essential to its independence bound. The following sets have $r+1$ vertices and contain only the named edge in hue $a$.

* For a horizontal pair, take both ends and one point in a third column in every other row.
* For a designated cycle edge, take $v$ and one representative per row. Assign the two columns around the odd cycle so its sole equal adjacent pair is the specified edge in its specified column. Use a third column in the unselected rows.
* For $vx$ of hue $a$, take $v,x$, alternate the two columns along the path of remaining selected rows, and use a third column in every unselected row.

**Optimizing the deletion and the grid.** The eligible deleted vertex $y$ is either a marked point of a selected row or a point of an unselected row. The two special points in every selected row have degree $r+1$, and $v$ has degree $D>r$. In every grid after deleting $y$, at least $D-1-2(r-1)$ edges at $v$ are off-grid.

A set of $s\ge3$ cells occupying more than one row and more than one column has at least $s-2$ off-grid pairs. If its longest line has length $2\le m<s$, each of its other $s-m$ points misses at least $m-1$ members of the line in both coordinates. The product is at least $s-2$. If $m=1$, every pair is off-grid. Thus if any of the original horizontal rows fails to lie on one grid line after deletion, it contributes at least $r-3$ additional off-grid edges, disjoint from those at $v$. The total is at least $D-r-2\ge D-r-k+3$.

Otherwise the $r-1$ intact rows fill parallel lines, since two perpendicular full lines intersect. The old row with one point deleted and $v$ occupy the last line. If $y$ came from a selected row, $v$ has at most $r-3$ neighbors on that line and $k-1$ on its perpendicular line, from a remaining degree of $D-1$. If $y$ came from an unselected row, $v$ has at most $k$ on-grid neighbors. This gives $E_a\ge D-r-k+3$ in either case. Equality is attained by putting $v$ in the original position of any deleted marked point. All surviving old target edges stay on-grid, and the star attains both of its line bounds. The exact minimum is therefore
$$
                          D-r-k+3=(k-1)(r-3).
$$

Yet the other $r-1$ hues all demand each edge $vx$. For any such hue, use its finite-slope lines as rows and the vertical lines as columns. A permutation through $x$ makes one choice in each other row and column. It has at most $(r-2)/(r-1)<1$ other star marks in expectation. Some permutation has none, and its cells contain no old edge of that hue. For $r=11$ the best eligible grid has 32 off-grid edges, while ten hues demand each edge at $v$.

The distinction between target balance and full balance is visible on each selected row. The vertex $v$ sends $r-2$ target edges to a full old target clique. A balanced extension can send at most one, since all $r-1$ nontarget labels must occur on the $r$ edges into that clique.

**Quadratic is the correct worst-case order under the old-square hypothesis.** On any balanced old square, write $\eta_a=e_a(Q)-rB(r)$. There is a grid with $E_a\le3\eta_a$. To see this, apply Füredi's stability theorem to the complement of the hue. It gives $r$ parts, padded with empty parts if necessary, with at most $\mu\le\eta_a$ nontarget pairs inside. Write their sizes $r+b_i$ and $O=\sum(b_i)_+$. Each part larger than $r$ needs at least $b_i$ edges in each other hue, since deleting one end per edge leaves at most $r$ points. Hence $(r-1)O\le\mu$. The number of target cross edges is $\eta_a+\mu-\sum b_i^2/2$. Move $O$ vertices from oversized parts into undersized parts to obtain equal rows. Losing the target edges of every pair removed from the original part interiors would add at most $rO+\sum_{b_i>0}(b_i^2-b_i)/2$ cross edges. Since $\sum_{b_i<0}b_i^2\ge O$, the final cross count is at most $\eta_a+\mu+(r-1)O\le3\eta_a$. Any column assignment works. [Füredi's stability theorem](https://arxiv.org/abs/1501.03129)

If the added vertex has target degree $D$, deleting any old point and putting the added vertex in its place costs at most $D$ additional edges. For a hue at or below the full mean, $\eta_a+D\le r(r+1)/2$. Thus $3\eta_a+D\le3r(r+1)/2$ bounds the best grid after *any* deletion, including every eligible one. The edge-critical family has minimum $(1/2+o(1))r^2$ along prime powers. The order $r^2$ upper and lower bounds concern the relaxed hypotheses and do not assert that a balanced extension exists.

## 2. What a hypothetical counterexample requires of one grid

We give the packing facts used in the count. In a balanced coloring, each vertex outside a monochromatic $K_r$ has at most one neighbor of its hue in the clique. On their union all the other $r-1$ hues must occur.

**No hue has $r$ disjoint full cliques.** Otherwise remove the neighbors of the remaining vertex from each clique. The $r$ resulting lists each have size at least $r-1$, and their mutual cuts are matchings in the target hue. If a list has size $r$, fill it last and choose independent representatives greedily. If some point in one list has no neighbor in a second list, choose it first and fill the second last. Both procedures would extend the remaining vertex to an independent $(r+1)$-set. Thus all lists have size $r-1$ and all mutual cuts are perfect matchings. Two representatives matched to the same point in a third list must themselves be matched. Otherwise choose them first and fill that third list last. Consequently the matchings align in $r-1$ transversal $K_r$'s.

On the $r(r-1)$ list points there are exactly $r B(r-1)+(r-1)B(r)$ target edges. Each other hue needs at least $rB(r-1)$ edges by complementary Turán. These floors sum to the remaining capacity, so each such hue is the disjoint union of $r$ cliques of size $r-1$, with no edges of its hue between them. Each of the $r+1$ exterior points must completely join one clique in that hue, or one nonneighbor in every clique extends the point. Two exterior points completely join the same clique. Their union with it has $r+1$ points and only their mutual edge can supply the other $r-1$ hues. This is impossible.

**A hue at or below the mean has at most $r-3$ disjoint full cliques for $r\ge5$.** Here are the details from the earlier packing argument. If an independent $r$-set $A$ avoids a full clique $C$, their cut is a perfect matching. Every point $x$ among the remaining $(r-1)^2$ points has a neighbor in $A$. If it has just one, replace that neighbor by $x$. The same perfect-matching argument shows $x$ then has a neighbor also in $C$. Writing $p_s(n)$ for the complementary Turán floor at independence cap $s$, the total edge count of the hue is at least
$$
                  B(r)+r+2(r-1)^2+p_r((r-1)^2)=r(r^2+1)/2 .
$$
Equality is compulsory at or below the mean. The remaining graph attains its floor, so trimming its one larger clique leaves an induced union of $r$ disjoint $(r-2)$-cliques. Each exterior point must completely join one of them. There are $2r+1$ exterior points and three must join the same clique. Only their three mutual pairs can supply $r-1\ge4$ other hues. Hence deleting a full clique lowers the independence cap to $r-1$. Each subsequent full-clique deletion lowers the cap by at least one, because a target-independent set of size $h<r$ outside the next clique forbids at most $h$ points there. A maximal packing of $r-2$ cliques would leave $2r+1$ points of independence at most two and no target $K_r$. The nontarget graph on these points is triangle-free and has maximum degree at most $r-1$, since each neighborhood is a target clique. Its edge count is at most $(2r+1)(r-1)/2$, whereas every one of its $r-1$ hues needs $p_r(2r+1)=r+2$ edges. A packing of $r-1$ or $r$ already contradicts the residual independence cap or the clique cap. This proves the assertion.

Fix a hue $a$ at or below the mean, a deleted vertex $z$ with degree $d\le r$ in that hue, and one grid. Its $d$ neighbors are marks. Every permutation of the board must contain a mark or an off-grid $a$-edge, or it extends $z$. Write $E=E_a$, let $m$ be the greatest number of marks on a line, and let $M$ count pairs of marks in different rows and columns. A fixed mark belongs to a proportion $1/r$ of the permutations, an off-grid edge to $1/[r(r-1)]$. Bonferroni's inequality through triples gives
$$
 E\ge (r-d)(r-1)+\left(1-\frac{d-2}{3(r-2)}\right)M,\qquad
 2M\ge d(d-2m+1).
 \tag{1}
$$
Each nonattacking pair of marks extends to at most $d-2$ triples; each triple uses three pairs. The second inequality counts that any mark shares a coordinate with at most $2(m-1)$ others. Orient a longest line as a row. In any of its $t=r-m$ unmarked positions, the other $u=d-m$ marks each exclude at most $(r-2)!$ permutations through that position. Dividing the number still to be blocked by $(r-2)!$ gives $E\ge t(r-1-u)$.

Two more counts use actual missing pairs in the rows. For a hole $x$ on the longest line, take permutations through it. For a missing target pair in a different, entirely unmarked row, take both ends and match the $r-2$ other rows outside the longest line to the $r-2$ unused columns. In either case let $l$ denote the size of the free permutation, $r-1$ or $r-2$ respectively. Let $w$ count distinct eligible free cells with an off-grid target neighbor among the fixed points. The other free cells are in distinct coordinates from the fixed points. The expected obstruction count gives
$$
                 l-u\ \le\ w+(E-w)/(l-1).                    \tag{2}
$$
There are at most $u$ other marks to avoid. At least $w$ distinct target edges from fixed points cannot also be internal to the free permutation. In the pair case the two fixed points miss the target by definition. Success would give $r$ old independent points avoiding the marks.

For holes on the same line the incident edges counted by $w$ are disjoint. They are also disjoint from those counted at a different row's fixed pair, whose free board excludes the longest line. For fixed pairs in two different rows, $w_1+w_2\le E+2$. Only edges between the two pairs could be counted twice. If $j$ such edges occur, their contributions count at most $j+2$ distinct endpoints across the two counts. With just one fixed pair and one hole, $w_1+w_2\le E$.

If $d\le r-2$, (1) gives $E\ge2(r-1)$. For $d=r-1,r$ and $m\le2$, (1) gives at least $(r-1)^2/3$ and $r(r-3)/3$, respectively. Both imply the claimed integer bound. For $3\le m\le r-2$, $E\ge(r-m)(m-1)\ge2(r-3)$.

If $m=r$, at least two other rows have a missing target pair by the packing bound. Apply (2) in both, with $l=r-2$, $u=0$, and $w_1+w_2\le E+2$. This gives $E\ge2r-8+4/(r-2)$. If $m=r-1$, use the hole and one missing pair in an entirely unmarked row. Such a row exists since at most one other row has a mark. Now $u\le1$, and replacing both denominators in (2) by $r-3$ gives $2r-5\le(1+1/(r-3))E$. Thus $E\ge2r-7+1/(r-2)$. Integrality proves $E\ge\max(r-1,2r-7)$ in all cases.

**Choosing a vertex of degree below $r$.** Such a vertex always exists in this hue. Otherwise the mean-degree bound makes the graph $r$-regular. Brooks' theorem gives an $r$-coloring, since there is no $K_{r+1}$ and $r\ge3$. One independent class then has at least $r+1$ vertices. [Brooks' theorem](https://doi.org/10.1017/S030500410002168X)

For $d\le r-1$, (1) gives $E\ge3(r-1)$ if $d\le r-3$. At $d=r-1,r-2$ and $m\le2$, the respective lower bounds $(r-1)^2/3,(r^2-r+4)/3$ both exceed $3r-12$. When $m,t\ge3$, use $E\ge t(r-1-u)\ge t(r-t)\ge3(r-3)$. The remaining possibilities are $t=1,2$. With one hole, $u=0$ and there are at least two defective unmarked rows. Sum (2) for the hole and one pair in each of two such rows, using $\sum w\le E+2$. This gives $E\ge3r-13+10/(r-1)$. With two holes there is at most one mark outside their line. Use both holes and one defective unmarked row with $\sum w\le E$. This gives $E\ge3r-13+8/(r-1)$. Rounding gives $E\ge3r-12$.

## 3. How the other hues force an edge

Take any colored old square $Q$ and any star at $z$. Write $S_a=N_a(z)$, $d_a=|S_a|$, and $F_a=\{x:a\text{ demands }zx\}$. In the grid chosen for $a$, call a permutation **clean** if it avoids the marks $S_a$ and contains no $a$-edge. Let $K$ be the set of hues with at least one clean permutation. It suffices that $\sum_a|F_a|>r^2$.

If $a\in K$, relabel a clean permutation as the diagonal. Each diagonal point is demanded. Swap the columns of each pair of diagonal points in turn. In the absence of a target edge, the two new cells give two demands if neither is marked, and one demand if just one is marked. Each off-diagonal cell occurs in exactly one such swap. Each off-grid target edge spoils at most one swap, since the diagonal is independent and any off-diagonal endpoint specifies the swap. Hence
$$
                         |F_a|\ge r^2-d_a-2E_a .
$$
If $b\notin K$, a uniform permutation that contains no $b$-edge has at least one mark. If it has exactly one, that mark is demanded. The probability to contain a $b$-edge is at most $E_b/[r(r-1)]$; the probability of a unique mark on an edge-free permutation is at most $|F_b\cap S_b|/r$. Comparing with the expectation $d_b/r$ for the number of marks gives $|F_b\cap S_b|\ge 2r-d_b-\lfloor2E_b/(r-1)\rfloor$. Summing the two estimates and using $\sum d_a=r^2$ proves that a collision occurs whenever
$$
             2\sum_{a\in K}E_a+
             \sum_{b\notin K}\left\lfloor 2E_b/(r-1)\right\rfloor
                    < |K|\,r(r-2).                              \tag{3}
$$
In particular, if each $E_a<r(r-2)/4$, just one clean permutation suffices. The equation uses an independently chosen grid for each hue.

**The unconditional star under the per-hue budget.** Assume $Q$ balanced and each $E_a\le r-2$. For $r\ge4$ and $K\ne\varnothing$, the margin in (3) is at least $|K|(r^2-4r+5)-r>0$. For $r=3$, there are only 512 sets of marks and 19 choices of at most one off-grid edge on a given board. For each board form the union of the cells of all clean permutations and the unique marks of the other edge-free permutations with exactly one mark. Exhausting these boards and taking three mark counts summing to nine gives a minimum total of ten demanded cells, counted across hues, whenever at least one hue has a clean permutation. The accompanying checker reproduces this finite calculation.

Finally suppose $K$ is empty. For each hue the union bound $1\le d_a/r+E_a/[r(r-1)]$ gives $d_a\ge r$, so all $d_a=r$. Remove one mark $x$ in a hue. The same union bound is now strictly below one. A permutation avoids the remaining marks and the target edges. It must pass through $x$, because the original marks and edges met every permutation. Thus every star edge is demanded by its own hue. If a set through $z$ misses a hue, each of its star edges also demands that missing hue and there is a collision. In the only remaining alternative the whole extension is balanced. At $r\ge5$ this contradicts Section 2 applied to a sparsest hue, since its star has degree $r$ and $E_a\le r-2$. At orders three and four the balanced extension is excluded by the original theorem. [Erdős and Gyárfás, Lemmas 1 and 2](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf)

**A balanced square that genuinely needs an exception.** For any prime power $r\ge3$, color nonvertical pairs by finite slope, except for one horizontal pair $pq$ in row zero in columns zero and one. Give $pq$ slope-one hue $b$ instead of horizontal hue $c$. In those two columns color vertical pairs touching row zero $c$, and the other pairs $b$. In the other columns color vertical pairs touching row zero $b$, and the other pairs $c$.

All finite slopes other than $c$ still have full parallel lines. Any $(r+1)$-set avoiding $c$ must contain $p,q$, since some horizontal row is repeated. Some column must also repeat. A non-$c$ pair in column zero or one would be joined in $c$ to $p$ or $q$ there. In any other column a non-$c$ vertical pair uses a third point of row zero, again giving $c$. Thus the square is balanced.

Hue $b$ has exactly one off-grid edge in its natural grid of slope-one lines and vertical lines. In any exact $b$-grid the $r$ full slope-one lines would be parallel grid lines. Every natural column other than zero and one has a spanning $b$-star joining distinct slope-one lines, forcing it to a single perpendicular grid line. On each exceptional column the $r-1$ points off row zero form a $b$-clique, forcing each group to one of the two remaining perpendicular lines. The groups overlap in their slope-one line indices, so these perpendicular lines are distinct. The remaining positions of $p,q$ are now forced, since their slope-one lines are different. They differ in both grid coordinates, contradicting the edge $pq$. Thus the minimum for $b$ is one. Every other hue has an exact grid, so the new collision theorem applies at all these orders.

**A test at a vertex of large degree.** The target hue need not have a grid with a small error count. Suppose $d_a=D$ at $z$. If no two hues demand its same edge, any choice of grids for the other hues must satisfy
$$
      \sum_{b\ne a} E_b\ \ge\
        \frac{(r-2)r^2}{r^2+4(r-2)}\,(D-3r+2)_+ .                \tag{4}
$$
Indeed, for $x\notin F_b$, every permutation through $x$ has another mark or a target edge. Conditioning on $x$ shows $r-1-d_b\le e_b^\times(x)+E_b/(r-2)$, where $e_b^\times(x)$ counts its incident off-grid $b$-edges. If $|F_b|\le r^2/2$, averaging over the at least $r^2/2$ excluded points gives $r-1-d_b\le(4/r^2+1/(r-2))E_b$. At most one hue can demand more than half the square without a collision. The sum of $r-1-d_b$ over $b\ne a$ equals $D-2r+1$. Omitting the exceptional hue costs at most $r-1$, proving (4). A vertex with $D$ of order $r^2$ therefore forces a total of order $r^3$ off-grid edges in the other hues if it avoids a conflict.

In a balanced old square the bound $E_b\le3\eta_b$ converts this into a test that does not require finding any grid. For example, two distinct hues each satisfying $3\eta_b(4/r^2+1/(r-2))<r-1-d_b$ force a collision at $z$. Another necessary inequality for avoiding a collision is
$$
     \frac{(r-2)r^2}{r^2+4(r-2)}(D-3r+2)_+
          \ \le\ 3\bigl(rB(r)-\eta_a\bigr),
$$
since $\sum_b\eta_b=rB(r)$. Both tests use the actual old edge counts and the degrees at the specified vertex.

## 4. Two colors and a test without grids

**Two approximate grids suffice for the conjectured witness when $r\ge17$.** Suppose two hues on the same old square each have a grid with $E\le r-4$; each grid is its own. If the entire coloring were balanced, no hue would have a partition of the old points into full cliques, by Section 2. Thus in either grid some horizontal pair and some vertical pair miss its hue.

Fix one such horizontal pair $u,v$. In any of the $r-2$ other columns exclude their row and all off-grid neighbors of $u,v$ in the hue. Two remaining points in this column must form a target edge. Otherwise the four anchors are independent, and choose a permutation on the other $r-3$ rows and columns. Each off-grid edge that could cause a conflict with these choices occurs with probability at most $1/(r-3)$, since no edge joins two anchors. With $E\le r-4$ some completion is independent, giving $r+1$ old points. Across the columns at most $E$ extra cells were excluded, each costing at most $r-2$ vertical pairs. Repeat with a vertical missing pair.

If we can choose a horizontal and a vertical missing pair with disjoint endpoints, the two exclusion counts combined are also at most $E+2$. Only edges between the two pairs can be charged on both sides; their counted endpoints exceed their number by at most two. If every horizontal missing pair meets every vertical missing pair, fix one of each. All missing vertical pairs then touch one of the two horizontal endpoints, so at most $2(r-1)$ vertical pairs are missing. The same bound holds horizontally. This gives at least $2rB(r)-4(r-1)$ on-grid edges, already greater than $(r-1)(r-2)^2$ for $r\ge5$. In both cases we obtain the lower bound
$$
             e_a(Q)\ge (r-1)(r-2)^2-(r-2)\min(2E,E+2)+E .
$$
The last term is the disjoint count of the off-grid target edges themselves.

For every remaining hue, Brouwer's refinement of Turán gives $e_b(Q)\ge rB(r)+r-1$. Otherwise the $r^2$ old points admit a partition into $r$ cliques of that hue. Since each has size at most $r$, this is precisely the forbidden full packing. Brouwer's hypotheses hold because independence is at most $r$ and $r^2>2r$. [Brouwer, Theorem 2](https://ir.cwi.nl/pub/6791/6791D.pdf)

At the worst allowed $E=r-4$ for each of the two hues, twice the resulting edge-count excess over $B(r^2)$ is $r^3-19r^2+46r-44$ for $r\ge6$. For $r=17+s$ this is $s^3+32s^2+267s+160>0$. For two *exact* grids the corresponding excess has sign $r^2-14r+12$, positive for $r\ge14$. This argument produces a missing color and does not locate a doubly demanded star edge.

**A local test using actual labels only.** For any pair $v,w$ and any hue $a$, take $X=N_a(v)\cap N_a(w)$. If at most one nontarget hue demands $vw$, there is some $c\ne a$ for which the largest adjacency eigenvalue of the graph of hues $a,c$ on $X$ is at most $r-3$. In particular an $a$-graph on $X$ of spectral radius greater than $r-3$ forces two nontarget demands on $vw$, whatever the label of that pair.

To verify this, designate the possible demanding nontarget hue as $c$ (or choose any such hue if there is no demand). Each of the other $r-2$ hues has independence at most $r-2$ on $X$, since $r-1$ independent common nonneighbors demand that hue on $vw$. For any graph $H$ of independence at most $s$, its adjacency matrix satisfies
$$
        w^\top A_H w\ \ge\ (\sum w_i)^2/s-\sum w_i^2
$$
for nonnegative weights. Indeed, maximize the weighted sum over complement edges at a fixed total weight. If two supported vertices are nonadjacent in the complement, move their combined weight to the endpoint giving the larger value; the objective is affine in that move. Repeating leaves a complement clique of size at most $s$, where Cauchy–Schwarz gives the inequality. Subtract the $r-2$ inequalities from the weighted sum over all edges of $X$. This gives $w^\top(A_a+A_c)w\le(r-3)\sum w_i^2$. Taking a nonnegative top eigenvector proves the assertion. The test may be applied to every vertex subset of $X$.

**Choosing a sparsest hue whose every edge already has one demand.** If a balanced extension exists, take a balanced coloring maximizing the sum of its squared color sizes. Choose a largest hue as a reserve. If an edge in any other hue can be removed without creating an independent $(r+1)$-set in its hue, reassign it to the reserve. Balance survives and the sum increases. Thus every edge of every nonreserve hue already has a demand from its owner. Take a sparsest such hue $a$, choosing any nonreserve hue in a tie of all the counts.

For $r\ge5$, every full $a$-clique is now an isolated component of $a$. Indeed a critical target edge from the clique to $y$ has $r-1$ other vertices witnessing its demand. They lie outside the clique and together with $y$ form an independent $r$-set disjoint from it, contrary to Section 2. The target components have independence numbers summing to at most $r$ and orders summing to $r^2+1$. Hence some connected component $H$ has $|H|>r\alpha(H)$, has no full clique, and every edge in it already demands $a$. Criticality also holds inside $H$, by additivity of independence over components.

For an edge $vw$ of this hue, a single nontarget demand suffices. Set $X=N_a(v)\cap N_a(w)$. If every nontarget hue fails to demand $vw$, sum the weighted inequality above over all $r-1$ of them. For every nonnegative $w'$ supported on $X$ it gives
$$
        (w')^\top A_a w' + (\textstyle\sum w'_i)^2/(r-2)
                    \le (r-2)\textstyle\sum (w'_i)^2 .
$$
In particular, for any disjoint target cliques in $X$ of sizes $s_i\le r-2$, it is necessary that
$$
                            \sum_i \frac{s_i}{r-1-s_i}\ \le\ r-2.       \tag{5}
$$
To see this take weight $1/(r-1-s_i)$ on each point of clique $i$, zero elsewhere. If the sum on the left of (5) is $T$, the displayed inequality gives $T^2/(r-2)\le T$ after keeping just the internal clique edges. For $r\ge6$, three disjoint common-neighbor cliques of size $r-3$ already violate (5). This is a second demand on a specified edge using the other colors, with no coordinate assumption. The existence of such an edge in the overfull component remains open.

## 5. Overlapping witnesses among the other colors

There is a separate way of locating the edge that uses no chosen root. Suppose a set $H$ of $2r+1$ vertices, $r\ge4$, has target independence at most two and contains no target $K_r$. **Every assignment of the remaining labels forces two nontarget hues to demand the same edge of $H$.**

Let $F$ be the graph of all nontarget edges on $H$. It is triangle-free. Each $F$-neighborhood is a target clique, so $\Delta(F)\le r-1$ and $e(F)\le(2r+1)(r-1)/2$. Any subgraph of $F$ with independence at most $r$ needs at least $r+3$ edges. Indeed the ordinary Turán floor on $2r+1$ points is $r+2$, with equality only for a triangle and $r-1$ disjoint edges. The triangle cannot occur.

Call a nontarget hue deficient if it misses some $(r+1)$-set in $H$. Two missing sets of different hues that share two vertices demand both hues on the common pair. If there are three deficient hues, take one set for each. Were their pairwise intersections at most one, their union would have size at least $3(r+1)-3=3r>2r+1$. If there are at most two deficient hues and no double demand, the nontarget edges must include at least $r-2$ disjoint subgraphs of independence at most $r$. With at most one deficient hue take the other hues. With two take the $r-3$ other hues and the union of the two deficient ones: an independent $(r+1)$-set in their union would miss both. Thus $e(F)\ge(r-2)(r+3)>(2r+1)(r-1)/2$, a contradiction. The earlier packing argument at this size needed only one missing hue.

More generally take $|H|=hr+1$, $2\le h\le r$, and target independence at most $h$. If $r>B(h)$, at most $h$ distinct nontarget hues can be deficient without a double demand, since $h+1$ missing sets with pairwise intersections at most one use at least $(h+1)(r+1)-B(h+1)>hr+1$ points. Every nontarget subgraph of independence at most $r$ has at least $L=rB(h)+2h-1$ edges, by Brouwer's theorem. It has clique number at most $h$, so $r$ cliques cannot cover its $hr+1$ points. If $t\ge2$ hues are deficient and there is no double demand, every pair of them has a union with at least $L$ edges. Summing over their pairs yields a lower bound $tL/2$ on their total. With $t=0$ or $1$, at least $r-2$ individual hues have the required floor. In either case it is necessary that $e(F)\ge(r-1-h/2)L$. At higher $h$ this inequality need not exceed the available capacity.

## Scope

The odd-cycle family rules out a deduction of the small grid from sparsity, the target independence cap, edge criticality and old-square balance alone. Its other hues give explicit conflicting demands. For arbitrary balanced old squares we still lack a guarantee that two hues admit the grids of Section 4, that the error totals violate (3) or (4), or that the common-neighborhood test fires. The previous private large-order cutoff remains $r\ge2^{483}$. The general arguments here are human-readable proofs awaiting independent review.
