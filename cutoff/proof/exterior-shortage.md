# Why the exterior vertices fall short

Robert Sneiderman and OpenAI GPT‑6.2 Astra · GitHub proof supplement · 25 November 2026

Color the edges of $K_{r^2+1}$ with $r$ colors, where $r\ge255\cdot2^{136}$. Suppose every $r+1$ vertices see all the colors. Choose the sparsest color $J$ and the retained cliques given by the width theorem. Put $h=s-1$ for the number of omitted rows. Let $G$ consist of vertices outside the retained cliques that have at most $9r/(40s)$ neighbors of color $J$ in each retained clique. Lean proves
$$
\Delta=hr-|G|>3r/20.
$$
Both the width and the shortage hold for one selection of rows in the original coloring. The formal statement returns that selection for use in the final signed cut. [Theorem from the original coloring](ExteriorShortage.lean) · [Selection and auxiliary construction](coloring-to-exterior.md)

## Completing a prescribed independent set

If the shortage fails, select up to $hr+1$ vertices of $G$. The auxiliary construction gives $h$ disjoint cliques on a subset of these vertices. A large attachment means more than $81r/200$ target neighbors in an auxiliary clique or more than $369r/1000$ in a temporarily trimmed ordinary clique.

Prescribe either two independent exterior vertices, or one exterior vertex and up to two compatible representatives in occupied rows. In each remaining requested row the exterior attachments must be small. First fill the auxiliary rows. Every available list is nonempty. For two distinct rows the product of their list sizes exceeds the total number of surviving cross edges. This last comparison matters because two prescribed exterior vertices may both exclude many candidates from the same row. The proof charges each deletion or previously prescribed representative against its actual rows. The square budget pays for the losses in the two rows together. [List counts](PrescribedListCounts.lean) · [Product estimates](PrescribedProducts.lean) · [Actual excluded neighbors](ColoredAuxiliaryExtension.lean)

Choose an entry uniformly from each available list. A particular cross edge is chosen with probability at most the reciprocal of the product of its two list sizes. Summed over cross edges this gives fewer than one expected conflict when edges are present. With no edges, any choice works. Lean proves the finite counting version, including the cases of zero and one requested rows. Now fill the ordinary rows. In the tighter case at least $1059r/32000>r/41$ candidates remain per row. The ordinary representative theorem applies. The combined proof counts the prescribed and newly chosen vertices in the original vertex set and proves that they are distinct and independent in color $J$. [Finite counting proof](EdgeProductTransversal.lean) · [Completion across both families](PrescribedCompletion.lean)

## Why the rows cannot pay for all arrivals

Use only the auxiliary rows if the selected set has $hr+1$ vertices. Otherwise count on all $r^2+1$ vertices, using the auxiliary and ordinary rows together. In either case an arena with $p$ rows has $pr+1$ vertices and target independence number at most $p$. An exterior vertex with no large attachment would extend across all the rows. A vertex with just one large row must join every vertex in it, and two such vertices with the same row must be adjacent. Any missing edge would give two prescribed vertices that extend across the other $p-1$ rows. Add these vertices to their respective cliques. If $P$ vertices remain outside, their population satisfies
$$
\sum_i (r-|C_i^{\mathrm{enlarged}}|)+1=P .
$$
Every remaining vertex has at least two large attachments to the original rows. [The two arenas](AttachmentArena.lean) · [Enlargement and the exact identity](UniqueAttachment.lean)

For a clique of size $r-d$ and any $z$ exterior arrivals, counting all other colors gives
$$
\sum_y \deg_J(y,C)+zd\le (r-1)d+z(z+1)/2 .
$$
Two disjoint cliques with vertex deficits $d,e$ have at most $r-d-e+de$ target edges between them. Charge each arrival $77d/100+r/10000$ against its row. If a sender has exactly two large rows, every nonneighbor of the sender in one must be adjacent to every nonneighbor in the other. Otherwise the sender and the two nonneighbors extend to an independent set of size $p+1$. The bound on the cut between the cliques then forces the sender's two original degrees to sum to more than $1.16421r$. For three large rows their combined deficit bound suffices directly. Every further large row contributes positively after its charge. [One- and two-clique edge counts](ExteriorRowEdges.lean) · [Degree and rounding bounds](CliqueArrivalPrice.lean) · [Two- and three-row comparisons](MultipleArrivalPrice.lean)

Add the degrees minus their charges first by sender, then by row. Each of the $P$ senders contributes at least $r$. The enlarged rows together can supply at most $(r-1)(P-1)$. The exact deficit identity implies $P\ge1$, so the bounds contradict each other. This proves the strict shortage. [Per-sender argument](SenderPayment.lean) · [Sum over the same incidences](ArrivalSummation.lean) · [Full §4 conclusion](ExteriorShortage.lean)

## What the final signed cut can use

Return to the original retained cliques. Write $H$ for the exterior vertices outside $G$ and $D$ for the total deficit of those cliques. The vertex count gives $|H|=1+\Delta+D$. Every vertex in $H$ has an actual destination with more than $9r/(40s)$ target neighbors. A retained clique with deficit $d$ has at most $2d$ exterior senders of degree greater than $r/2$, and their total degree into that row is at most $rd$. If $M$ senders have no such strong destination and $B$ senders have at least two, this gives $M+D\ge1+\Delta+B$. [Sender counts on the original rows](SenderDestinations.lean) · [Strong row bound and variance charge](HeavyRowSenders.lean) · [Population comparison](SenderPopulation.lean)

For a sender with neighbor fraction $q$ in one row, draw a uniformly random vertex. On hitting a neighbor, retry with probability $100\rho$, where $\rho=9/(40s)$, using a fresh uniform draw. Lean derives the success probability $(1-q)(1+100\rho q)$ and the probability $(1+100\rho q)/|C|$ of returning each particular nonneighbor in that clique. The width bound gives the extra charge $37\rho r(1-q)$ for a strong sender. [Exact finite trial](SenderRetry.lean) · [Surplus on a retained row](RetainedSenders.lean)

The next graph step is to combine the individual trials into the marked sample on these same rows. The proof must bound the conflicts and the cost of repairing them, including when two senders choose the same row. Those estimates are inputs to Appendix A, §5, inequality (5). The exact numerical checker verifies its 1,280 endpoint comparisons. The implication from the coloring to (5) and the end-to-end cutoff theorem remain open in Lean. [Marked senders and excess arcs](cutoff-165.md#5-charge-only-the-excess-of-a-heavy-load) · [Final inequality](weighted-width.md#5-the-five-width-bands-and-the-final-signed-cut) · [Endpoint checker](verify_retained_width.py)

## Replaying the proof

From the directory containing the pinned Lake environment, run

```sh
lake env python3 -B proof/replay_pruning_kernels.py shortage
```

Use `enlargement` for the prescribed extensions and `senders` for the initial §5 counts and the single-sender trial. Each command builds the Lean modules from source, reports the axioms, and replays one export with Lean’s kernel, Lean4Lean and Nanoda. Add `--lean-only` for the source build and axiom report. [Replay script](replay_pruning_kernels.py)

### Verification record, 25 November 2026

The three kernels accepted each export. Each replay audited eleven named declarations and found only `propext`, `Classical.choice` and `Quot.sound`. The declaration counts include imported dependencies.

| Replay | Declarations | Export SHA-256 |
| --- | ---: | --- |
| `enlargement` | 28,730 | `ed4bcbf0d9cacb45d885b5e611679125db72e3c4f2c53788f93c26e3284600ea` |
| `shortage` | 29,820 | `cc29199c9e6e3e415ec397e690a1dbab46525bc525f55b3987c58d595f6ea8d8` |
| `senders` | 29,873 | `08c99d25b9b575d992d22ff780cb1b1be920f276bae3ce3cd9cdf5408d8448d1` |
