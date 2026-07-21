# Dependency audit for fixed \(r=9\), order 26, level \(m=64\)

## Verdict

PASS. The human implication chain, exact rational duals, solver-free scalar
reduction, three-hub argument, and two-hub orbit exhaustion pass the checks
below. A separately encoded incremental CaDiCaL audit also excludes all
101,880 raw states. The dependency-closed release manifest verifies.

## 1. Scope checked

The theorem excludes only an order-26 target graph \(H\) with

\[
 \alpha(H)\le3,
 \quad
 \omega(H)\le8,
 \quad
 e(H)\le120,
 \quad
 \delta(H)=9,
\]

when a degree-nine witness has a 16-vertex complement core with 64 edges.
It does not address the order-26 degree-eight branch, either order-27
branch, the stronger order-26 edge levels needed by the present outer
recurrence, or the outer implication itself.

## 2. Human implication chain

The following deductions were checked directly.

1. A degree-nine witness \(v\) splits the other 25 vertices into its
   nine-vertex neighborhood \(A\) and 16-vertex nonneighborhood \(B\).
2. For \(F=\overline{H[A]}\), a \(K_4\) is an independent four-set of
   \(H\). An independent eight-set of \(F\), together with \(v\), is a
   target \(K_9\). Hence \(F\) is \(K_4\)-free and
   \(\alpha(F)\le7\).
3. For \(L=\overline{H[B]}\), an \(L\)-triangle together with \(v\) is
   an independent four-set of \(H\). An independent nine-set of \(L\)
   is a target \(K_9\). A vertex of degree at least nine in the
   triangle-free graph \(L\) has an independent nine-set in its
   neighborhood. Hence \(L\) is triangle-free,
   \(\alpha(L)\le8\), and \(\Delta(L)\le8\).
4. Since \(e(L)=64\), equality in Mantel's theorem gives
   \(L=K_{8,8}\). Its only independent eight-sets are its two sides
   \(X,Y\).
5. The target-edge count is
   \[
   e(H)=9+(36-f)+(120-64)+\sum_aq_a,
   \]
   so \(e(H)\le120\) gives \(\sum_aq_a\le f+19\).
6. Minimum degree at \(a\in A\) gives \(q_a\ge d_F(a)\). Minimum
   degree at \(b\in B\) gives column demand
   \(d_L(b)-6=2\).
7. If \(aa'\in E(F)\), failure of \(D_a\cup D_{a'}\) to cover one
   edge of \(L\) produces an independent four-set of \(H\). If three
   shell vertices form a triangle of \(F\), failure of their rows to
   cover one core vertex gives the same contradiction.
8. No row \(D_a\) contains \(X\) or \(Y\), because either set is an
   eight-clique of \(H[B]\) and would form a target \(K_9\) with \(a\).
9. Summing the 16 column demands gives
   \(\sum_aq_a\ge32\), hence \(f\ge13\). Summing
   \(q_a\ge d_F(a)\) gives \(\sum_aq_a\ge2f\), hence \(f\le19\).
10. A shell realization supplies a nonnegative slack vector of total
    at most \(19-f\). Every shell edge has row-size sum at least eight,
    because its two rows cover \(K_{8,8}\). Thus the shell catalog's
    edge range and minimum-slack filter omit no candidate.

No item in this implication chain uses a conclusion from the finite
search.

## 3. Finite partition

The exact catalog partition is

\[
 7454=6892+562.
\]

Exact rational duals exclude the first 6,892 core-shell pairs. The scalar
replay checks 101,880 row-size states over the 562-pair complement. It
rejects 551 pairs and leaves eleven pairs with 10,639 scalar states.

Four states lie on four cover-number-three shells and are excluded by the
three-hub argument. The remaining seven shells have cover number two and
contain 10,635 states, all excluded by the orbit recurrence. Catalog,
complement, classification, and frontier hashes pin every boundary of this
partition.

## 4. Exact-dual semantics

Every selected inequality is a valid lower bound on a sum of incidence
variables. The semantic verifier reconstructs the core and shell catalogs,
the row lower bounds, the column demands, every core-edge cover inequality,
and every triangle-cover inequality.

Each retained rational weight is positive. Exact Fraction arithmetic
checks that every incidence variable has total coefficient at most one
and that the weighted right side is strictly larger than the global
incidence budget \(f+19\). Floating-point optimization proposes supports
but is not a proof premise. The retained generator must reproduce the
JSONL byte for byte before the package is banked.

## 5. Scalar semantics

For each complement shell, the scalar verifier enumerates every vector

\[
 q_a=d_F(a)+\epsilon_a,
 \qquad
 \epsilon_a\ge0,
 \qquad
 f+\sum_a\epsilon_a\le19.
\]

It then enumerates all integer side counts

\[
 x_a=|D_a\cap X|,
 \qquad
 y_a=|D_a\cap Y|,
 \qquad
 x_a+y_a=q_a,
\]

subject to \(0\le x_a,y_a\le7\), the two side-demand sums, the
edge-cover disjunctions, and both triangle-cover sums. These are necessary
conditions for an incidence realization. A rejected state is impossible;
a surviving state is not treated as a realization.

## 6. Three-hub exclusion

Each of the four cover-number-three shells has a unique minimum cover
\(\{c,u,w\}\), whose induced graph is the path \(u-c-w\). The exact scalar
assignments reduce, up to exchanging \(X,Y\), to

\[
 |D_c\cap X|=1,\quad |D_c\cap Y|=6,\quad
 D_u,D_w\subseteq X,\quad |D_u|=|D_w|=7.
\]

Writing \(D_c\cap X=\{x_0\}\) and \(S=D_c\cap Y\), the two hub edges
force

\[
 D_u=D_w=X\setminus\{x_0\}.
\]

Every row adjacent to all three hubs has order three. Its edge with \(c\)
must cover \(Y\), while its edges with \(u,w\) must cover \(X\). It is
therefore exactly

\[
 (Y\setminus S)\cup\{x_0\}.
\]

The six vertices in \(S\) have only their incidence in \(D_c\) among the
hubs and all-hub rows. Their second required incidences need six remaining
row positions. The four shell states have remaining capacities
\(4,0,1,2\), respectively. Each is impossible. The solver-free checker
enumerates all ten scalar assignments and verifies the shell structure and
capacity calculation.

## 7. Orbit quotient and recurrence

For \(K_{8,8}\), the side-preserving subgroup is \(S_8\times S_8\).
For an ordered hub-row pair, the four membership counts
\((00,01,10,11)\) on each side form a complete orbit invariant. Permuting
vertices inside the corresponding bins transports any pair with one
signature to any other.

The self-test compares the formula and direct representative counts in
every ordered row-size cell. It also checks transports under the adjacent
transposition generators.

After fixing the two hub rows, the other seven shell vertices have no
shell edges among them. Their remaining local restrictions are unary,
apart from hub-hub-low triangles already encoded in each domain. The
recurrence tracks the sixteen residual lower-bound column demands.

For a fixed low-row domain and the support of positive residual demands,
an effect contained in another effect can be deleted. Both effects come
from rows in the same unary domain. Replacing the smaller by the larger
preserves the row's local restrictions and cannot decrease any positive
column count. The antichain reduction therefore preserves existence and
nonexistence.

## 8. Independent reconstruction and package gates

The independent CaDiCaL reconstruction rebuilds every one of the 101,880
raw row-size states. Its CNF is written separately from the solver-free
orbit recurrence. It encodes exact row sizes with incremental totalizers,
all column demands, every shell-edge cover, every triangle union, and both
forbidden full sides. The pinned replay returned

~~~text
q_states=101880 cadical_UNSAT=101880 cadical_SAT=0 cadical_UNKNOWN=0
classification_sha256=e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331
cadical_receipt_sha256=d08cee42dcfbab41f8caaa3fec7a7133059577d63ec7a02ebe81db496a04c218
status=PASS
~~~

The machine-readable receipt records the full pair-size profile, tool
versions, worker count, and wall time. The audit is confirmation, not a
premise of the solver-free theorem.

The corruption suite passes 17 tests covering truncated or
mutated dual data, duplicate or missing records, malformed weights, a
false dual overload, altered core premises, and corrupted three-hub and
orbit receipts. Python compilation, Ruff, strict Mypy, final source hashes,
tool versions, and the dependency-closed manifest verification pass. A
replay from committed source in a clean checkout remains a release-level
gate.

This is a local audit, not external mathematical review. The fixed
\(r=9\) theorem is locally proved. Erdős Problem 617 for arbitrary \(r\)
remains open.
