# Dependency audit for the fixed \(r=9\), 27-vertex terminal

> **SUPERSEDED DOWNSTREAM STATUS.** This terminal audit remains valid.
> Its statements that fixed \(r=9\) remained open are historical. See
> output/ERDOS_617_R9_RELEASE_HANDOFF.md for the current theorem chain.

## Verdict

PASS LOCALLY. The implication chain, finite partition, formula semantics,
and 50 LRAT refutations agree. The theorem proved is only the emptiness of
the 27-vertex three-layer terminal family. Downstream packages complete
fixed \(r=9\) locally. The universal problem remains open.

## 1. Human implication chain

The following deductions were checked directly.

1. Full-color coexistence gives \(e(H)\le D_9(27)=135\).
2. The colored terminal-core theorem gives \(\delta(H)\ge9\).
3. The average-degree bound gives \(\delta(H)\le10\).
4. The degree-nine case maps to the common 17-core theorem.
5. In the degree-ten case, equality in the handshake bound makes \(H\)
   10-regular with 135 edges.
6. Exact regularity gives \(|C_b|=d_L(b)-5\).
7. Every core edge requires two columns whose union covers \(F\).
8. Since \(\alpha(F)\le7\) on ten vertices, every such cover has order at
   least three. Hence every core edge has endpoint-degree sum at least 13.
9. The checked core catalogue has 332 types; exactly 50 satisfy this last
   condition.
10. The relaxation CNF for each of those 50 types is UNSAT.

No step assumes the outer fixed-\(r=9\) conclusion.

## 2. Finite partition

The core count by edge level is

~~~text
56: 179
57: 80
58: 39
59: 17
60: 9
61: 4
62: 2
63: 1
64: 1
total: 332
~~~

The minimum edge-degree-sum profile is

~~~text
10: 19
11: 102
12: 161
13: 38
14: 10
15: 1
16: 1
~~~

Thus \(19+102+161=282\) cores are excluded by the human degree-sum
lemma, and \(38+10+1+1=50\) enter the certificate package. The four shard
sizes are 14, 13, 9, and 14, with no duplicate or missing survivor index.

## 3. Formula direction

Every clause family is a necessary consequence of a surviving target
configuration. The formula omits some valid full-color constraints and an
explicit decomposition into the eight other colors. This direction is
safe: every real configuration gives a satisfying assignment of the CNF,
while a satisfying assignment need not extend to a coloring. Therefore an
LRAT refutation of the relaxation excludes the real configuration.

The independent verifier reconstructs each clause family and compares the
DIMACS formula as a clause multiset. It does not trust variable order,
generator output text, solver exit text, or floating-point optimization.

## 4. Counting encodings

The only auxiliary variables come from unary totalizers. For every merge
shape used by the 50 formulas, the verifier enumerates all input-count
states and checks that the clauses force the exact output-count state. It
audited 79,574 merges, 83 distinct shapes, and 108,839 count states.

## 5. Proof replay

Each formula was solved by Kissat, converted from DRAT to LRAT by
`drat-trim`, and replayed by `lrat-check`. The package pins the three binary
hashes, both source hashes, every artifact size and hash, every case index,
and the complete graph6 catalogue. The aggregate replay checked 9,100,515
clauses and accepted all 50 LRAT proofs.

The four manifest digests are recorded in
`R9_P93_ORDER27_CLOSURE.md`. A second local copy of the complete artifacts
is stored outside `/private/tmp` before the temporary build directories are
removed.

The deliberate corruption suite passed five tests. It rejected a modified
manifest, a same-size CNF byte change, a truncated CNF, a false source hash,
and a truncated LRAT proof after first replaying the unmodified proof.

## 6. Remaining caveats

1. The package is locally replayed but not externally reviewed.
2. The current archive is replay-complete rather than release-minimal.
3. The order-26 \(m=64\) package has passed its independent audit and
   clean-checkout replay.
4. The downstream full-color bridge and outer recurrence complete fixed
   \(r=9\) locally.
5. Erdős Problem 617 for arbitrary \(r\) remains open.
