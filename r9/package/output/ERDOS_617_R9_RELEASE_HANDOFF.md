# Erdős Problem 617: fixed-\(r=9\) release handoff

Date: 21 July 2026

## Verdict

**LOCALLY PROVED; PUBLIC PACKAGE VERIFIED; EXTERNAL REVIEW PENDING.**

The local theorem is:

> Every nine-coloring of \(E(K_{82})\) contains ten vertices whose
> induced edges omit at least one color.

The mathematical proof and theorem commits are complete. The independent
CaDiCaL audit of the order-26 level \(m=64\) passed all 101,880 raw states
with zero SAT and zero UNKNOWN. The solver-free proof of that level remains
the proof premise and has passed from committed source in a clean checkout.
The exact public directory layout has passed the dependency-ordered release
replay. No public push, external review, or submission is claimed here.
Erdős Problem 617 for arbitrary \(r\) remains open.

This file supersedes older fixed-\(r=9\) status statements. Historical
notes remain useful for their scoped lemmas, experiments, and audit trails.

## 1. Dependency graph

### Node A: colored least-color reduction and packing theorem

- Result: a hypothetical counterexample has a least color graph \(G\)
  with \(e(G)\le369\) and minimum degree at most eight.
- Result: strictness of the five packing cells for that degree forces five
  disjoint target copies of \(K_9\) in a target nonneighbor set.
- Result: the full-color representative lemma and colored thresholds
  forbid those five blocks.
- Theorem file:
  research/erdos-617-r6/COLORED_CORE_LADDER.md.
- Verifier:
  research/erdos-617-r6/verify_colored_core_ladder.py.
- Current theorem commit:
  93cc83ed68155a149c432d0d437453acb6f7dbff.
- Replay:

~~~sh
python3 research/erdos-617-r6/verify_colored_core_ladder.py
~~~

- Human/computer status: human proof with an integer-arithmetic replay.
- Published inputs: Turán's theorem, the
  Andrásfai--Erdős--Sós theorem, the Kang--Pikhurko theorem, and Brooks's
  theorem.
- Nonclaim: this node alone does not produce the terminal floors needed
  for the degree-eight row.

### Node B: order-26, degree-eight branch

- Result: the common 17-core two-row theorem excludes the order-26
  degree-eight branch under \(e(H)\le120\).
- Theorem file:
  research/erdos-617-r6/R9_P93_ORDER26_D8_TWO_ROW_EXCLUSION.md.
- Verifier:
  research/erdos-617-r6/verify_r9_p93_order26_d8_two_row.py.
- Commit: dccdfa4cba2c1af0f4fd444bb9d6c24bcec94d30.
- Manifest: no standalone artifact manifest is needed; the catalog and
  witness digests are pinned in source.
- Artifact location: no SAT artifact is needed. The retained data are the
  fourteen-core catalog and witness digest.
- Replay:

~~~sh
python3 research/erdos-617-r6/verify_r9_p93_order26_d8_two_row.py \
  --geng /path/to/pinned/geng
~~~

- Human/computer status: human contradiction plus exhaustive reconstruction
  of fourteen core types and 2,228,224 cover masks.
- Imported input: nauty canonical graph generation.
- Nonclaim: the same theorem also treats the order-27 degree-nine branch,
  but not the regular order-27 branch.

### Node C: order-26, degree-nine branch

- Result: all nine complement-core levels \(m=56,\ldots,64\) are
  impossible.
- Canonical theorem notes and current commits:

| Levels | Theorem note | Commit |
|---|---|---|
| \(56,57\) | R9_P93_ORDER26_D9_ENDPOINT_56_57.md | 99f986867e587480c5dc4c7baba173d3ab9bca82 |
| \(58\) | R9_P93_ORDER26_M58_REDUCED_FRONTIER.md | f8f16401ec2c5c7959f201f6b342e700e3fd9274 |
| \(59\) | R9_P93_ORDER26_M59_REDUCED_FRONTIER.md | 7941226852393ad5f1d228fef479b84a64ede01d |
| \(60\) | R9_P93_ORDER26_M60_REDUCED_FRONTIER.md | 3c83b3547b32ad341d87e7ef70af399ef394db36 |
| \(61\) | R9_P93_ORDER26_M61_REDUCED_FRONTIER.md | 995104189d9c4c1e561b7f6314f81d485b2b3dbf |
| \(62\) | R9_P93_ORDER26_M62_REDUCED_FRONTIER.md | a182e0a1a5f0736a8a1fcf2ec3fa451b9ec1acdc |
| \(63\) | R9_P93_ORDER26_M63_REDUCED_FRONTIER.md | 81447ddd956706941108478ff810bff45c7327fa |
| \(64\) | R9_P93_ORDER26_M64_REDUCED_FRONTIER.md | 722b874c6a3bf4a9e8f8c2a8d959bb691354456b |

- Manifest for \(m=62\):
  research/erdos-617-r6/artifacts/r9-order26-m62/manifest.json.
- Manifest for \(m=63\):
  research/erdos-617-r6/artifacts/r9-order26-m63/manifest.json.
- Manifest for \(m=64\):
  research/erdos-617-r6/artifacts/r9-order26-m64/manifest.json,
  SHA-256 c1c7bb3187b33cca65315d1ec0fc0a50dd693910169858148508be201595362f.
- Human/computer status: exact rational duals, direct structural lemmas,
  and deterministic solver-free finite-state searches. Levels \(58\)
  through \(63\) also have completed independent Boolean reconstructions.
- Current \(m=64\) proof receipt:

~~~text
core_shell_pairs=7454
exact_dual_exclusions=6892
raw_scalar_states=101880
surviving_scalar_states=10639
three_hub_states_excluded=4
two_hub_states=10635
orbit_UNSAT=10635
orbit_SAT=0
orbit_representatives=3883026
demand_states=299684034
~~~

- Independent \(m=64\) audit receipt:

~~~text
q_states=101880 cadical_UNSAT=101880 cadical_SAT=0 cadical_UNKNOWN=0
classification_sha256=e68dfcaf336ff575e0091a757e60874b81cd79966b418df2e6487eb698ade331
cadical_receipt_sha256=d08cee42dcfbab41f8caaa3fec7a7133059577d63ec7a02ebe81db496a04c218
status=PASS
~~~

- Independent audit implementation:
  research/erdos-617-r6/r9_p93_order26_m64_cadical_audit.py.
- Machine-readable receipt:
  research/erdos-617-r6/artifacts/r9-order26-m64/cadical_receipt.json.
- Nonclaim: the audit must not be called complete before it returns
  101,880 UNSAT, zero SAT, and zero UNKNOWN with the pinned digest.

Nodes B and C prove

\[
 P_3(26)\ge121.
\]

### Node D: order-27 terminal

- Result: \(\mathcal P_3(27)=\varnothing\).
- Degree-nine theorem: Node B's common 17-core argument.
- Degree-ten reduction:
  research/erdos-617-r6/R9_P93_D10_CORE_DEGREE_SUM_REDUCTION.md.
- Degree-ten verifier:
  research/erdos-617-r6/verify_r9_p93_d10_core_degree_sum.py.
- Closure theorem:
  research/erdos-617-r6/R9_P93_ORDER27_CLOSURE.md.
- Semantic and LRAT verifier:
  research/erdos-617-r6/verify_r9_p93_d10_certificate.py.
- Corruption suite:
  research/erdos-617-r6/test_r9_p93_d10_certificate_corruptions.py.
- Commit: 1f6e8fdd6a59eaaa717aa91c49bbe3a75aa75b78.
- Artifact root:
  output/erdos-617-artifacts/r9-p93-order27-d10-20260721/.
- The four manifest SHA-256 values are:

~~~text
f332adb9327c02b2b9964a1d781baae75d27371a83995dc3c1f7393b35c09cba
0df642bb21e52310ec19f479d5ec62fe179a0b075738643bb165baeef7dcda40
7427d8c307411374f332056bdd3638ff26c9d70c6c1283458d87f6313fd1bc2f
e1cc2b4b6f2643d16bc3ba64d50e7e1e9cf73d7043a19f632571bf328c158d1d
~~~

- Aggregate receipt:

~~~text
cases_reconstructed=332
cnfs_verified=50
clauses_verified=9100515
totalizer_merges_verified=79574
totalizer_shapes_verified=83
totalizer_states_verified=108839
lrat_proofs_replayed=50
status=PASS
~~~

- Human/computer status: the human endpoint-degree-sum lemma removes 282
  cores. Independent semantic reconstruction and LRAT replay exclude the
  remaining 50.
- Imported inputs: nauty, Kissat, DRAT-to-LRAT conversion, and certified
  LRAT checking.
- Nonclaim: a SAT result for the relaxation would not be a coloring. Only
  the checked UNSAT proofs are used.

### Node E: the 37-vertex full-color bridge

- Result:

\[
 P_3(26)\ge121,\quad \mathcal P_3(27)=\varnothing
 \quad\Longrightarrow\quad P_4(37)\ge192.
\]

- Theorem file:
  research/erdos-617-r6/R9_D8_FULL_COLOR_BRIDGE.md.
- Line audit:
  research/erdos-617-r6/R9_FIXED_OUTER_AUDIT_20260721.md.
- Verifier:
  research/erdos-617-r6/verify_r9_d8_full_color_bridge.py.
- Commit: 5f0a085b3e346506687aa901a2e2518554b5fe31.
- Replay:

~~~sh
python3 research/erdos-617-r6/verify_r9_d8_full_color_bridge.py
~~~

- Exact human calculation: for a degree-ten vertex, if
  \(M=45-e(H[A])\), then \(M\ge16\),
  \(e_H(A,B)\ge2M\), and

\[
 e(H)\ge10+(45-M)+2M+121=176+M\ge192.
\]

- Human/computer status: human proof with exact integer replay and two
  dependency mutations.
- Nonclaim: replacing \(45-M\) by 29 in this lower bound is invalid.

### Node F: five-cell propagation and final theorem

- Propagated diagonal:

\[
 192,\ 227,\ 264,\ 301,\ 338.
\]

- Degree-eight packing margins:

\[
 5,\ 4,\ 3,\ 2,\ 3.
\]

- All 45 outer cells are strict or empty.
- Final theorem file:
  research/erdos-617-r6/R9_FIXED_OUTER_AUDIT_20260721.md.
- Current checkpoint:
  output/ERDOS_617_R9_CURRENT_CHECKPOINT.md.
- Verifiers:
  research/erdos-617-r6/verify_r9_d8_full_color_bridge.py and
  research/erdos-617-r6/verify_colored_core_ladder.py.
- Commit: 5f0a085b3e346506687aa901a2e2518554b5fe31.
- Human/computer status: human implication chain with exact integer
  recurrence replay.
- Nonclaim: the conclusion is only the fixed \(r=9\) case.

## 2. Manuscript

- Source:
  research/erdos-617-r9-manuscript/main.tex.
- Bibliography:
  research/erdos-617-r9-manuscript/references.bib.
- Current build:
  research/erdos-617-r9-manuscript/build/main.pdf.
- Status: affirmative preprint. Its live status banner records the completed
  independent audit, clean public-package replay, and pending external review.
- Author: Robert Sneiderman.
- Universal nonclaim: the paper does not prove the assertion for
  arbitrary \(r\).

## 3. Release-gate receipt

The four order-27 archives pass SHA-256 and decompression checks. The exact
public directory layout passed its release entry point with:

~~~text
packages_verified=4
cases_reconstructed=332
cnfs_verified=50
clauses_verified=9100515
totalizer_merges_verified=79574
totalizer_shapes_verified=83
totalizer_states_verified=108839
lrat_proofs_replayed=50
r9 P3 d10 corruption suite: PASS tests=5 baseline_lrat=PASS
47 passed
fixed_r9_release_replay=VERIFIED
~~~

The final manuscript builds as a 12-page PDF without missing references,
undefined citations, or overfull boxes. Every page has passed visual
inspection. All local release gates pass. External mathematical review
remains outstanding and must not be implied by a release or proof-claim
submission.

No public push, tag, release, email, or proof-claim submission is
authorized by this handoff.

## 4. Universal problem

The universal Erdős Problem 617 remains open. Its worktree and dependency
ledger are separate. The fixed-\(r=9\) release does not import the open
synchronization or descent theorem.
