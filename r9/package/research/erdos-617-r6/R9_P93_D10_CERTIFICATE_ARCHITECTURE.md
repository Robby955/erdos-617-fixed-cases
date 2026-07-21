# Fixed \(r=9\), \(P_3(27)\), degree-ten certificate architecture

> **SUPERSEDED DOWNSTREAM STATUS.** This scoped package is a dependency
> of the locally proved fixed-\(r=9\) theorem. See
> output/ERDOS_617_R9_RELEASE_HANDOFF.md for the complete chain.

## Status

**LOCALLY PROVED; 50-CASE REDUCED PACKAGE REPLAYED.**

The deterministic catalogue contains 332 core cases. The human degree-sum
theorem in `R9_P93_D10_CORE_DEGREE_SUM_REDUCTION.md` excludes 282 and leaves
exactly 50. Four proof shards contain those 50 cases. An independent
semantic verifier reconstructed every formula and replayed every LRAT
refutation.

This package excludes only the degree-ten branch. The degree-nine branch is
closed separately in `R9_P93_ORDER26_D8_TWO_ROW_EXCLUSION.md`; their union is
stated in `R9_P93_ORDER27_CLOSURE.md`. The downstream full-color bridge and
outer recursion complete fixed \(r=9\) locally.

## Mathematical target

Let \(H\) be an actual target-color graph on 27 vertices in the fixed
\(r=9\), \(P_3(27)\) reduction. The branch treated here has

\[
 \alpha(H)\le 3,
 \qquad
 \omega(H)\le 8,
 \qquad
 e(H)\le 135,
 \qquad
 \delta(H)=10.
\]

The average-degree bound and minimum degree force \(H\) to be 10-regular
and \(e(H)=135\). Choose a vertex \(v\), put

\[
 A=N_H(v),
 \qquad
 B=V(H)\setminus(A\cup\{v\}),
 \qquad
 L=\overline{H[B]}.
\]

Then \(|A|=10\), \(|B|=16\), and \(L\) satisfies all of the following:

1. \(L\) is triangle-free.
2. \(\alpha(L)\le8\).
3. \(5\le d_L(b)\le8\) for every \(b\in B\).
4. \(56\le e(L)\le64\).
5. Every \(Z\subseteq B\) with \(|Z|\ge10\) satisfies
   \[
   e(L[Z])\ge 8p_9(|Z|),
   \]
   where
   \[
   p_9(n)=(9-a)\binom q2+a\binom{q+1}2,
   \qquad n=9q+a,\quad 0\le a<9.
   \]

For item 3, a vertex of \(L\)-degree at most four would already have at
least eleven target neighbors inside \(B\), contrary to 10-regularity.
The upper bound follows because every neighborhood in the triangle-free
graph \(L\) is independent. Item 4 follows from the eight inherited
nontarget colors and Mantel's theorem. Item 5 is the inherited full-color
density inequality.

The command

```text
geng -q -t -d5 -D8 16 56:64
```

followed by the independent checks in items 2 and 5 gives exactly 332
nonisomorphic graph6 cases. Lexicographic graph6 order defines case indices
\(0,\ldots,331\). Since all constraints are invariant under relabeling of
\(B\), one representative from each isomorphism class is enough.

The case counts by \(e(L)\) are

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

## Formula represented by each case

For a fixed core \(L\), the 205 primary variables are:

* 45 variables for edges of \(F=\overline{H[A]}\);
* 160 variables for target-color edges from \(A\) to \(B\).

Auxiliary variables come only from unary totalizers. The CNF imposes:

1. no independent four-set contained in \(A\);
2. no target \(K_9\) containing \(v\) and eight vertices of \(A\);
3. nonincreasing \(F\)-degree order as a sound shell-label symmetry break;
4. the exact total target edge count 135;
5. exact target degree ten at every vertex of \(A\cup B\);
6. the mixed \(2+2\) and \(3+1\) independent-four constraints;
7. every mixed split of a target \(K_9\);
8. the full-color cap on the 11-set \(\{v\}\cup A\);
9. the identity \(e(F)=e(L)-40\);
10. the ten local inequalities
    \[
    e(F[A\setminus\{a\}])\ge8.
    \]

The CNF deliberately omits the lazy ten-set cuts, higher mixed full-color
constraints, and an explicit decomposition into the eight nontarget
colors. It is therefore a relaxation of the actual colored configuration.
UNSAT for the relaxation excludes the actual configuration. SAT for the
relaxation would not produce a coloring and would require additional
checks.

## Sources

* `r9_p93_d10_certificate_generator.py` reconstructs and orders the 332
  cases, emits deterministic DIMACS, records hashes and clause categories,
  invokes Kissat, converts DRAT to LRAT, replays LRAT, and writes a canonical
  manifest.
* `verify_r9_p93_d10_certificate.py` does not import the generator or the
  exploratory scout. It independently reconstructs the 332 cases, rebuilds
  every emitted CNF, compares clause multisets, checks the exact unary
  totalizer merge schema, checks forcing clauses for every count state, and
  optionally replays every LRAT proof.

The verifier accepts more than one package. This permits bounded shards
without a manifest-merging step. Duplicate case indices are rejected.
`--require-all` requires indices 0 through 331, while
`--require-degree-sum-survivors` requires exactly the 50 indices left by the
human reduction.

Each package contains `manifest.json` and `manifest.sha256`. The manifest
records the graph6 catalog, selected indices, artifact sizes and SHA-256
values, generator and verifier hashes, proof-tool hashes, command templates,
formula metadata, and exact nonclaims. It contains no absolute filesystem
path.

## Final reduced-package receipt

The independent aggregate replay returned:

```text
r9 P3 d10 certificate semantic audit: PASS
packages_verified=4
cases_reconstructed=332
cnfs_verified=50
clauses_verified=9100515
totalizer_merges_verified=79574
totalizer_shapes_verified=83
totalizer_states_verified=108839
lrat_proofs_replayed=50
```

The manifest SHA-256 values are

```text
f332adb9327c02b2b9964a1d781baae75d27371a83995dc3c1f7393b35c09cba
0df642bb21e52310ec19f479d5ec62fe179a0b075738643bb165baeef7dcda40
7427d8c307411374f332056bdd3638ff26c9d70c6c1283458d87f6313fd1bc2f
e1cc2b4b6f2643d16bc3ba64d50e7e1e9cf73d7043a19f632571bf328c158d1d
```

Static checks on the two source files pass:

```text
python3 -m py_compile: PASS
ruff check: PASS
mypy --follow-imports=skip: PASS
```

## Reduced certificate workflow

The executable paths below are the binaries currently installed on this
machine:

```sh
R9_GENG=/private/tmp/nauty289-build/geng
R9_SOLVER=/private/tmp/kissat-erdos617/build/kissat
R9_DRAT_TRIM=/private/tmp/drat-trim-erdos617/drat-trim
R9_LRAT_CHECK=/private/tmp/drat-trim-erdos617/lrat-check
R9_PACKAGE_ROOT=/private/tmp/erdos-617-r9-p93-d10-reduced

mkdir -p "$R9_PACKAGE_ROOT"
for R9_RESIDUE in {0..3}; do
  python3 research/erdos-617-r6/r9_p93_d10_certificate_generator.py \
    --geng "$R9_GENG" \
    --output "$R9_PACKAGE_ROOT/shard-$R9_RESIDUE-of-4" \
    --degree-sum-survivors \
    --residue "$R9_RESIDUE" \
    --modulus 4 \
    --prove \
    --solver "$R9_SOLVER" \
    --drat-trim "$R9_DRAT_TRIM" \
    --lrat-check "$R9_LRAT_CHECK" \
    --compress
done
```

After all shards finish, the independent aggregate replay is:

```sh
R9_VERIFY_ARGS=()
for R9_RESIDUE in {0..3}; do
  R9_VERIFY_ARGS+=(
    --package "$R9_PACKAGE_ROOT/shard-$R9_RESIDUE-of-4"
  )
done

python3 research/erdos-617-r6/verify_r9_p93_d10_certificate.py \
  --geng "$R9_GENG" \
  "${R9_VERIFY_ARGS[@]}" \
  --lrat-check "$R9_LRAT_CHECK" \
  --require-degree-sum-survivors \
  --require-lrat
```

No full run should be described as complete unless the aggregate command
prints all of the following:

* `cases_reconstructed=332`;
* `cnfs_verified=50`;
* `lrat_proofs_replayed=50`;
* a final `PASS` with no missing or duplicate index.

The package should then receive a source audit, an independent mathematical
fidelity audit, a fresh replay from copied artifacts, and a visual review of
any PDF before external sharing.

## Exact nonclaims

1. A generated CNF without a checked LRAT proof is not a certificate of
   UNSAT.
2. The 50-case package proves only the fixed \(r=9\), \(P_3(27)\),
   degree-ten family.
3. The degree-nine branch remains a separate human dependency.
4. The downstream full-color bridge and outer implication complete fixed
   \(r=9\) locally.
5. Erdős Problem 617 remains open.
6. The theorem has not received external review or been published.
