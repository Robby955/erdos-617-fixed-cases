# Fixed r = 9 public-package replay receipt

Date: 21 July 2026

## Scope

The `release` mode was run from the exact public directory layout with the
four compressed order-27 release assets. This mode checks public file and
asset hashes, the order-26 level-64 dependency manifest, uniform level
arithmetic, the degree-eight core catalogue, the order-27 degree-sum
reduction, semantic reconstruction of all 50 retained formulas, every LRAT
proof, corruption tests, and the final outer implication arithmetic.

The longer `proof` and `audit` modes are supplied for full recomputation of
the order-26 finite searches and their separate solver reconstructions.
Their component programs and pinned receipts were checked during theorem
development, but they are not rerun by `release` mode.

## Recorded command

```sh
./r9/reproduce.sh \
  --mode release \
  --geng /private/tmp/nauty289-build/geng \
  --lrat-check /private/tmp/drat-trim-erdos617/lrat-check \
  --assets-dir output/erdos-617-r9-release-assets-20260721
```

The replay used Python 3.13.13, networkx 3.4.2, NumPy 2.4.4, SciPy 1.17.1,
pytest 9.0.3, z3-solver 4.16.0.0, python-sat 1.9.dev7, nauty 2.8.9, and the
LRAT checker from DRAT-trim commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`.

## Receipt

```text
manifest_sha256=c1c7bb3187b33cca65315d1ec0fc0a50dd693910169858148508be201595362f
valid_degree8_cores=14
degree8_cover_masks_checked=2228224
order27_valid_cores=332
order27_degree_sum_survivors=50
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
P3_26_floor=121 P3_27=EMPTY P4_37_floor=192
diagonal_P4_to_P8=192,227,264,301,338
d8_margins_j0_to_j4=5,4,3,2,3
all_45_outer_cells=STRICT_OR_EMPTY
fixed_r9_release_replay=VERIFIED
```

The fixed theorem remains an unreviewed proof claim. This receipt checks the
stated computational dependencies; it does not replace mathematical review
of the human implication chain.
