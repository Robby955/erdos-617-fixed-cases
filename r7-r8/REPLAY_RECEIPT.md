# Fixed r = 7, 8 public-package replay receipt

Date: 24 July 2026

## Scope

`r7-r8/reproduce.sh` was run from a clean clone of this repository, with
no file modified beforehand. The run checks the package checksums, the
weighted light-edge enumeration, its independent Sage and nauty
reconstruction, the fixed-outer closure, the colored core ladder, the
degree-seven full-color bridge, the endpoint18 semantic reconstruction
and LRAT replay, and the portable degree-eight cross-certificate with
all 861 indexed pair replays.

This receipt records a reproduction of the published package. It is not
external mathematical review, and it does not establish the fixed r = 7
or r = 8 statement beyond what the package already claims.

## Recorded command

```sh
git clone https://github.com/marijnheule/drat-trim.git
git -C drat-trim checkout 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C drat-trim lrat-check

cd r7-r8
./reproduce.sh --lrat-check "$PWD/../drat-trim/lrat-check"
```

The checker built by that recipe has SHA-256
`a2caddba197bbb0846aabf2dd54e87d79612e3b840ea0c43714f5c522f2d86c7`,
matching the value pinned in the degree-eight package manifest.

Environment: Python 3.13, SageMath present so the independent r = 7
reconstruction was not skipped, arm64 macOS. Elapsed 182 seconds.

## Recorded output

```text
r7_weighted_graph_counts {6: 54257, 7: 116280, 8: 203490, 9: 293930}
r7_weighted_cases=12618770
r7_weighted_light_edge=VERIFIED
r7_sage_unlabeled_graph_counts {6: 40, 7: 65, 8: 97, 9: 131}
r7_sage_labeled_graph_counts {6: 54257, 7: 116280, 8: 203490, 9: 293930}
r7_sage_weighted_cases=12618770
r7_weighted_light_edge_independent=VERIFIED
r7_new_floors=P4(28):100,P4(29):113
r7_new_floors=P5(35):122,P5(36):134,P6(43):156
r7_fixed_outer_closure_arithmetic=VERIFIED
r8_d7_full_color_bridge_arithmetic=VERIFIED
encoding=VERIFIED
lrat=VERIFIED
checksum_entries_verified=2599
pair_index_count=861
status=VERIFIED
fixed_r7_r8_release_replay=VERIFIED
```

The primary and Sage reconstructions agree on all four labeled graph
counts and on every weighted maximum. Checksum lines reported OK across
the run: 2615.

## Note on the checker

The package requires `lrat-check`, built from the pinned drat-trim
commit by `make lrat-check`. Passing `drat-trim` itself makes the
endpoint18 replay report `s NOT VERIFIED`, because the DRAT checker
misparses LRAT antecedent hints, and building `lrat-check` without the
makefile flags produces a binary that fails the pinned hash comparison in
the degree-eight verifier. Both are covered by the recipe in
`r7-r8/README.md`.
