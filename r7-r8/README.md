# The seven- and eight-color cases

This directory contains a computer-assisted proof preprint for two fixed
cases of [Erdős Problem 617](https://www.erdosproblems.com/617).

The claimed results are:

- Every seven-coloring of the edges of `K_50` has eight vertices whose
  induced edges omit a color.
- Every eight-coloring of the edges of `K_65` has nine vertices whose
  induced edges omit a color.

These are fixed-parameter results. They do not settle the problem for all
`r`, and they do not settle `r=9`.

## Proof structure

The PDF contains the full human implication chains.

- The `r=7` proof reduces to a weighted lemma on seven-vertex graphs. A
  direct labeled enumeration checks 12,618,770 cases. A separate Sage and
  nauty implementation reconstructs the same result from unlabelled graphs
  and automorphism orders. This part does not use SAT.
- The `r=8` proof combines a full-color extremal reduction with 862 finite
  unsatisfiability results. Separate semantic verifiers reconstruct the
  endpoint formula and all 861 core-shell formulas. A pinned LRAT checker
  then checks every refutation.

The LRAT files certify only the stated finite formulas. The reductions from
the edge-coloring problem to those formulas are mathematical arguments in
the PDF. The external inputs are Brooks's theorem, the
Andrasfai-Erdos-Sos theorem, and the Kang-Pikhurko extremal theorem.

## Contents

- `erdos-617-r7-r8.pdf`: human-readable preprint.
- `main.tex`, `references.bib`: manuscript source.
- `code/`: independent enumeration, arithmetic, and semantic checkers.
- `artifacts/endpoint18/`: compressed CNF and LRAT for the degree-five
  endpoint.
- `artifacts/r8-fixed-outer/`: portable archive containing all 861
  degree-eight formulas, LRAT files, graph streams, manifests, and the
  independent semantic verifier.
- `reproduce.sh`: full local replay.
- `SHA256SUMS`: hashes of the public release files.

## Checker build

The LRAT checker is pinned to DRAT-trim commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`:

```sh
git clone https://github.com/marijnheule/drat-trim.git
git -C drat-trim checkout 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C drat-trim lrat-check
```

The arm64 binary used for the recorded replay had SHA-256
`a2caddba197bbb0846aabf2dd54e87d79612e3b840ea0c43714f5c522f2d86c7`.
A binary built on another platform will normally have a different hash; the
pinned source commit is the portable identity.

## Full replay

From this directory, with Python 3 and Sage available:

```sh
./reproduce.sh --lrat-check "$PWD/drat-trim/lrat-check"
```

The final line is:

```text
fixed_r7_r8_release_replay=VERIFIED
```

If Sage is unavailable, `--skip-sage` skips only the second, independent
`r=7` reconstruction. The direct `r=7` enumeration and both `r=8` LRAT
packages still run.

## Review status and AI disclosure

This is an unreviewed proof claim posted for independent checking. A passing
replay checks the finite computations; it does not replace review of the
human reductions or the cited theorems.

OpenAI GPT-5.6 Sol was used substantially for proof search, drafting,
program development, and internal criticism. The repository-level
[AI disclosure](../AI_DISCLOSURE.md) describes the roles of the tools used.
Model agreement is not treated as a correctness certificate.

Please report a suspected gap with the theorem, page, and exact implication
that fails.
