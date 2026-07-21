# The nine-color case

This directory contains a computer-assisted proof preprint for the fixed
`r = 9` case of [Erdős Problem 617](https://www.erdosproblems.com/617).

The claimed theorem is:

> Every nine-coloring of the edges of K₈₂ has ten vertices whose induced
> edges omit at least one color.

This is a fixed-parameter result. It does not prove the assertion for every
`r`, and it does not imply the `r = 10` case.

## Proof structure

The paper gives the complete human implication chain. Assuming a
counterexample, the colored density recursion reduces the deficient
minimum-degree row to two terminal statements:

- `P₃(26) ≥ 121`. The order-26 proof splits by minimum degree. Its
  degree-nine branch classifies the complement-core levels 56 through 64
  using exact rational certificates, structural reductions, and
  deterministic solver-free searches. A separate reconstruction of the
  final level checks 101,880 Boolean states. The degree-eight branch uses a
  fourteen-core classification and checks 2,228,224 cover masks.
- `𝒫₃(27) = ∅`. A degree-sum argument removes 282 of 332 regular endpoint
  cores. The other 50 are independently reconstructed and excluded by LRAT
  certificates.

These terminals imply `P₄(37) ≥ 192`. Exact recurrence arithmetic then
makes all 45 outer packing cells strict or empty, and the representative
selection argument gives the final contradiction.

## Contents

- `erdos-617-r9.pdf`: human-readable preprint.
- `main.tex`, `references.bib`: manuscript source.
- `package/`: theorem notes, exact data, manifests, semantic verifiers,
  corruption tests, and replay programs in their repository-relative paths.
- `reproduce.sh`: dependency-ordered replay entry point.
- `requirements.txt`: Python versions used for the recorded audits.
- `RELEASE_ASSET_SHA256SUMS`: hashes of the four large certificate archives.
- `ASSET_INDEX.json`: archive sizes, hashes, and aggregate replay receipt.
- `REPLAY_RECEIPT.md`: exact release-mode environment, scope, and result.
- `SHA256SUMS`: hashes of the files stored in this directory.

The four order-27 archives are GitHub Release assets rather than Git blobs.
Together they contain 50 CNF/LRAT instances and their manifests. Download
all four into one directory before running the release or proof replay.

## External tools

The graph catalogues were generated with nauty 2.8.9 `geng`. The recorded
Apple Silicon binary had SHA-256:

```text
3ca950af2145c546f9f586cf960eaf98f88fc3920564338f8306b6f58d018af5
```

The LRAT checker is pinned to DRAT-trim commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. Build it with:

```sh
git clone https://github.com/marijnheule/drat-trim.git
git -C drat-trim checkout 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C drat-trim lrat-check
```

The recorded Apple Silicon checker had SHA-256
`a2caddba197bbb0846aabf2dd54e87d79612e3b840ea0c43714f5c522f2d86c7`.
A binary built on another platform will normally have another hash.

The order-27 archives record the original `geng` binary hash. The public
portable wrapper relaxes only that binary-identity check. It still rebuilds
the 332-case catalogue, checks its pinned identities, checks the exact
source named by each archive, reconstructs every clause multiset, checks
all unary-totalizer semantics, and replays every LRAT proof.

## Replay modes

Install the Python dependencies in an isolated environment, then run:

```sh
python3 -m pip install -r requirements.txt

./reproduce.sh \
  --mode release \
  --geng /absolute/path/to/geng \
  --lrat-check /absolute/path/to/lrat-check \
  --assets-dir /absolute/path/to/downloaded-assets
```

`release` checks the public file hashes, all manifests, the outer
implication arithmetic, the order-26 degree-eight classification, the
order-27 degree-sum reduction, all 50 semantic reconstructions and LRAT
proofs, and the corruption suites. Its final line is:

```text
fixed_r9_release_replay=VERIFIED
```

The longer proof-premise replay is:

```sh
./reproduce.sh \
  --mode proof \
  --workers 8 \
  --geng /absolute/path/to/geng \
  --lrat-check /absolute/path/to/lrat-check \
  --assets-dir /absolute/path/to/downloaded-assets
```

This additionally recomputes the solver-free order-26 searches for every
level from 56 through 64. It is intentionally expensive. `--mode audit`
also runs the independent Z3 and CaDiCaL reconstructions and requires the
optional solver dependencies in `requirements.txt`.

## Review status and AI disclosure

This is an unreviewed proof claim posted for independent checking. A
passing replay checks the finite computations. It does not replace review
of the human reductions or cited theorems.

OpenAI GPT-5.6 Sol was used substantially for proof exploration, drafting,
program development, and internal criticism. OpenAI GPT-5 (Codex) was used
for source review, replay packaging, and release checks. The repository-level
[AI disclosure](../AI_DISCLOSURE.md) gives the full statement. Model
agreement is not treated as mathematical review.

Please report a suspected gap with the theorem, page, and exact implication
that fails.
