# Fixed r = 9 case of Erdős Problem 617

This release records the following computer-assisted proof claim:

> Every nine-coloring of the edges of K₈₂ has ten vertices whose induced
> edges omit at least one color.

The paper contains the human reduction from the coloring problem. The proof
package contains exact rational-dual data, deterministic finite-state
searches, independent catalogue reconstruction, semantic checks, corruption
tests, manifests, and 50 LRAT refutations for the final order-27 branch.

The four large certificate archives are separate release assets. Their names,
sizes, and SHA-256 values are recorded in `r9/ASSET_INDEX.json` and
`r9/RELEASE_ASSET_SHA256SUMS`.

This release proves only the fixed `r = 9` case. It does not settle Erdős
Problem 617 for arbitrary `r`, and it has not received external mathematical
review.

OpenAI GPT-5.6 Sol was used substantially during proof exploration, drafting,
program development, and internal criticism. OpenAI GPT-5 (Codex) was used
for source review, replay packaging, and release checks. The author assumes
responsibility for every claim and error.
