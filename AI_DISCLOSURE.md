# AI disclosure

Robert Sneiderman directed the research and is the author of the manuscripts.

## November cutoff and twelve-color manuscript

OpenAI's Astra model in Codex contributed to mathematical proof search, drafting, exact-checker implementation and Lean formalization. Fable contributed fixed-row arguments and internal reviews of earlier stages. The manuscript identifies the statements verified in Lean and the checks reproduced in Python. The two full theorems await independent mathematical review. [Paper and verification guide](cutoff/README.md)

## July fixed-case manuscripts

- **OpenAI GPT-5.6 Sol:** proof search, drafting, checking of reductions and
  case splits, verification-program development, and revisions.
- **OpenAI GPT-5 (Codex):** later source review, compilation, replay
  packaging, file checks, and preparation of the public artifacts.
- **xAI Grok 4.5:** critique of drafts of the r = 5, 6, 7, 8 manuscripts.

AI output is not a correctness certificate, and review by another model is
not external mathematical review. The manuscripts should be read as
unreviewed proof claims.

The mathematical statements and arguments are presented in full in the PDFs.
The r = 5, 6 proofs do not use program output as a premise. The r = 7, 8, 9
proofs are computer-assisted; their finite premises are accompanied by
separate reconstructions, replay scripts, manifests, and proof artifacts.
Readers are invited to report any gap with the exact page, lemma, and line of
reasoning involved.
