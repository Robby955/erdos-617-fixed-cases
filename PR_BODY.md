The r=9 directory carries a replay receipt and the r=7,8 directory does not. This adds one for r=7,8, recording a clean-clone run of `reproduce.sh` with the pinned `lrat-check`: the weighted light-edge enumeration over 12,618,770 configurations, its independent Sage and nauty reconstruction, the endpoint18 replay, and all 861 indexed degree-eight pair replays, ending at `fixed_r7_r8_release_replay=VERIFIED`.

The `release` mode for r=9 deliberately does not rerun the order-26 finite searches, so the reconstruction output for levels m=58 to 61 was absent from the package even though the verifiers and their solver audits were already present. This adds that output: fifteen stages, no failures, no undecided states, with the classification hash for each level.

Level m=58 is recorded as it is rather than smoothed. Seventy-five of its 5,056 q-states are satisfiable boundary states, each accompanied by a verified forcing-side model, and the level returns PASS on that basis. Levels m=59, 60 and 61 are all-UNSAT.

Both receipts record reproductions. Neither is external review, and neither changes what the package claims. The checksum files each gain one line and both still validate.
