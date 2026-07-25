# Fixed r = 9 order-26 levels m = 58 to 61: reconstruction receipt

Date: 24 July 2026

## Scope

`REPLAY_RECEIPT.md` in this directory records a `release` mode run. That
mode deliberately does not rerun the order-26 finite searches or their
separate solver reconstructions. This receipt records those runs for the
four levels whose reconstruction receipts were previously absent from the
package, namely m = 58, 59, 60 and 61.

The verifiers and their independent solver audits were already present
here; only the recorded output was missing. Nothing in the package
changed to produce this receipt.

These reconstructions are audits, not premises. As stated in the r = 9
manuscript, the order-26 exclusion does not depend on them.

## Recorded commands

Run from `r9/package`, with `geng` from nauty and Python 3.13,
networkx 3.4.2, z3-solver 4.16.0.0.

```sh
P=research/erdos-617-r6
for L in 58 59 60 61; do
  python3 $P/verify_r9_p93_order26_m${L}_duals.py \
    --geng "$GENG" --certificates $P/r9_p93_order26_m${L}_duals.jsonl
done

python3 $P/verify_r9_p93_order26_m58_qstates.py --geng "$GENG" --workers 8
python3 $P/r9_p93_order26_m59_p1_qstate_verifier.py --geng "$GENG" --workers 8
python3 $P/r9_p93_order26_m60_p1_exceptional_shell_verifier.py --geng "$GENG"
python3 $P/r9_p93_order26_m60_p1_qstate_verifier.py --geng "$GENG" --workers 8
python3 $P/r9_p93_order26_m61_scalar_side_verifier.py --geng "$GENG"
python3 $P/r9_p93_order26_m61_p1_qstate_verifier.py --geng "$GENG" --workers 8

python3 $P/audit_r9_p93_order26_m58_qstates_z3.py --geng "$GENG" --workers 8
for L in 59 60 61; do
  python3 $P/r9_p93_order26_m${L}_p1_qstate_z3_audit.py --geng "$GENG" --workers 8
done
```

## Results

All fifteen stages passed, with no failures and no undecided states.

```text
m58_duals              PASS      4s
m59_duals              PASS      4s
m60_duals              PASS      9s
m61_duals              PASS     17s
m58_qstates            PASS     35s
m59_qstate             PASS    154s
m60_exceptional_shell  PASS     10s
m60_qstate             PASS    405s
m61_scalar_side        PASS     20s
m61_qstate             PASS   1054s
m58_z3_independent     PASS     14s
m59_z3_independent     PASS     35s
m60_z3_independent     PASS     70s
m61_z3_independent     PASS    229s
uniform_m58_m64_core_arithmetic=VERIFIED
```

Independent solver reconstructions:

```text
m58  cores=50 shells=55 remaining_pairs=892
     q_states=5056  UNSAT=4981  SAT=75  UNKNOWN=0
     boundary_q_states=274  boundary_SAT=75  forcing_side_models_verified=75
     classification_sha256=0dff9f3a707e730c3a31e880de7ce32a38404e7b7a92ba4355ec7c97a04d6938

m59  cores=20 shells=85 remaining_pairs=465
     q_states=11943 UNSAT=11943 SAT=0 UNKNOWN=0
     classification_sha256=688ba89fcb69a6ca76cc8607dd4aaba4cebd4850367d2b9946919648a55067c8

m60  cores=10 shells=152 remainder_pairs=230 selected_pairs=220
     q_states=23157 UNSAT=23157 SAT=0 UNKNOWN=0
     classification_sha256=1454b3bb20347bad1cf4e064c0414151c863caa7b4695c168f8f34cc3548fa21

m61  cores=4 shells=393 complement_pairs=111
     q_states=29155 UNSAT=29155 SAT=0 UNKNOWN=0
     classification_sha256=9b11d394ea1bd1f5cad5cc6c37ca721dfea9b3a561f23e0eaabe27b9091aec65
```

Level m = 58 is not an all-UNSAT level. Seventy-five of its 5,056
q-states are satisfiable, all of them inside the 274 boundary states, and
each is accompanied by a verified forcing-side model. The level returns
PASS on that basis. Levels m = 59, 60 and 61 are all-UNSAT. No state was
left undecided at any level.
