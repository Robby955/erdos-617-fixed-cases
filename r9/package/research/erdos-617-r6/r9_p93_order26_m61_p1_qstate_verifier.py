#!/usr/bin/env python3
"""Verify the solver-free two-hub remainder for fixed r=9 and m=61.

The exact-dual and scalar-side verifiers exclude every complementary pair
except 81 two-hub pairs.  This checker reconstructs all 82 two-hub pairs,
including one already excluded by the scalar test, applies the scalar filter,
and exhausts the resulting 8,531 row-size states with the solver-free dynamic
program imported from the independently pinned m=60 checker.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import hashlib
import importlib.util
from pathlib import Path
import sys
from typing import Any

HERE = Path(__file__).resolve().parent
QSTATE_PATH = HERE / "r9_p93_order26_m60_p1_qstate_verifier.py"
SCALAR_PATH = HERE / "r9_p93_order26_m61_scalar_side_verifier.py"
DUAL_DATA = HERE / "r9_p93_order26_m61_duals.jsonl"
EXPECTED_COMPLEMENT_PAIRS = 111
EXPECTED_PAIRS = 82
EXPECTED_STATES = 8531
EXPECTED_HUB_PAIRS_EXAMINED = 1663514400
EXPECTED_DEMAND_STATES_EXAMINED = 936689030
EXPECTED_PAIR_PROFILE = Counter(
    {
        0: 1,
        3: 1,
        10: 4,
        36: 4,
        37: 2,
        43: 3,
        52: 12,
        54: 2,
        55: 22,
        128: 2,
        155: 3,
        193: 4,
        206: 6,
        208: 2,
        216: 6,
        219: 2,
        220: 6,
    }
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "30fb0bb76a200e956904e908acf36475c3b5e66fd4afed85922f165eb94758b8"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


QSTATE = load_module("erdos617_m61_twohub_qstate", QSTATE_PATH)
QSTATE.GLOBAL_OFFSET = 16
SCALAR = load_module("erdos617_m61_twohub_scalar", SCALAR_PATH)


def audit_task(task: tuple[int, int, str, str]) -> tuple[Any, ...]:
    core_index, shell_index, core_name, shell_name = task
    core = QSTATE.nx.from_graph6_bytes(core_name.encode("ascii"))
    shell = QSTATE.nx.from_graph6_bytes(shell_name.encode("ascii"))
    search = QSTATE.P1CoreSearch(core)
    demand_x, demand_y = SCALAR.side_demands(core)
    results = []
    for row_sizes in QSTATE.row_size_states(shell):
        if not SCALAR.feasible_side_counts(shell, row_sizes, demand_x, demand_y):
            continue
        receipt = search.solve(shell, row_sizes)
        results.append(
            QSTATE.StateReceipt(
                core_index,
                shell_index,
                row_sizes,
                receipt.satisfiable,
                receipt.hub_pairs,
                receipt.demand_states,
            )
        )
    return tuple(results)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_DATA)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")

    cores = SCALAR.DUAL.generate_cores(args.geng)
    shells = SCALAR.DUAL.generate_shells(args.geng)
    certified = SCALAR.certified_pairs(args.duals, cores, shells)
    complement = tuple(
        (core_index, shell_index)
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (core.graph6.decode("ascii"), shell.graph6.decode("ascii")) not in certified
    )
    if len(complement) != EXPECTED_COMPLEMENT_PAIRS:
        raise AssertionError(f"wrong complement count: {len(complement)}")
    tasks = []
    for core_index, shell_index in complement:
        shell = shells[shell_index].graph
        if SCALAR.vertex_cover_number(shell) != 2:
            continue
        tasks.append(
            (
                core_index,
                shell_index,
                cores[core_index].graph6.decode("ascii"),
                shells[shell_index].graph6.decode("ascii"),
            )
        )
    if len(tasks) != EXPECTED_PAIRS:
        raise AssertionError(f"wrong task count: {len(tasks)}")
    if args.workers == 1:
        nested = tuple(audit_task(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            nested = tuple(pool.map(audit_task, tasks))
    states = tuple(state for group in nested for state in group)
    if len(states) != EXPECTED_STATES:
        raise AssertionError(f"wrong state count: {len(states)}")
    satisfiable = tuple(state for state in states if state.satisfiable)
    if satisfiable:
        raise AssertionError(f"unexpected p1-SAT states: {len(satisfiable)}")
    classification = "".join(
        f"{state.core_index}:{state.shell_index}:"
        f"{','.join(map(str, state.row_sizes))}:{int(state.satisfiable)}\n"
        for state in sorted(
            states,
            key=lambda item: (item.core_index, item.shell_index, item.row_sizes),
        )
    ).encode("ascii")
    classification_sha256 = hashlib.sha256(classification).hexdigest()
    if classification_sha256 != EXPECTED_CLASSIFICATION_SHA256:
        raise AssertionError(f"classification digest mismatch: {classification_sha256}")
    pair_profile = Counter(len(group) for group in nested)
    if pair_profile != EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"pair-profile mismatch: {pair_profile}")
    hub_pairs_examined = sum(state.hub_pairs for state in states)
    demand_states_examined = sum(state.demand_states for state in states)
    if hub_pairs_examined != EXPECTED_HUB_PAIRS_EXAMINED:
        raise AssertionError(f"hub-pair count mismatch: {hub_pairs_examined}")
    if demand_states_examined != EXPECTED_DEMAND_STATES_EXAMINED:
        raise AssertionError(f"demand-state count mismatch: {demand_states_examined}")
    print(f"two_hub_pairs={len(tasks)} scalar_feasible_states={len(states)}")
    print(
        f"q_states={len(states)} p1_UNSAT={len(states) - len(satisfiable)} "
        f"p1_SAT={len(satisfiable)}"
    )
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"hub_pairs_examined={hub_pairs_examined}")
    print(f"demand_states_examined={demand_states_examined}")
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
