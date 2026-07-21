#!/usr/bin/env python3
"""Audit the fixed r=9, m=61 incidence frontier with Z3.

This program rebuilds all 111 pairs left by the exact rational duals and
classifies every raw row-size state.  It reuses the generic Boolean encoding
from the pinned m=60 Z3 audit, but does not import the m=61 solver-free dynamic
program or its scalar-side filter.  Z3 is an independent encoding and search
audit, not the proof premise for the m=61 exclusion.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from typing import Any, Iterator, cast

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
Z3_PATH = HERE / "r9_p93_order26_m60_p1_qstate_z3_audit.py"
DUAL_PATH = HERE / "verify_r9_p93_order26_m61_duals.py"
DUAL_DATA = HERE / "r9_p93_order26_m61_duals.jsonl"
SHELL_ORDER = 9
GLOBAL_OFFSET = 16
EXPECTED_COMPLEMENT_PAIRS = 111
EXPECTED_STATES = 29155
EXPECTED_PAIR_PROFILE = Counter(
    {
        1: 16,
        10: 12,
        11: 1,
        55: 12,
        74: 1,
        102: 1,
        117: 2,
        181: 5,
        220: 20,
        221: 6,
        229: 3,
        266: 1,
        275: 2,
        318: 2,
        385: 6,
        386: 2,
        394: 1,
        467: 1,
        670: 2,
        715: 8,
        724: 2,
        725: 1,
        761: 1,
        1227: 1,
        2002: 2,
    }
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "9b11d394ea1bd1f5cad5cc6c37ca721dfea9b3a561f23e0eaabe27b9091aec65"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


Z3_AUDIT = load_module("erdos617_m61_z3_encoding", Z3_PATH)
DUAL = load_module("erdos617_m61_z3_dual_catalog", DUAL_PATH)


def weak_compositions_at_most(
    budget: int, length: int, prefix: tuple[int, ...] = ()
) -> Iterator[tuple[int, ...]]:
    if length == 0:
        yield prefix
        return
    for value in range(budget + 1):
        yield from weak_compositions_at_most(
            budget - value, length - 1, prefix + (value,)
        )


def row_size_states(shell: nx.Graph) -> tuple[tuple[int, ...], ...]:
    budget = GLOBAL_OFFSET - shell.number_of_edges()
    if not 0 <= budget <= 8:
        raise AssertionError("shell scalar budget is outside zero through eight")
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    states = set()
    for epsilon in weak_compositions_at_most(budget, SHELL_ORDER):
        rows = tuple(degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER))
        if all(
            rows[int(first)] + rows[int(second)] >= 8 for first, second in shell.edges
        ):
            states.add(rows)
    return tuple(sorted(states))


Z3_AUDIT.row_size_states = row_size_states


def audit_task(task: tuple[int, int, str, str]) -> tuple[Any, ...]:
    return cast(tuple[Any, ...], Z3_AUDIT.audit_pair(task))


def certified_pairs(
    path: Path,
    cores: tuple[Any, ...],
    shells: tuple[Any, ...],
) -> frozenset[tuple[str, str]]:
    data_hash = hashlib.sha256(path.read_bytes()).hexdigest()
    if data_hash != DUAL.EXPECTED_DATA_SHA256:
        raise AssertionError(f"dual data digest mismatch: {data_hash}")
    lines = tuple(
        line for line in path.read_text(encoding="ascii").splitlines() if line.strip()
    )
    if len(lines) != DUAL.EXPECTED_CERTIFICATES + 1:
        raise AssertionError(f"wrong dual line count: {len(lines)}")
    DUAL.parse_header(json.loads(lines[0]))
    core_names = frozenset(case.graph6.decode("ascii") for case in cores)
    shell_names = frozenset(case.graph6.decode("ascii") for case in shells)
    result = set()
    for line_number, line in enumerate(lines[1:], start=2):
        record = json.loads(line)
        if not isinstance(record, dict) or set(record) != {
            "core",
            "shell",
            "weights",
        }:
            raise AssertionError(f"bad dual record at line {line_number}")
        core_name = record["core"]
        shell_name = record["shell"]
        if core_name not in core_names or shell_name not in shell_names:
            raise AssertionError(f"pair outside catalogs at line {line_number}")
        DUAL.parse_weights(record["weights"])
        pair = core_name, shell_name
        if pair in result:
            raise AssertionError(f"duplicate dual pair at line {line_number}")
        result.add(pair)
    return frozenset(result)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_DATA)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")

    cores = DUAL.generate_cores(args.geng)
    shells = DUAL.generate_shells(args.geng)
    if len(cores) != DUAL.EXPECTED_CORES:
        raise AssertionError(f"wrong core count: {len(cores)}")
    if len(shells) != DUAL.EXPECTED_SHELLS:
        raise AssertionError(f"wrong shell count: {len(shells)}")
    if DUAL.catalog_sha256(cores) != DUAL.EXPECTED_CORE_CATALOG_SHA256:
        raise AssertionError("core catalog digest mismatch")
    if DUAL.catalog_sha256(shells) != DUAL.EXPECTED_SHELL_CATALOG_SHA256:
        raise AssertionError("shell catalog digest mismatch")
    certified = certified_pairs(args.duals, cores, shells)
    complement = tuple(
        (core_index, shell_index)
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (core.graph6.decode("ascii"), shell.graph6.decode("ascii")) not in certified
    )
    if len(complement) != EXPECTED_COMPLEMENT_PAIRS:
        raise AssertionError(f"wrong complement count: {len(complement)}")
    tasks = tuple(
        (
            core_index,
            shell_index,
            cores[core_index].graph6.decode("ascii"),
            shells[shell_index].graph6.decode("ascii"),
        )
        for core_index, shell_index in complement
    )
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
        raise AssertionError(f"unexpected Z3-SAT states: {len(satisfiable)}")
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
    pair_profile = Counter(map(len, nested))
    if pair_profile != EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"pair-profile mismatch: {pair_profile}")
    print(f"cores={len(cores)} shells={len(shells)} complement_pairs={len(complement)}")
    print(f"q_states={len(states)} z3_UNSAT={len(states)} z3_SAT=0 z3_UNKNOWN=0")
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
