#!/usr/bin/env python3
"""Independently reconstruct all raw m=63 incidence states with Z3.

This program does not import the scalar filter or the orbit search.  It
rebuilds every one of the 334 exact-dual complement pairs and sends all
44,504 raw row-size states to a separate Boolean encoding.
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
import z3  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
Z3_PATH = HERE / "r9_p93_order26_m60_p1_qstate_z3_audit.py"
DUAL_PATH = HERE / "verify_r9_p93_order26_m63_duals.py"
DUAL_DATA = HERE / "r9_p93_order26_m63_duals.jsonl"
SHELL_ORDER = 9
GLOBAL_OFFSET = 18
EXPECTED_COMPLEMENT_PAIRS = 334
EXPECTED_STATES = 44504
EXPECTED_COMPLEMENT_BUDGET_PROFILE = Counter(
    {0: 9, 1: 17, 2: 36, 3: 63, 4: 92, 5: 111, 6: 6}
)
EXPECTED_PAIR_PROFILE: Counter[int] = Counter(
    {
        1: 29,
        2: 20,
        3: 6,
        4: 13,
        5: 5,
        6: 4,
        8: 3,
        10: 28,
        11: 26,
        12: 10,
        13: 4,
        19: 21,
        20: 11,
        21: 10,
        22: 5,
        23: 1,
        24: 1,
        28: 5,
        29: 1,
        30: 1,
        31: 2,
        36: 8,
        37: 5,
        38: 1,
        40: 2,
        46: 4,
        53: 2,
        55: 12,
        56: 8,
        57: 1,
        64: 4,
        65: 10,
        66: 3,
        67: 2,
        68: 1,
        70: 1,
        74: 4,
        75: 2,
        76: 1,
        78: 1,
        81: 2,
        100: 6,
        101: 2,
        102: 3,
        110: 1,
        111: 1,
        117: 2,
        119: 2,
        126: 1,
        136: 1,
        145: 1,
        148: 1,
        181: 1,
        190: 2,
        220: 6,
        229: 2,
        239: 1,
        265: 1,
        274: 2,
        275: 1,
        402: 1,
        550: 1,
        715: 3,
        724: 1,
        880: 1,
        2002: 4,
        2011: 1,
        2035: 1,
        2047: 1,
        3289: 1,
        5005: 2,
    }
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "81e6fdb89bde8d4b1663fee7cca85cd4bbf3e8091ec1746ec045d8faa2357f2f"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


Z3_AUDIT = load_module("erdos617_m63_z3_encoding", Z3_PATH)
DUAL = load_module("erdos617_m63_z3_catalog", DUAL_PATH)


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
    if not 0 <= budget <= 6:
        raise AssertionError("m=63 shell budget lies outside zero through six")
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    states = set()
    for epsilon in weak_compositions_at_most(budget, SHELL_ORDER):
        rows = tuple(degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER))
        if all(rows[int(first)] + rows[int(second)] >= 8 for first, second in shell.edges):
            states.add(rows)
    return tuple(sorted(states))


Z3_AUDIT.row_size_states = row_size_states


def cover13_sides(core: nx.Graph) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Return the two sides after checking the K_8,8-minus-one premise."""

    if core.number_of_nodes() != 16 or core.number_of_edges() != 63:
        raise AssertionError("cover-13 core has the wrong order or size")
    if not nx.is_bipartite(core):
        raise AssertionError("cover-13 core is not bipartite")
    coloring = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(sorted(int(vertex) for vertex, color in coloring.items() if color == side))
        for side in (0, 1)
    )
    if tuple(sorted(map(len, sides))) != (8, 8):
        raise AssertionError("cover-13 core does not have two sides of order eight")
    missing = sum(
        not core.has_edge(first, second)
        for first in sides[0]
        for second in sides[1]
    )
    if missing != 1:
        raise AssertionError("cover-13 core is not K8,8 minus one edge")
    return cast(tuple[tuple[int, ...], tuple[int, ...]], sides)


def solve_pair_with_cover13(
    core: nx.Graph,
    shell: nx.Graph,
    core_index: int,
    shell_index: int,
    row_states: tuple[tuple[int, ...], ...],
) -> tuple[Any, ...]:
    """Rebuild the Boolean model with the proved cover-13 consequence.

    A shell-edge row union is a vertex cover of the core.  If the two row
    sizes sum to at most thirteen, that union has order at most thirteen.
    Every such cover of K_8,8 minus one edge contains a full side.  Adding
    this redundant constraint makes the independent audit reproducible on
    the hard raw states without changing its satisfying assignments.
    """

    sides = cover13_sides(core)
    variables = tuple(
        tuple(
            z3.Bool(f"x_{shell_vertex}_{core_vertex}")
            for core_vertex in range(Z3_AUDIT.CORE_ORDER)
        )
        for shell_vertex in range(SHELL_ORDER)
    )
    solver = z3.Solver()
    for core_vertex in range(Z3_AUDIT.CORE_ORDER):
        solver.add(
            z3.PbGe(
                [
                    (variables[shell_vertex][core_vertex], 1)
                    for shell_vertex in range(SHELL_ORDER)
                ],
                max(0, int(core.degree(core_vertex)) - 6),
            )
        )
    for raw_first_shell, raw_second_shell in shell.edges:
        first_shell = int(raw_first_shell)
        second_shell = int(raw_second_shell)
        for raw_first_core, raw_second_core in core.edges:
            first_core = int(raw_first_core)
            second_core = int(raw_second_core)
            solver.add(
                z3.Or(
                    variables[first_shell][first_core],
                    variables[first_shell][second_core],
                    variables[second_shell][first_core],
                    variables[second_shell][second_core],
                )
            )
    for triangle in Z3_AUDIT.triangles(shell):
        for core_vertex in range(Z3_AUDIT.CORE_ORDER):
            solver.add(
                z3.Or(
                    *(variables[shell_vertex][core_vertex] for shell_vertex in triangle)
                )
            )
    for shell_vertex in range(SHELL_ORDER):
        for side in sides:
            solver.add(
                z3.PbLe(
                    [
                        (variables[shell_vertex][core_vertex], 1)
                        for core_vertex in side
                    ],
                    7,
                )
            )

    results = []
    for row_sizes in row_states:
        solver.push()
        for shell_vertex in range(SHELL_ORDER):
            solver.add(
                z3.PbEq(
                    [
                        (variables[shell_vertex][core_vertex], 1)
                        for core_vertex in range(Z3_AUDIT.CORE_ORDER)
                    ],
                    row_sizes[shell_vertex],
                )
            )
        for raw_first, raw_second in shell.edges:
            first = int(raw_first)
            second = int(raw_second)
            if row_sizes[first] + row_sizes[second] > 13:
                continue
            solver.add(
                z3.Or(
                    *(
                        z3.And(
                            *(
                                z3.Or(
                                    variables[first][core_vertex],
                                    variables[second][core_vertex],
                                )
                                for core_vertex in side
                            )
                        )
                        for side in sides
                    )
                )
            )
        status = solver.check()
        if status == z3.unknown:
            raise AssertionError(f"Z3 returned unknown: {solver.reason_unknown()}")
        satisfiable = status == z3.sat
        if satisfiable:
            rows = Z3_AUDIT.model_rows(solver.model(), variables)
            side_masks = tuple(sum(1 << vertex for vertex in side) for side in sides)
            Z3_AUDIT.verify_sat_model(core, shell, row_sizes, rows, side_masks)
            for raw_first, raw_second in shell.edges:
                first = int(raw_first)
                second = int(raw_second)
                if row_sizes[first] + row_sizes[second] <= 13 and not any(
                    (rows[first] | rows[second]) & mask == mask for mask in side_masks
                ):
                    raise AssertionError("Z3 model violates the cover-13 consequence")
        results.append(
            Z3_AUDIT.StateResult(core_index, shell_index, row_sizes, satisfiable)
        )
        solver.pop()
    return tuple(results)


def audit_task(
    task: tuple[int, int, str, str, tuple[tuple[int, ...], ...]],
) -> tuple[Any, ...]:
    """Audit one deterministic row-state chunk with a fresh Z3 solver.

    Chunking prevents one large shell from occupying a single worker while
    preserving the separate Boolean encoding.
    """

    core_index, shell_index, core_name, shell_name, row_states = task
    return solve_pair_with_cover13(
        nx.from_graph6_bytes(core_name.encode("ascii")),
        nx.from_graph6_bytes(shell_name.encode("ascii")),
        core_index,
        shell_index,
        row_states,
    )


def certified_pairs(
    path: Path, cores: tuple[Any, ...], shells: tuple[Any, ...]
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
        if not isinstance(record, dict) or set(record) != {"core", "shell", "weights"}:
            raise AssertionError(f"bad dual record at line {line_number}")
        pair = record["core"], record["shell"]
        if pair[0] not in core_names or pair[1] not in shell_names:
            raise AssertionError(f"pair outside catalogs at line {line_number}")
        DUAL.parse_weights(record["weights"])
        if pair in result:
            raise AssertionError(f"duplicate dual pair at line {line_number}")
        result.add(pair)
    return frozenset(result)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_DATA)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--chunk-size", type=int, default=512)
    parser.add_argument("--allow-unpinned", action="store_true")
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")
    if args.chunk_size <= 0:
        parser.error("--chunk-size must be positive")

    cores = DUAL.generate_cores(args.geng)
    shells = DUAL.generate_shells(args.geng)
    if len(cores) != DUAL.EXPECTED_CORES or len(shells) != DUAL.EXPECTED_SHELLS:
        raise AssertionError("catalog count mismatch")
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
    budget_profile = Counter(
        GLOBAL_OFFSET - shells[shell_index].graph.number_of_edges()
        for _, shell_index in complement
    )
    if budget_profile != EXPECTED_COMPLEMENT_BUDGET_PROFILE:
        raise AssertionError(f"complement budget profile mismatch: {budget_profile}")
    pair_groups = tuple(
        (
            core_index,
            shell_index,
            cores[core_index].graph6.decode("ascii"),
            shells[shell_index].graph6.decode("ascii"),
            row_size_states(shells[shell_index].graph),
        )
        for core_index, shell_index in complement
    )
    pair_profile = Counter(len(group[4]) for group in pair_groups)
    if sum(len(group[4]) for group in pair_groups) != EXPECTED_STATES:
        raise AssertionError("wrong pre-solver row-state count")
    tasks = tuple(
        (core_index, shell_index, core_name, shell_name, row_states[offset:end])
        for core_index, shell_index, core_name, shell_name, row_states in pair_groups
        for offset in range(0, len(row_states), args.chunk_size)
        for end in (min(len(row_states), offset + args.chunk_size),)
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
        for state in sorted(states, key=lambda item: (item.core_index, item.shell_index, item.row_sizes))
    ).encode("ascii")
    classification_sha256 = hashlib.sha256(classification).hexdigest()
    if not args.allow_unpinned:
        if pair_profile != EXPECTED_PAIR_PROFILE:
            raise AssertionError(f"pair profile mismatch: {pair_profile}")
        if classification_sha256 != EXPECTED_CLASSIFICATION_SHA256:
            raise AssertionError(f"classification digest mismatch: {classification_sha256}")
    print(f"cores={len(cores)} shells={len(shells)} complement_pairs={len(complement)}")
    print(f"complement_budget_profile={dict(sorted(budget_profile.items()))}")
    print(f"chunks={len(tasks)} chunk_size={args.chunk_size}")
    print("cover13_redundant_constraints=enabled")
    print(f"q_states={len(states)} z3_UNSAT={len(states)} z3_SAT=0 z3_UNKNOWN=0")
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
