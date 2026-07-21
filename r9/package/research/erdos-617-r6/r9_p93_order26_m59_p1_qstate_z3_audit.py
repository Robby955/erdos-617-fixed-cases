#!/usr/bin/env python3
"""Cross-check the r=9, m=59 p=1 finite search with Z3.

This audit reconstructs the row-size states and Boolean incidence model
without importing the solver-free dynamic program.  Z3 is an independent
classification audit, not the proof of the 11,943 UNSAT states.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from typing import Any

import networkx as nx  # type: ignore[import-untyped]
import z3  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
CATALOG_PATH = HERE / "verify_r9_p93_order26_m59_duals.py"
DUAL_PATH = HERE / "r9_p93_order26_m59_duals.jsonl"
CORE_ORDER = 16
SHELL_ORDER = 9
FULL_CORE_MASK = (1 << CORE_ORDER) - 1
GLOBAL_OFFSET = 14
EXPECTED_CORES = 20
EXPECTED_SHELLS = 85
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_DUAL_PAIRS = 1235
EXPECTED_REMAINING_PAIRS = 465
EXPECTED_Q_STATES = 11943
EXPECTED_CLASSIFICATION_SHA256 = (
    "688ba89fcb69a6ca76cc8607dd4aaba4cebd4850367d2b9946919648a55067c8"
)


def load_catalog() -> Any:
    spec = importlib.util.spec_from_file_location(
        "r9_m59_p1_z3_catalog", CATALOG_PATH
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CATALOG_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


CATALOG = load_catalog()


@dataclass(frozen=True)
class StateResult:
    core_index: int
    shell_index: int
    row_sizes: tuple[int, ...]
    satisfiable: bool


@dataclass(frozen=True)
class CoreResult:
    core_index: int
    states: tuple[StateResult, ...]


def weak_compositions_at_most(
    budget: int, length: int
) -> tuple[tuple[int, ...], ...]:
    result: list[tuple[int, ...]] = []

    def extend(prefix: tuple[int, ...], remaining: int) -> None:
        if len(prefix) == length:
            result.append(prefix)
            return
        for value in range(remaining + 1):
            extend(prefix + (value,), remaining - value)

    extend((), budget)
    return tuple(result)


def row_size_states(shell: nx.Graph) -> tuple[tuple[int, ...], ...]:
    budget = GLOBAL_OFFSET - shell.number_of_edges()
    if not 0 <= budget <= 6:
        raise AssertionError("shell scalar budget is outside zero through six")
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    states = set()
    for epsilon in weak_compositions_at_most(budget, SHELL_ORDER):
        row_sizes = tuple(
            degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER)
        )
        if all(
            row_sizes[first] + row_sizes[second] >= 8
            for first, second in shell.edges
        ):
            states.add(row_sizes)
    return tuple(sorted(states))


def read_dual_pairs(
    path: Path,
    core_names: frozenset[str],
    shell_names: frozenset[str],
) -> frozenset[tuple[str, str]]:
    lines = tuple(
        line for line in path.read_text(encoding="ascii").splitlines() if line.strip()
    )
    if len(lines) != EXPECTED_DUAL_PAIRS + 1:
        raise AssertionError(f"wrong dual line count: {len(lines)}")
    header = json.loads(lines[0])
    expected_header = {
        "schema": "erdos617-r9-m59-duals-v1",
        "core_count": EXPECTED_CORES,
        "shell_count": EXPECTED_SHELLS,
        "pair_count": EXPECTED_PAIRS,
        "certificate_count": EXPECTED_DUAL_PAIRS,
        "uncertified_pair_count": EXPECTED_REMAINING_PAIRS,
        "core_catalog_sha256": CATALOG.EXPECTED_CORE_CATALOG_SHA256,
        "shell_catalog_sha256": CATALOG.EXPECTED_SHELL_CATALOG_SHA256,
        "nonclaim": CATALOG.NONCLAIM,
    }
    if header != expected_header:
        raise AssertionError(f"dual header mismatch: {header}")
    pairs = set()
    for line_number, line in enumerate(lines[1:], start=2):
        record = json.loads(line)
        if not isinstance(record, dict) or set(record) != {
            "core",
            "shell",
            "weights",
        }:
            raise AssertionError(f"bad dual record at line {line_number}")
        core = record["core"]
        shell = record["shell"]
        if not isinstance(core, str) or not isinstance(shell, str):
            raise AssertionError(f"non-string dual pair at line {line_number}")
        if core not in core_names or shell not in shell_names:
            raise AssertionError(f"dual pair outside catalogs at line {line_number}")
        pair = (core, shell)
        if pair in pairs:
            raise AssertionError(f"duplicate dual pair at line {line_number}")
        pairs.add(pair)
    return frozenset(pairs)


def adjacency_masks(graph: nx.Graph) -> tuple[int, ...]:
    masks = [0] * graph.number_of_nodes()
    for raw_first, raw_second in graph.edges:
        first = int(raw_first)
        second = int(raw_second)
        masks[first] |= 1 << second
        masks[second] |= 1 << first
    return tuple(masks)


def independent(mask: int, adjacency: tuple[int, ...]) -> bool:
    remaining = mask
    while remaining:
        bit = remaining & -remaining
        vertex = bit.bit_length() - 1
        if adjacency[vertex] & mask:
            return False
        remaining ^= bit
    return True


def bipartition_masks(core: nx.Graph) -> tuple[int, int]:
    if not nx.is_bipartite(core):
        raise AssertionError("m=59 core is not bipartite")
    colours = nx.algorithms.bipartite.color(core)
    first = sum(
        1 << int(vertex) for vertex, colour in colours.items() if colour == 0
    )
    second = FULL_CORE_MASK ^ first
    if first.bit_count() != 8 or second.bit_count() != 8:
        raise AssertionError("m=59 core does not have an 8+8 bipartition")
    adjacency = adjacency_masks(core)
    independent_eights = set()
    for vertices in itertools.combinations(range(CORE_ORDER), 8):
        mask = sum(1 << vertex for vertex in vertices)
        if independent(mask, adjacency):
            independent_eights.add(mask)
    if independent_eights != {first, second}:
        raise AssertionError("core sides are not its only independent eight-sets")
    return first, second


def triangles(shell: nx.Graph) -> tuple[tuple[int, int, int], ...]:
    return tuple(
        vertices
        for vertices in itertools.combinations(range(SHELL_ORDER), 3)
        if all(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(vertices, 2)
        )
    )


def model_rows(
    model: z3.ModelRef,
    variables: tuple[tuple[z3.BoolRef, ...], ...],
) -> tuple[int, ...]:
    return tuple(
        sum(
            1 << core_vertex
            for core_vertex, variable in enumerate(row)
            if z3.is_true(model.eval(variable, model_completion=True))
        )
        for row in variables
    )


def verify_sat_model(
    core: nx.Graph,
    shell: nx.Graph,
    row_sizes: tuple[int, ...],
    rows: tuple[int, ...],
    sides: tuple[int, int],
) -> None:
    if tuple(row.bit_count() for row in rows) != row_sizes:
        raise AssertionError("Z3 model violates an exact row size")
    adjacency = adjacency_masks(core)
    for first, second in shell.edges:
        cover = rows[int(first)] | rows[int(second)]
        if not independent(FULL_CORE_MASK ^ cover, adjacency):
            raise AssertionError("Z3 model violates a row-pair cover")
    for triangle in triangles(shell):
        if rows[triangle[0]] | rows[triangle[1]] | rows[triangle[2]] != FULL_CORE_MASK:
            raise AssertionError("Z3 model violates a triangle column")
    for vertex in range(CORE_ORDER):
        incidence = sum((row >> vertex) & 1 for row in rows)
        if incidence < max(0, int(core.degree(vertex)) - 6):
            raise AssertionError("Z3 model violates a column demand")
    for row in rows:
        if any(row & side == side for side in sides):
            raise AssertionError("Z3 model violates the p=1 target-K9 condition")


def solve_pair(
    core: nx.Graph,
    shell: nx.Graph,
    core_index: int,
    shell_index: int,
) -> tuple[StateResult, ...]:
    variables = tuple(
        tuple(
            z3.Bool(f"x_{shell_vertex}_{core_vertex}")
            for core_vertex in range(CORE_ORDER)
        )
        for shell_vertex in range(SHELL_ORDER)
    )
    solver = z3.Solver()
    for core_vertex in range(CORE_ORDER):
        demand = max(0, int(core.degree(core_vertex)) - 6)
        solver.add(
            z3.PbGe(
                [
                    (variables[shell_vertex][core_vertex], 1)
                    for shell_vertex in range(SHELL_ORDER)
                ],
                demand,
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
    for triangle in triangles(shell):
        for core_vertex in range(CORE_ORDER):
            solver.add(
                z3.Or(
                    *(variables[shell_vertex][core_vertex] for shell_vertex in triangle)
                )
            )
    sides = bipartition_masks(core)
    for shell_vertex in range(SHELL_ORDER):
        for side in sides:
            solver.add(
                z3.PbLe(
                    [
                        (variables[shell_vertex][core_vertex], 1)
                        for core_vertex in range(CORE_ORDER)
                        if side >> core_vertex & 1
                    ],
                    7,
                )
            )

    results = []
    for row_sizes in row_size_states(shell):
        solver.push()
        for shell_vertex in range(SHELL_ORDER):
            solver.add(
                z3.PbEq(
                    [
                        (variables[shell_vertex][core_vertex], 1)
                        for core_vertex in range(CORE_ORDER)
                    ],
                    row_sizes[shell_vertex],
                )
            )
        status = solver.check()
        if status == z3.unknown:
            raise AssertionError(f"Z3 returned unknown: {solver.reason_unknown()}")
        satisfiable = status == z3.sat
        if satisfiable:
            rows = model_rows(solver.model(), variables)
            verify_sat_model(core, shell, row_sizes, rows, sides)
        results.append(
            StateResult(core_index, shell_index, row_sizes, satisfiable)
        )
        solver.pop()
    return tuple(results)


def audit_core(
    task: tuple[int, str, tuple[tuple[int, str], ...]],
) -> CoreResult:
    core_index, core_name, shell_entries = task
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    states: list[StateResult] = []
    for shell_index, shell_name in shell_entries:
        shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
        states.extend(solve_pair(core, shell, core_index, shell_index))
    return CoreResult(core_index, tuple(states))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_PATH)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")

    cores = CATALOG.generate_cores(args.geng)
    shells = CATALOG.generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        raise AssertionError(
            f"catalog mismatch: cores={len(cores)} shells={len(shells)}"
        )
    core_names = frozenset(case.graph6.decode("ascii") for case in cores)
    shell_names = frozenset(case.graph6.decode("ascii") for case in shells)
    dual_pairs = read_dual_pairs(args.duals, core_names, shell_names)

    tasks = []
    remaining_pairs = 0
    for core_index, core_case in enumerate(cores):
        core_name = core_case.graph6.decode("ascii")
        entries = []
        for shell_index, shell_case in enumerate(shells):
            shell_name = shell_case.graph6.decode("ascii")
            if (core_name, shell_name) in dual_pairs:
                continue
            entries.append((shell_index, shell_name))
            remaining_pairs += 1
        tasks.append((core_index, core_name, tuple(entries)))
    if remaining_pairs != EXPECTED_REMAINING_PAIRS:
        raise AssertionError(f"wrong remaining-pair count: {remaining_pairs}")

    if args.workers == 1:
        core_results = tuple(audit_core(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            core_results = tuple(pool.map(audit_core, tasks))
    core_results = tuple(sorted(core_results, key=lambda result: result.core_index))
    states = tuple(state for result in core_results for state in result.states)
    satisfiable = tuple(state for state in states if state.satisfiable)
    if len(states) != EXPECTED_Q_STATES:
        raise AssertionError(f"wrong q-state count: {len(states)}")
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
        raise AssertionError(
            "classification digest mismatch: "
            f"{classification_sha256} != {EXPECTED_CLASSIFICATION_SHA256}"
        )
    pair_state_profile = Counter(
        sum(
            state.core_index == core_index and state.shell_index == shell_index
            for state in states
        )
        for core_index, _, entries in tasks
        for shell_index, _ in entries
    )
    print(
        f"cores={len(cores)} shells={len(shells)} "
        f"remaining_pairs={remaining_pairs}"
    )
    print(
        f"q_states={len(states)} z3_UNSAT={len(states)} "
        "z3_SAT=0 z3_UNKNOWN=0"
    )
    print(f"pair_q_state_profile={dict(sorted(pair_state_profile.items()))}")
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
