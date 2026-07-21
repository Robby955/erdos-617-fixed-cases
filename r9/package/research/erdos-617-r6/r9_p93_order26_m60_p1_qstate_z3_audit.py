#!/usr/bin/env python3
"""Audit the r=9, m=60 p=1 q-state classification with Z3.

This audit consumes the canonical exact-dual package but reconstructs the
Boolean incidence search independently of the solver-free dynamic program.
Z3 is an encoding and search audit, not the proof of the UNSAT states.
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
DUAL_MODULE_PATH = HERE / "verify_r9_p93_order26_m60_duals.py"
DUAL_PATH = HERE / "r9_p93_order26_m60_duals.jsonl"
CORE_ORDER = 16
SHELL_ORDER = 9
FULL_CORE_MASK = (1 << CORE_ORDER) - 1
GLOBAL_OFFSET = 15
EXPECTED_CORES = 10
EXPECTED_SHELLS = 152
EXPECTED_DUAL_PAIRS = 1290
EXPECTED_REMAINDER_PAIRS = 230
EXPECTED_SELECTED_PAIRS = 220
EXPECTED_Q_STATES = 23157
EXPECTED_CLASSIFICATION_SHA256 = (
    "1454b3bb20347bad1cf4e064c0414151c863caa7b4695c168f8f34cc3548fa21"
)


def load_module(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


DUAL = load_module("r9_m60_p1_z3_dual_catalog", DUAL_MODULE_PATH)


@dataclass(frozen=True)
class StateResult:
    core_index: int
    shell_index: int
    row_sizes: tuple[int, ...]
    satisfiable: bool


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
    if not 0 <= budget <= 7:
        raise AssertionError("shell scalar budget is outside zero through seven")
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


def has_two_vertex_edge_cover(shell: nx.Graph) -> bool:
    return any(
        all(first in pair or second in pair for first, second in shell.edges)
        for pair in itertools.combinations(range(SHELL_ORDER), 2)
    )


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
        raise AssertionError("m=60 core is not bipartite")
    colours = nx.algorithms.bipartite.color(core)
    first = sum(
        1 << int(vertex) for vertex, colour in colours.items() if colour == 0
    )
    second = FULL_CORE_MASK ^ first
    if first.bit_count() != 8 or second.bit_count() != 8:
        raise AssertionError("m=60 core does not have an 8+8 bipartition")
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
    for core_vertex in range(CORE_ORDER):
        incidence = sum((row >> core_vertex) & 1 for row in rows)
        if incidence < max(0, int(core.degree(core_vertex)) - 6):
            raise AssertionError("Z3 model violates a column demand")
    for row in rows:
        if any(row & side == side for side in sides):
            raise AssertionError("Z3 model violates a p=1 side cap")


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
            side_vertices = tuple(
                core_vertex
                for core_vertex in range(CORE_ORDER)
                if side >> core_vertex & 1
            )
            if len(side_vertices) != 8:
                raise AssertionError("p=1 side cap does not have eight literals")
            solver.add(
                z3.PbLe(
                    [
                        (variables[shell_vertex][core_vertex], 1)
                        for core_vertex in side_vertices
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
            verify_sat_model(
                core,
                shell,
                row_sizes,
                model_rows(solver.model(), variables),
                sides,
            )
        results.append(StateResult(core_index, shell_index, row_sizes, satisfiable))
        solver.pop()
    return tuple(results)


def audit_pair(
    task: tuple[int, int, str, str],
) -> tuple[StateResult, ...]:
    core_index, shell_index, core_name, shell_name = task
    core = nx.from_graph6_bytes(core_name.encode("ascii"))
    shell = nx.from_graph6_bytes(shell_name.encode("ascii"))
    return solve_pair(core, shell, core_index, shell_index)


def read_certified_pairs(
    path: Path,
    cores: tuple[Any, ...],
    shells: tuple[Any, ...],
) -> frozenset[tuple[str, str]]:
    data_sha256 = hashlib.sha256(path.read_bytes()).hexdigest()
    if data_sha256 != DUAL.EXPECTED_DATA_SHA256:
        raise AssertionError(f"dual data digest mismatch: {data_sha256}")
    lines = tuple(
        line for line in path.read_text(encoding="ascii").splitlines() if line.strip()
    )
    if len(lines) != EXPECTED_DUAL_PAIRS + 1:
        raise AssertionError(f"wrong dual line count: {len(lines)}")
    DUAL.parse_header(json.loads(lines[0]))
    core_names = frozenset(case.graph6.decode("ascii") for case in cores)
    shell_names = frozenset(case.graph6.decode("ascii") for case in shells)
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
        if core not in core_names or shell not in shell_names:
            raise AssertionError(f"dual pair outside catalogs at line {line_number}")
        pair = core, shell
        if pair in pairs:
            raise AssertionError(f"duplicate dual pair at line {line_number}")
        pairs.add(pair)
    if len(pairs) != EXPECTED_DUAL_PAIRS:
        raise AssertionError(f"wrong certified-pair count: {len(pairs)}")
    return frozenset(pairs)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--duals", type=Path, default=DUAL_PATH)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.workers <= 0:
        parser.error("--workers must be positive")

    cores = DUAL.generate_cores(args.geng)
    shells = DUAL.generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        raise AssertionError(
            f"catalog mismatch: cores={len(cores)} shells={len(shells)}"
        )
    if DUAL.catalog_sha256(cores) != DUAL.EXPECTED_CORE_CATALOG_SHA256:
        raise AssertionError("core catalog digest mismatch")
    if DUAL.catalog_sha256(shells) != DUAL.EXPECTED_SHELL_CATALOG_SHA256:
        raise AssertionError("shell catalog digest mismatch")
    certified = read_certified_pairs(args.duals, cores, shells)
    remainder = tuple(
        (core_index, shell_index)
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (
            core.graph6.decode("ascii"),
            shell.graph6.decode("ascii"),
        )
        not in certified
    )
    if len(remainder) != EXPECTED_REMAINDER_PAIRS:
        raise AssertionError(f"wrong remainder-pair count: {len(remainder)}")
    selected = tuple(
        pair
        for pair in remainder
        if has_two_vertex_edge_cover(shells[pair[1]].graph)
    )
    if len(selected) != EXPECTED_SELECTED_PAIRS:
        raise AssertionError(f"wrong selected-pair count: {len(selected)}")
    tasks = tuple(
        (
            core_index,
            shell_index,
            cores[core_index].graph6.decode("ascii"),
            shells[shell_index].graph6.decode("ascii"),
        )
        for core_index, shell_index in selected
    )
    if args.workers == 1:
        nested = tuple(audit_pair(task) for task in tasks)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as pool:
            nested = tuple(pool.map(audit_pair, tasks))
    states = tuple(state for group in nested for state in group)
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
    pair_profile = Counter(
        sum(
            state.core_index == core_index and state.shell_index == shell_index
            for state in states
        )
        for core_index, shell_index in selected
    )
    print(
        f"cores={len(cores)} shells={len(shells)} remainder_pairs={len(remainder)} "
        f"selected_pairs={len(selected)}"
    )
    print(
        f"q_states={len(states)} z3_UNSAT={len(states)} "
        "z3_SAT=0 z3_UNKNOWN=0"
    )
    print(f"pair_q_state_profile={dict(sorted(pair_profile.items()))}")
    print(f"classification_sha256={classification_sha256}")
    print("status=PASS")


if __name__ == "__main__":
    main()
