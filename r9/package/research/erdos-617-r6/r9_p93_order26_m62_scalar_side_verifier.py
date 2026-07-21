#!/usr/bin/env python3
"""Verify scalar side-count exclusions for the m=62 dual complement.

This checker uses only integer arithmetic and exhaustive finite search. It
does not assign actual core vertices to shell rows. Consequently, a feasible
state here is only a necessary-condition survivor, while an infeasible state
is rigorously excluded by the proved side-count conditions.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from typing import Any, Iterator, cast

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
DUAL_PATH = HERE / "verify_r9_p93_order26_m62_duals.py"
DUAL_DATA = HERE / "r9_p93_order26_m62_duals.jsonl"
SHELL_ORDER = 9
GLOBAL_OFFSET = 17
EXPECTED_COMPLEMENT_PAIRS = 152
EXPECTED_DISTINCT_SHELLS = 89
EXPECTED_RAW_STATES = 38342
EXPECTED_FEASIBLE_STATES = 11706
EXPECTED_COMPLEMENT_SHA256 = (
    "f5a0febbfb028eb99aa4201df31232ec46ded7f1c4299011d753d29b031532fb"
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "95c95dd18f15be8887e0d302ae5173cae87a7891d48faaf5754de16bf37c876c"
)
EXPECTED_PAIR_PROFILE = Counter(
    {
        (2, True): 35,
        (3, False): 107,
        (4, False): 10,
    }
)


def load_dual_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("m62_scalar_dual", DUAL_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {DUAL_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


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


DUAL = load_dual_verifier()


def row_size_states(shell: nx.Graph) -> tuple[tuple[int, ...], ...]:
    degrees = tuple(int(shell.degree(vertex)) for vertex in range(SHELL_ORDER))
    budget = GLOBAL_OFFSET - shell.number_of_edges()
    states = set()
    for epsilon in weak_compositions_at_most(budget, SHELL_ORDER):
        rows = tuple(degrees[vertex] + epsilon[vertex] for vertex in range(SHELL_ORDER))
        if all(rows[first] + rows[second] >= 8 for first, second in shell.edges):
            states.add(rows)
    return tuple(sorted(states))


def triangles(shell: nx.Graph) -> tuple[tuple[int, int, int], ...]:
    return tuple(
        triple
        for triple in itertools.combinations(range(SHELL_ORDER), 3)
        if all(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(triple, 2)
        )
    )


def side_demands(core: nx.Graph) -> tuple[int, int]:
    colors = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(int(vertex) for vertex, color in colors.items() if color == side)
        for side in (0, 1)
    )
    if tuple(sorted(map(len, sides))) != (8, 8):
        raise AssertionError("core does not have an 8+8 bipartition")
    return cast(
        tuple[int, int],
        tuple(
            sum(max(0, int(core.degree(vertex)) - 6) for vertex in side)
            for side in sides
        ),
    )


def feasible_side_counts(
    shell: nx.Graph, rows: tuple[int, ...], demand_x: int, demand_y: int
) -> bool:
    """Return whether necessary integer side counts x_a can coexist.

    Here x_a=|D_a intersect X| and y_a=rows[a]-x_a.  The bounds x_a,y_a<=7
    are the p=1 exclusions.  If an edge has row-size sum at most 12, the
    uniform cover lemma says its union contains X or Y.  A shell triangle
    covers the entire core, hence contributes at least eight incidences to
    each side.
    """

    small_edges = tuple(
        (int(first), int(second))
        for first, second in shell.edges
        if rows[int(first)] + rows[int(second)] <= 12
    )
    shell_triangles = triangles(shell)
    domains = tuple(tuple(range(max(0, row - 7), min(7, row) + 1)) for row in rows)
    incident_constraints = tuple(
        sum(vertex in edge for edge in small_edges)
        + 2 * sum(vertex in triple for triple in shell_triangles)
        for vertex in range(SHELL_ORDER)
    )
    order = tuple(
        sorted(
            range(SHELL_ORDER),
            key=lambda vertex: (-incident_constraints[vertex], len(domains[vertex])),
        )
    )
    position = {vertex: index for index, vertex in enumerate(order)}
    values: list[int | None] = [None] * SHELL_ORDER

    def search(index: int, sum_x: int, sum_y: int) -> bool:
        if index == SHELL_ORDER:
            return sum_x >= demand_x and sum_y >= demand_y
        remaining = order[index:]
        if sum_x + sum(max(domains[vertex]) for vertex in remaining) < demand_x:
            return False
        if (
            sum_y + sum(rows[vertex] - min(domains[vertex]) for vertex in remaining)
            < demand_y
        ):
            return False

        vertex = order[index]
        for x_value in domains[vertex]:
            values[vertex] = x_value
            y_value = rows[vertex] - x_value
            valid = True
            for first, second in small_edges:
                other = (
                    second if first == vertex else first if second == vertex else None
                )
                if other is None or position[other] >= index:
                    continue
                other_x = values[other]
                if other_x is None:
                    raise AssertionError("assigned-order invariant failed")
                if x_value + other_x < 8 and y_value + rows[other] - other_x < 8:
                    valid = False
                    break
            if not valid:
                values[vertex] = None
                continue
            for triple in shell_triangles:
                if vertex not in triple:
                    continue
                if any(position[other] >= index for other in triple if other != vertex):
                    continue
                assigned_values = tuple(
                    x_value if other == vertex else values[other] for other in triple
                )
                if any(value is None for value in assigned_values):
                    raise AssertionError("triangle assignment invariant failed")
                triple_x = sum(cast(int, value) for value in assigned_values)
                triple_y = sum(rows[other] for other in triple) - triple_x
                if triple_x < 8 or triple_y < 8:
                    valid = False
                    break
            if valid and search(index + 1, sum_x + x_value, sum_y + y_value):
                values[vertex] = None
                return True
            values[vertex] = None
        return False

    return search(0, 0, 0)


def vertex_cover_number(graph: nx.Graph) -> int:
    edges = tuple((int(first), int(second)) for first, second in graph.edges)
    for size in range(SHELL_ORDER + 1):
        if any(
            all(first in cover or second in cover for first, second in edges)
            for cover in itertools.combinations(range(SHELL_ORDER), size)
        ):
            return size
    raise AssertionError("shell has no vertex cover")


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
            raise AssertionError(f"dual pair outside catalogs at line {line_number}")
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
    args = parser.parse_args()

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
    payload = "".join(f"{first}:{second}\n" for first, second in complement).encode(
        "ascii"
    )
    digest = hashlib.sha256(payload).hexdigest()
    if digest != EXPECTED_COMPLEMENT_SHA256:
        raise AssertionError("dual-complement digest mismatch")

    shell_states: dict[int, tuple[tuple[int, ...], ...]] = {}
    rows = []
    pair_profile: Counter[tuple[int, bool]] = Counter()
    for core_index, shell_index in complement:
        core = cores[core_index].graph
        shell = shells[shell_index].graph
        if shell_index not in shell_states:
            shell_states[shell_index] = row_size_states(shell)
        demands = side_demands(core)
        feasible = tuple(
            state
            for state in shell_states[shell_index]
            if feasible_side_counts(shell, state, demands[0], demands[1])
        )
        tau = vertex_cover_number(shell)
        pair_profile[(tau, bool(feasible))] += 1
        rows.append(
            f"{core_index}:{shell_index}:{tau}:{len(shell_states[shell_index])}:"
            f"{len(feasible)}\n"
        )

    classification = "".join(rows).encode("ascii")
    classification_digest = hashlib.sha256(classification).hexdigest()
    if len(shell_states) != EXPECTED_DISTINCT_SHELLS:
        raise AssertionError(f"wrong distinct shell count: {len(shell_states)}")
    if sum(int(row.split(":")[3]) for row in rows) != EXPECTED_RAW_STATES:
        raise AssertionError("wrong raw state count")
    if sum(int(row.split(":")[4]) for row in rows) != EXPECTED_FEASIBLE_STATES:
        raise AssertionError("wrong feasible state count")
    if pair_profile != EXPECTED_PAIR_PROFILE:
        raise AssertionError(f"wrong pair profile: {pair_profile}")
    if classification_digest != EXPECTED_CLASSIFICATION_SHA256:
        raise AssertionError(f"classification digest mismatch: {classification_digest}")
    print(f"complement_pairs={len(complement)} complement_sha256={digest}")
    print(f"distinct_shells={len(shell_states)}")
    print(f"pair_profile={dict(sorted(pair_profile.items()))}")
    print(f"classification_sha256={classification_digest}")
    print(
        f"raw_q_states={EXPECTED_RAW_STATES} "
        f"scalar_feasible_q_states={EXPECTED_FEASIBLE_STATES}"
    )
    print("status=PASS")


if __name__ == "__main__":
    main()

