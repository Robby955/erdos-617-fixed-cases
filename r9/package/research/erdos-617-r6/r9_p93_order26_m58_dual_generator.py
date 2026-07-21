#!/usr/bin/env python3
"""Generate exact rational duals for strict m=58 covering pairs.

The floating-point optimizer is used only to discover candidate weights.
Every emitted weight vector is normalized and checked with Fraction before
it is written.  The separate semantic verifier is the proof-facing check.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import subprocess

import networkx as nx  # type: ignore[import-untyped]
import numpy as np
from scipy.optimize import linprog  # type: ignore[import-untyped]
from scipy.sparse import lil_matrix  # type: ignore[import-untyped]


R = 9
CORE_ORDER = 16
SHELL_ORDER = 9
CORE_EDGES = 58
GLOBAL_OFFSET = 13
VARIABLE_COUNT = CORE_ORDER * SHELL_ORDER
MAX_DENOMINATOR = 1_000_000
EXPECTED_CORES = 50
EXPECTED_SHELLS = 55
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_CERTIFICATES = 1858


@dataclass(frozen=True)
class GraphCase:
    graph6: bytes
    graph: nx.Graph


@dataclass(frozen=True)
class Inequality:
    variables: tuple[int, ...]
    right_side: int


def p_r(order: int) -> int:
    quotient, remainder = divmod(order, R)
    return (R - remainder) * math.comb(quotient, 2) + remainder * math.comb(
        quotient + 1, 2
    )


def adjacency_masks(graph: nx.Graph) -> tuple[int, ...]:
    masks = [0] * graph.number_of_nodes()
    for first, second in graph.edges:
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


def induced_edges(mask: int, adjacency: tuple[int, ...]) -> int:
    return sum(
        (adjacency[vertex] & mask).bit_count()
        for vertex in range(len(adjacency))
        if mask >> vertex & 1
    ) // 2


def valid_core(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != CORE_ORDER:
        return False
    if graph.number_of_edges() != CORE_EDGES:
        return False
    if any(nx.triangles(graph).values()):
        return False
    if max(dict(graph.degree()).values()) > R - 1:
        return False
    adjacency = adjacency_masks(graph)
    for vertices in itertools.combinations(range(CORE_ORDER), R):
        mask = sum(1 << vertex for vertex in vertices)
        if independent(mask, adjacency):
            return False
    for order in range(R + 1, CORE_ORDER + 1):
        minimum = (R - 1) * p_r(order)
        for vertices in itertools.combinations(range(CORE_ORDER), order):
            mask = sum(1 << vertex for vertex in vertices)
            if induced_edges(mask, adjacency) < minimum:
                return False
    return True


def minimum_shell_slack(
    graph: nx.Graph, limit: int
) -> tuple[int, ...] | None:
    degrees = tuple(graph.degree(vertex) for vertex in range(SHELL_ORDER))
    demands = tuple(
        (first, second, max(0, 8 - degrees[first] - degrees[second]))
        for first, second in graph.edges
    )
    visited: set[tuple[int, ...]] = set()
    best: tuple[int, ...] | None = None

    def search(epsilon: tuple[int, ...]) -> None:
        nonlocal best
        total = sum(epsilon)
        if total > limit or epsilon in visited:
            return
        if best is not None and total >= sum(best):
            return
        visited.add(epsilon)
        violations = [
            (demand - epsilon[first] - epsilon[second], first, second)
            for first, second, demand in demands
            if epsilon[first] + epsilon[second] < demand
        ]
        if not violations:
            best = epsilon
            return
        deficit, first, second = max(violations)
        for first_increment in range(deficit + 1):
            updated = list(epsilon)
            updated[first] += first_increment
            updated[second] += deficit - first_increment
            search(tuple(updated))

    search((0,) * SHELL_ORDER)
    return best


def generate_cores(geng: Path) -> tuple[GraphCase, ...]:
    command = [str(geng), "-q", "-t", "-D8", "16", "58:58"]
    result = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if valid_core(graph):
            result.append(GraphCase(graph6, graph))
    return tuple(sorted(result, key=lambda case: case.graph6))


def has_independent_eight(graph: nx.Graph) -> bool:
    adjacency = adjacency_masks(graph)
    for omitted in range(SHELL_ORDER):
        mask = ((1 << SHELL_ORDER) - 1) ^ (1 << omitted)
        if independent(mask, adjacency):
            return True
    return False


def generate_shells(geng: Path) -> tuple[GraphCase, ...]:
    command = [str(geng), "-q", "-k", "9", "8:13"]
    result = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if has_independent_eight(graph):
            continue
        limit = GLOBAL_OFFSET - graph.number_of_edges()
        if minimum_shell_slack(graph, limit) is not None:
            result.append(GraphCase(graph6, graph))
    return tuple(sorted(result, key=lambda case: case.graph6))


def cross(shell_vertex: int, core_vertex: int) -> int:
    return CORE_ORDER * shell_vertex + core_vertex


def sorted_edges(graph: nx.Graph) -> tuple[tuple[int, int], ...]:
    return tuple(sorted(tuple(sorted(edge)) for edge in graph.edges))


def inequalities(core: nx.Graph, shell: nx.Graph) -> tuple[Inequality, ...]:
    result = []
    for shell_vertex in range(SHELL_ORDER):
        result.append(
            Inequality(
                tuple(
                    cross(shell_vertex, core_vertex)
                    for core_vertex in range(CORE_ORDER)
                ),
                shell.degree(shell_vertex),
            )
        )
    for core_vertex in range(CORE_ORDER):
        result.append(
            Inequality(
                tuple(
                    cross(shell_vertex, core_vertex)
                    for shell_vertex in range(SHELL_ORDER)
                ),
                max(0, core.degree(core_vertex) - 6),
            )
        )
    for first_shell, second_shell in sorted_edges(shell):
        for first_core, second_core in sorted_edges(core):
            result.append(
                Inequality(
                    (
                        cross(first_shell, first_core),
                        cross(first_shell, second_core),
                        cross(second_shell, first_core),
                        cross(second_shell, second_core),
                    ),
                    1,
                )
            )
    for triangle in itertools.combinations(range(SHELL_ORDER), 3):
        if not all(
            shell.has_edge(first, second)
            for first, second in itertools.combinations(triangle, 2)
        ):
            continue
        for core_vertex in range(CORE_ORDER):
            result.append(
                Inequality(
                    tuple(
                        cross(shell_vertex, core_vertex)
                        for shell_vertex in triangle
                    ),
                    1,
                )
            )
    return tuple(result)


def discover_dual(
    rows: tuple[Inequality, ...],
) -> tuple[tuple[int, Fraction], ...]:
    matrix = lil_matrix((VARIABLE_COUNT, len(rows)), dtype=float)
    for row_index, row in enumerate(rows):
        for variable in row.variables:
            matrix[variable, row_index] = 1.0
    objective = -np.array([row.right_side for row in rows], dtype=float)
    result = linprog(
        objective,
        A_ub=matrix.tocsr(),
        b_ub=np.ones(VARIABLE_COUNT),
        bounds=(0, None),
        method="highs-ds",
    )
    if result.status != 0 or result.x is None:
        raise RuntimeError(f"dual solve failed with status {result.status}")
    weights = tuple(
        (index, Fraction(float(value)).limit_denominator(MAX_DENOMINATOR))
        for index, value in enumerate(result.x)
        if value > 1e-9
    )
    loads = [Fraction(0) for _ in range(VARIABLE_COUNT)]
    for row_index, weight in weights:
        for variable in rows[row_index].variables:
            loads[variable] += weight
    scale = max(Fraction(1), max(loads))
    normalized = tuple((index, weight / scale) for index, weight in weights)
    verify_dual(rows, normalized)
    return normalized


def verify_dual(
    rows: tuple[Inequality, ...],
    weights: tuple[tuple[int, Fraction], ...],
) -> None:
    loads = [Fraction(0) for _ in range(VARIABLE_COUNT)]
    seen = set()
    for row_index, weight in weights:
        if row_index in seen or not 0 <= row_index < len(rows):
            raise AssertionError("invalid dual row index")
        if weight <= 0:
            raise AssertionError("dual weights must be positive")
        seen.add(row_index)
        for variable in rows[row_index].variables:
            loads[variable] += weight
    if max(loads) > 1:
        raise AssertionError("dual variable load exceeds one")


def encoded_weights(
    weights: tuple[tuple[int, Fraction], ...]
) -> list[list[int]]:
    return [
        [row_index, weight.numerator, weight.denominator]
        for row_index, weight in weights
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    cores = generate_cores(args.geng)
    shells = generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        raise AssertionError(
            f"catalog mismatch: cores={len(cores)} shells={len(shells)}"
        )

    records = []
    for core in cores:
        for shell in shells:
            rows = inequalities(core.graph, shell.graph)
            weights = discover_dual(rows)
            objective = sum(
                rows[row_index].right_side * weight
                for row_index, weight in weights
            )
            budget = shell.graph.number_of_edges() + GLOBAL_OFFSET
            if objective <= budget:
                continue
            records.append(
                {
                    "core": core.graph6.decode("ascii"),
                    "shell": shell.graph6.decode("ascii"),
                    "weights": encoded_weights(weights),
                }
            )

    if len(records) != EXPECTED_CERTIFICATES:
        raise AssertionError(
            f"expected {EXPECTED_CERTIFICATES} certificates, "
            f"found {len(records)}"
        )

    header = {
        "schema": "erdos617-r9-m58-duals-v1",
        "core_count": len(cores),
        "shell_count": len(shells),
        "pair_count": len(cores) * len(shells),
        "certificate_count": len(records),
        "uncertified_pair_count": EXPECTED_PAIRS - len(records),
    }
    with args.output.open("w", encoding="ascii") as handle:
        handle.write(json.dumps(header, sort_keys=True, separators=(",", ":")))
        handle.write("\n")
        for record in records:
            handle.write(
                json.dumps(record, sort_keys=True, separators=(",", ":"))
            )
            handle.write("\n")

    print(f"cores={len(cores)} shells={len(shells)} pairs={EXPECTED_PAIRS}")
    print(
        f"certificates={len(records)} "
        f"uncertified={EXPECTED_PAIRS - len(records)}"
    )
    print(f"output={args.output}")
    print("status=PASS")


if __name__ == "__main__":
    main()
