#!/usr/bin/env python3
"""Semantically verify exact rational duals for the strict m=58 pairs.

This verifier reconstructs the 50 cores, the 55 scalar-compatible shells,
and every inequality named by a certificate.  It does not call an LP or SAT
solver.  It proves only the pairs represented by strict exact duals.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import subprocess
from typing import Any

import networkx as nx  # type: ignore[import-untyped]


R = 9
CORE_ORDER = 16
SHELL_ORDER = 9
CORE_EDGES = 58
GLOBAL_OFFSET = 13
VARIABLE_COUNT = CORE_ORDER * SHELL_ORDER
EXPECTED_CORES = 50
EXPECTED_SHELLS = 55
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_CERTIFICATES = 1858
EXPECTED_UNCERTIFIED = EXPECTED_PAIRS - EXPECTED_CERTIFICATES
EXPECTED_DEMAND_PROFILE = Counter(
    {
        (10, 10): 17,
        (10, 11): 14,
        (10, 12): 11,
        (11, 11): 4,
        (10, 13): 2,
        (11, 12): 1,
        (10, 14): 1,
    }
)


@dataclass(frozen=True)
class GraphCase:
    graph6: bytes
    graph: nx.Graph


@dataclass(frozen=True)
class Inequality:
    variables: tuple[int, ...]
    right_side: int


def fail(message: str) -> None:
    raise AssertionError(message)


def exact_int(value: Any, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{name} must be an integer")
    return value


def exact_string(value: Any, name: str) -> str:
    if not isinstance(value, str):
        fail(f"{name} must be a string")
    return value


def p_r(order: int) -> int:
    quotient, remainder = divmod(order, R)
    return (R - remainder) * math.comb(quotient, 2) + remainder * math.comb(
        quotient + 1, 2
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


def induced_edges(mask: int, adjacency: tuple[int, ...]) -> int:
    degree_sum = 0
    for vertex in range(len(adjacency)):
        if mask >> vertex & 1:
            degree_sum += (adjacency[vertex] & mask).bit_count()
    return degree_sum // 2


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


def generate_cores(geng: Path) -> tuple[GraphCase, ...]:
    command = [str(geng), "-q", "-t", "-D8", "16", "58:58"]
    cases = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if valid_core(graph):
            cases.append(GraphCase(graph6, graph))
    return tuple(sorted(cases, key=lambda case: case.graph6))


def weak_compositions(total: int, length: int) -> tuple[tuple[int, ...], ...]:
    result = []

    def extend(prefix: tuple[int, ...], remaining: int) -> None:
        if len(prefix) + 1 == length:
            result.append(prefix + (remaining,))
            return
        for value in range(remaining + 1):
            extend(prefix + (value,), remaining - value)

    extend((), total)
    return tuple(result)


COMPOSITIONS = {
    budget: tuple(
        vector
        for total in range(budget + 1)
        for vector in weak_compositions(total, SHELL_ORDER)
    )
    for budget in range(6)
}


def shell_compatible(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != SHELL_ORDER:
        return False
    if any(
        all(
            graph.has_edge(first, second)
            for first, second in itertools.combinations(vertices, 2)
        )
        for vertices in itertools.combinations(range(SHELL_ORDER), 4)
    ):
        return False
    adjacency = adjacency_masks(graph)
    full = (1 << SHELL_ORDER) - 1
    for omitted in range(SHELL_ORDER):
        if independent(full ^ (1 << omitted), adjacency):
            return False
    budget = GLOBAL_OFFSET - graph.number_of_edges()
    if not 0 <= budget <= 5:
        return False
    degrees = tuple(graph.degree(vertex) for vertex in range(SHELL_ORDER))
    return any(
        all(
            degrees[first]
            + degrees[second]
            + epsilon[first]
            + epsilon[second]
            >= 8
            for first, second in graph.edges
        )
        for epsilon in COMPOSITIONS[budget]
    )


def generate_shells(geng: Path) -> tuple[GraphCase, ...]:
    command = [str(geng), "-q", "-k", "9", "8:13"]
    cases = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        if shell_compatible(graph):
            cases.append(GraphCase(graph6, graph))
    return tuple(sorted(cases, key=lambda case: case.graph6))


def independent_eights(graph: nx.Graph) -> tuple[int, ...]:
    adjacency = adjacency_masks(graph)
    result = []
    for vertices in itertools.combinations(range(CORE_ORDER), 8):
        mask = sum(1 << vertex for vertex in vertices)
        if independent(mask, adjacency):
            result.append(mask)
    return tuple(result)


def core_demand_profile(core: nx.Graph) -> tuple[int, int]:
    if not nx.is_bipartite(core):
        fail("m=58 core is not bipartite")
    coloring = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(sorted(vertex for vertex, color in coloring.items() if color == side))
        for side in (0, 1)
    )
    if sorted(map(len, sides)) != [8, 8]:
        fail("m=58 core does not have an 8+8 bipartition")
    if len(independent_eights(core)) != 2:
        fail("m=58 core does not have exactly two independent eight-sets")
    demand_sums = tuple(
        sum(max(0, core.degree(vertex) - 6) for vertex in side)
        for side in sides
    )
    return tuple(sorted(demand_sums))  # type: ignore[return-value]


def cross(shell_vertex: int, core_vertex: int) -> int:
    return CORE_ORDER * shell_vertex + core_vertex


def sorted_edges(graph: nx.Graph) -> tuple[tuple[int, int], ...]:
    result = []
    for raw_first, raw_second in graph.edges:
        first = int(raw_first)
        second = int(raw_second)
        result.append((first, second) if first < second else (second, first))
    return tuple(sorted(result))


def inequalities(core: nx.Graph, shell: nx.Graph) -> tuple[Inequality, ...]:
    rows = []
    for shell_vertex in range(SHELL_ORDER):
        rows.append(
            Inequality(
                tuple(
                    cross(shell_vertex, core_vertex)
                    for core_vertex in range(CORE_ORDER)
                ),
                shell.degree(shell_vertex),
            )
        )
    for core_vertex in range(CORE_ORDER):
        rows.append(
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
            rows.append(
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
            rows.append(
                Inequality(
                    tuple(
                        cross(shell_vertex, core_vertex)
                        for shell_vertex in triangle
                    ),
                    1,
                )
            )
    return tuple(rows)


def parse_header(raw: Any) -> None:
    if not isinstance(raw, dict):
        fail("certificate header must be an object")
    expected = {
        "schema": "erdos617-r9-m58-duals-v1",
        "core_count": EXPECTED_CORES,
        "shell_count": EXPECTED_SHELLS,
        "pair_count": EXPECTED_PAIRS,
        "certificate_count": EXPECTED_CERTIFICATES,
        "uncertified_pair_count": EXPECTED_UNCERTIFIED,
    }
    if raw != expected:
        fail(f"certificate header mismatch: {raw}")


def parse_weights(raw: Any) -> tuple[tuple[int, Fraction], ...]:
    if not isinstance(raw, list):
        fail("weights must be a list")
    result = []
    previous_index = -1
    for position, entry in enumerate(raw):
        if not isinstance(entry, list) or len(entry) != 3:
            fail(f"weight {position} must be a three-item list")
        row_index = exact_int(entry[0], f"weight {position} row")
        numerator = exact_int(entry[1], f"weight {position} numerator")
        denominator = exact_int(entry[2], f"weight {position} denominator")
        if row_index <= previous_index:
            fail("weight row indices must be strictly increasing")
        if numerator <= 0 or denominator <= 0:
            fail("weight fractions must be positive")
        weight = Fraction(numerator, denominator)
        if weight.numerator != numerator or weight.denominator != denominator:
            fail("weight fraction is not reduced")
        result.append((row_index, weight))
        previous_index = row_index
    return tuple(result)


def verify_record(
    raw: Any,
    core_map: dict[str, nx.Graph],
    shell_map: dict[str, nx.Graph],
) -> tuple[tuple[str, str], Fraction, int]:
    if not isinstance(raw, dict) or set(raw) != {"core", "shell", "weights"}:
        fail("certificate record has the wrong fields")
    core_name = exact_string(raw["core"], "core")
    shell_name = exact_string(raw["shell"], "shell")
    if core_name not in core_map or shell_name not in shell_map:
        fail("certificate names a graph outside the exact catalogs")
    weights = parse_weights(raw["weights"])
    rows = inequalities(core_map[core_name], shell_map[shell_name])
    loads = [Fraction(0) for _ in range(VARIABLE_COUNT)]
    objective = Fraction(0)
    for row_index, weight in weights:
        if row_index >= len(rows):
            fail("certificate row index is out of range")
        row = rows[row_index]
        objective += row.right_side * weight
        for variable in row.variables:
            loads[variable] += weight
    if max(loads) > 1:
        fail("certificate gives a variable coefficient above one")
    budget = shell_map[shell_name].number_of_edges() + GLOBAL_OFFSET
    if objective <= budget:
        fail("certificate objective does not exceed the global budget")
    return (core_name, shell_name), objective - budget, len(weights)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--certificates", type=Path, required=True)
    args = parser.parse_args()

    cores = generate_cores(args.geng)
    shells = generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        fail(f"catalog mismatch: cores={len(cores)} shells={len(shells)}")

    demand_profile = Counter(core_demand_profile(case.graph) for case in cores)
    if demand_profile != EXPECTED_DEMAND_PROFILE:
        fail(f"core demand profile mismatch: {demand_profile}")

    core_map = {case.graph6.decode("ascii"): case.graph for case in cores}
    shell_map = {case.graph6.decode("ascii"): case.graph for case in shells}
    if len(core_map) != EXPECTED_CORES or len(shell_map) != EXPECTED_SHELLS:
        fail("graph6 catalog contains a duplicate")

    with args.certificates.open(encoding="ascii") as handle:
        lines = [line for line in handle if line.strip()]
    if len(lines) != EXPECTED_CERTIFICATES + 1:
        fail(f"certificate line count mismatch: {len(lines)}")
    parse_header(json.loads(lines[0]))

    certified = set()
    margins: Counter[Fraction] = Counter()
    support_sizes: Counter[int] = Counter()
    for line in lines[1:]:
        pair, margin, support_size = verify_record(
            json.loads(line), core_map, shell_map
        )
        if pair in certified:
            fail(f"duplicate certificate pair: {pair}")
        certified.add(pair)
        margins[margin] += 1
        support_sizes[support_size] += 1

    if len(certified) != EXPECTED_CERTIFICATES:
        fail(f"wrong number of certified pairs: {len(certified)}")

    print(
        f"cores={len(cores)} shells={len(shells)} "
        f"pairs={EXPECTED_PAIRS}"
    )
    print(f"core_structure=K8,8-minus-6 demand_profile={dict(demand_profile)}")
    print(
        f"strict_duals_verified={len(certified)} "
        f"uncertified_pairs={EXPECTED_UNCERTIFIED}"
    )
    print(f"margin_profile={dict(sorted(margins.items()))}")
    print(f"support_size_profile={dict(sorted(support_sizes.items()))}")
    print("status=PASS")


if __name__ == "__main__":
    main()
