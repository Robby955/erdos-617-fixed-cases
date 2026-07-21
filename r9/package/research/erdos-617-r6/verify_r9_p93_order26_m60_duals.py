#!/usr/bin/env python3
"""Semantically verify exact rational duals for strict m=60 pairs.

This verifier independently reconstructs the 10 cores, the 152 compatible
shells, and every inequality named by a certificate. It does not import the
generator or exploratory fixed-shell code, and it does not call an LP or SAT
solver. It proves only the 1,290 pairs represented by strict exact duals.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import subprocess
from typing import Any, cast

import networkx as nx  # type: ignore[import-untyped]


R = 9
CORE_ORDER = 16
SHELL_ORDER = 9
CORE_EDGES = 60
GLOBAL_OFFSET = 15
VARIABLE_COUNT = CORE_ORDER * SHELL_ORDER
EXPECTED_CORES = 10
EXPECTED_SHELLS = 152
EXPECTED_PAIRS = EXPECTED_CORES * EXPECTED_SHELLS
EXPECTED_CERTIFICATES = 1290
EXPECTED_UNCERTIFIED = EXPECTED_PAIRS - EXPECTED_CERTIFICATES
EXPECTED_CORE_CATALOG_SHA256 = (
    "098b5d2179897443534a16d50e2cd1c86ccd8ed0e7c2a716ac612e8c5443a9ec"
)
EXPECTED_SHELL_CATALOG_SHA256 = (
    "234b69f2babc04e987b2fff4cb02af1e7c44d8096d05d5453262006048875a93"
)
EXPECTED_UNCERTIFIED_PAIR_SHA256 = (
    "f54b16c3087a849b7084193ce522a45e2f90ae6e24be168a968e83cfbeb6f5e7"
)
EXPECTED_SEMANTIC_SHA256 = (
    "b2d58b705277226d36ebc951d886e869e70fa7cf52669edc8d25d8b1041ccf3c"
)
EXPECTED_DATA_SHA256 = (
    "9470c5b7ea9b0951f99dccdf6ff03dccd420b1620de4dedb5ad9dc8252ea4953"
)
NONCLAIM = (
    "The 230 uncertified pairs remain open in this package; it does not "
    "exclude m=60, prove fixed r=9, or solve Erdos Problem 617."
)
EXPECTED_DEMAND_PROFILE = Counter(
    {
        (12, 12): 7,
        (12, 13): 2,
        (12, 14): 1,
    }
)
EXPECTED_SHELL_PROFILE = Counter(
    {
        (8, 4): 5,
        (8, 5): 8,
        (8, 6): 7,
        (8, 7): 1,
        (9, 2): 1,
        (9, 3): 2,
        (9, 4): 10,
        (9, 5): 4,
        (9, 6): 15,
        (10, 2): 3,
        (10, 3): 6,
        (10, 4): 10,
        (10, 5): 3,
        (11, 0): 1,
        (11, 1): 1,
        (11, 2): 8,
        (11, 3): 1,
        (11, 4): 6,
        (12, 0): 3,
        (12, 1): 3,
        (12, 2): 1,
        (12, 3): 9,
        (13, 0): 4,
        (13, 1): 2,
        (13, 2): 14,
        (14, 0): 5,
        (14, 1): 9,
        (15, 0): 10,
    }
)


@dataclass(frozen=True)
class GraphCase:
    graph6: bytes
    graph: nx.Graph
    minimum_slack: int | None = None


@dataclass(frozen=True)
class Inequality:
    variables: tuple[int, ...]
    right_side: int


def fail(message: str) -> None:
    raise AssertionError(message)


def exact_int(value: Any, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{name} must be an integer")
    return cast(int, value)


def exact_string(value: Any, name: str) -> str:
    if not isinstance(value, str):
        fail(f"{name} must be a string")
    return cast(str, value)


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
    command = [str(geng), "-q", "-t", "-D8", "16", "60:60"]
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
    for budget in range(8)
}


def minimum_shell_slack(graph: nx.Graph) -> int | None:
    budget = GLOBAL_OFFSET - graph.number_of_edges()
    if not 0 <= budget <= 7:
        return None
    degrees = tuple(graph.degree(vertex) for vertex in range(SHELL_ORDER))
    minimum = None
    for epsilon in COMPOSITIONS[budget]:
        if not all(
            degrees[first]
            + degrees[second]
            + epsilon[first]
            + epsilon[second]
            >= 8
            for first, second in graph.edges
        ):
            continue
        total = sum(epsilon)
        if minimum is None or total < minimum:
            minimum = total
    return minimum


def shell_compatible(graph: nx.Graph) -> tuple[bool, int | None]:
    if graph.number_of_nodes() != SHELL_ORDER:
        return False, None
    if any(
        all(
            graph.has_edge(first, second)
            for first, second in itertools.combinations(vertices, 2)
        )
        for vertices in itertools.combinations(range(SHELL_ORDER), 4)
    ):
        return False, None
    adjacency = adjacency_masks(graph)
    full = (1 << SHELL_ORDER) - 1
    if any(
        independent(full ^ (1 << omitted), adjacency)
        for omitted in range(SHELL_ORDER)
    ):
        return False, None
    minimum = minimum_shell_slack(graph)
    return minimum is not None, minimum


def generate_shells(geng: Path) -> tuple[GraphCase, ...]:
    command = [str(geng), "-q", "-k", "9", "8:15"]
    cases = []
    for graph6 in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(graph6)
        compatible, minimum = shell_compatible(graph)
        if compatible:
            cases.append(GraphCase(graph6, graph, minimum))
    return tuple(sorted(cases, key=lambda case: case.graph6))


def catalog_sha256(cases: tuple[GraphCase, ...]) -> str:
    payload = b"\n".join(case.graph6 for case in cases) + b"\n"
    return hashlib.sha256(payload).hexdigest()


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
        fail("m=60 core is not bipartite")
    coloring = nx.algorithms.bipartite.color(core)
    sides = tuple(
        tuple(sorted(vertex for vertex, color in coloring.items() if color == side))
        for side in (0, 1)
    )
    if sorted(map(len, sides)) != [8, 8]:
        fail("m=60 core does not have an 8+8 bipartition")
    if len(independent_eights(core)) != 2:
        fail("m=60 core does not have exactly two independent eight-sets")
    demand_sums = tuple(
        sum(max(0, core.degree(vertex) - 6) for vertex in side)
        for side in sides
    )
    smaller, larger = sorted(demand_sums)
    return smaller, larger


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
        "schema": "erdos617-r9-m60-duals-v1",
        "core_count": EXPECTED_CORES,
        "shell_count": EXPECTED_SHELLS,
        "pair_count": EXPECTED_PAIRS,
        "certificate_count": EXPECTED_CERTIFICATES,
        "uncertified_pair_count": EXPECTED_UNCERTIFIED,
        "core_catalog_sha256": EXPECTED_CORE_CATALOG_SHA256,
        "shell_catalog_sha256": EXPECTED_SHELL_CATALOG_SHA256,
        "uncertified_pair_sha256": EXPECTED_UNCERTIFIED_PAIR_SHA256,
        "semantic_sha256": EXPECTED_SEMANTIC_SHA256,
        "nonclaim": NONCLAIM,
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


def semantic_sha256(
    rows: list[tuple[str, str, Fraction, int]],
) -> str:
    payload = "".join(
        f"{core}:{shell}:{margin.numerator}/{margin.denominator}:{support}\n"
        for core, shell, margin, support in sorted(rows)
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def uncertified_pair_sha256(
    cores: tuple[GraphCase, ...],
    shells: tuple[GraphCase, ...],
    certified: set[tuple[str, str]],
) -> str:
    payload = "".join(
        f"{core_index}:{shell_index}\n"
        for core_index, core in enumerate(cores)
        for shell_index, shell in enumerate(shells)
        if (
            core.graph6.decode("ascii"),
            shell.graph6.decode("ascii"),
        )
        not in certified
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--certificates", type=Path, required=True)
    args = parser.parse_args()

    data_hash = hashlib.sha256(args.certificates.read_bytes()).hexdigest()
    if data_hash != EXPECTED_DATA_SHA256:
        fail(f"certificate data digest mismatch: {data_hash}")

    cores = generate_cores(args.geng)
    shells = generate_shells(args.geng)
    if len(cores) != EXPECTED_CORES or len(shells) != EXPECTED_SHELLS:
        fail(f"catalog mismatch: cores={len(cores)} shells={len(shells)}")
    if catalog_sha256(cores) != EXPECTED_CORE_CATALOG_SHA256:
        fail("core catalog digest mismatch")
    if catalog_sha256(shells) != EXPECTED_SHELL_CATALOG_SHA256:
        fail("shell catalog digest mismatch")

    demand_profile = Counter(core_demand_profile(case.graph) for case in cores)
    if demand_profile != EXPECTED_DEMAND_PROFILE:
        fail(f"core demand profile mismatch: {demand_profile}")
    shell_profile = Counter(
        (case.graph.number_of_edges(), case.minimum_slack) for case in shells
    )
    if shell_profile != EXPECTED_SHELL_PROFILE:
        fail(f"shell profile mismatch: {shell_profile}")

    core_map = {case.graph6.decode("ascii"): case.graph for case in cores}
    shell_map = {case.graph6.decode("ascii"): case.graph for case in shells}
    if len(core_map) != EXPECTED_CORES or len(shell_map) != EXPECTED_SHELLS:
        fail("graph6 catalog contains a duplicate")

    with args.certificates.open(encoding="ascii") as handle:
        lines = [line for line in handle if line.strip()]
    if len(lines) != EXPECTED_CERTIFICATES + 1:
        fail(f"certificate line count mismatch: {len(lines)}")
    parse_header(json.loads(lines[0]))

    certified: set[tuple[str, str]] = set()
    semantic_rows = []
    margins: Counter[Fraction] = Counter()
    support_sizes: Counter[int] = Counter()
    for line in lines[1:]:
        pair, margin, support_size = verify_record(
            json.loads(line), core_map, shell_map
        )
        if pair in certified:
            fail(f"duplicate certificate pair: {pair}")
        certified.add(pair)
        semantic_rows.append((pair[0], pair[1], margin, support_size))
        margins[margin] += 1
        support_sizes[support_size] += 1

    if len(certified) != EXPECTED_CERTIFICATES:
        fail(f"wrong number of certified pairs: {len(certified)}")
    semantic_hash = semantic_sha256(semantic_rows)
    if semantic_hash != EXPECTED_SEMANTIC_SHA256:
        fail(f"semantic digest mismatch: {semantic_hash}")
    remainder_hash = uncertified_pair_sha256(cores, shells, certified)
    if remainder_hash != EXPECTED_UNCERTIFIED_PAIR_SHA256:
        fail(f"uncertified-pair digest mismatch: {remainder_hash}")

    print(
        f"cores={len(cores)} shells={len(shells)} "
        f"pairs={EXPECTED_PAIRS}"
    )
    print(
        "core_structure=K8,8-minus-4 "
        f"demand_profile={dict(demand_profile)}"
    )
    print(f"shell_profile={dict(sorted(shell_profile.items()))}")
    print(
        f"strict_duals_verified={len(certified)} "
        f"uncertified_pairs={EXPECTED_UNCERTIFIED}"
    )
    print(f"semantic_sha256={semantic_hash}")
    print(f"uncertified_pair_sha256={remainder_hash}")
    print(f"data_sha256={data_hash}")
    print(f"margin_profile={dict(sorted(margins.items()))}")
    print(f"support_size_profile={dict(sorted(support_sizes.items()))}")
    print("status=PASS")


if __name__ == "__main__":
    main()
