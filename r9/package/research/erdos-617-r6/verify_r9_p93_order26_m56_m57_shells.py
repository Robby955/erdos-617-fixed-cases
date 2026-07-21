#!/usr/bin/env python3
"""Verify the endpoint shell catalogs and their transversal exclusions.

The calculation is independent of the fixed-shell SAT runner.  It checks
the scalar shell condition by direct enumeration of all relevant slack
vectors.  Simple integral dual witnesses then exclude both shells at
core level 56 and thirteen of the sixteen shells at core level 57.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path
import subprocess

import networkx as nx  # type: ignore[import-untyped]


SHELL_ORDER = 9
TARGET_EDGES_ON_V_PLUS_A = 45
LOCAL_TARGET_CAP_10 = 37
MIN_SHELL_EDGES = TARGET_EDGES_ON_V_PLUS_A - LOCAL_TARGET_CAP_10
MAX_SHELL_EDGES_57 = 57 - 45
EXPECTED = {
    56: (b"H???Fbp", b"H???Frx"),
    57: (
        b"H???CB|",
        b"H???EBx",
        b"H???EB|",
        b"H???FBp",
        b"H???FBx",
        b"H???FB|",
        b"H???Fbo",
        b"H???Fbp",
        b"H???Fbx",
        b"H???Fb|",
        b"H???Frw",
        b"H???Frx",
        b"H???Fr|",
        b"H???Fz{",
        b"H??EEBB",
        b"H?BEENE",
    ),
}
SURVIVORS_57 = frozenset({b"H???Fbo", b"H???Frw", b"H???Fz{"})

# Each pair is (constant term, weighted vertex set, certified lower bound).
# The associated dual inequality is
#
#     constant + |S intersect vertex_set| <= |S|
#
# for every bounded triangle transversal S.
DUAL_CERTIFICATES = {
    b"H???CB|": (1, frozenset({1, 2, 3, 4, 5}), 21),
    b"H???EBx": (1, frozenset({0, 2, 3, 4}), 21),
    b"H???EB|": (1, frozenset({0, 2, 3, 4, 5}), 22),
    b"H???FBp": (1, frozenset({0, 1, 2, 3}), 23),
    b"H???FBx": (1, frozenset({0, 1, 3, 4}), 22),
    b"H???FB|": (1, frozenset({1, 2, 3, 4, 5}), 23),
    b"H???Fbp": (1, frozenset({0, 1, 2, 3}), 24),
    b"H???Fbx": (1, frozenset({0, 1, 2, 4}), 23),
    b"H???Fb|": (1, frozenset({0, 1, 2, 4, 5}), 24),
    b"H???Frx": (1, frozenset({0, 1, 2, 4}), 24),
    b"H???Fr|": (1, frozenset({0, 1, 2, 3, 5}), 25),
    b"H??EEBB": (1, frozenset({0, 6}), 22),
    b"H?BEENE": (2, frozenset(), 32),
}


def independent_eight_set(graph: nx.Graph) -> bool:
    for omitted in range(SHELL_ORDER):
        vertices = [
            vertex for vertex in range(SHELL_ORDER) if vertex != omitted
        ]
        if graph.subgraph(vertices).number_of_edges() == 0:
            return True
    return False


def slack_vectors(order: int, budget: int) -> tuple[tuple[int, ...], ...]:
    result = []

    def extend(prefix: tuple[int, ...], remaining: int) -> None:
        if len(prefix) == order:
            result.append(prefix)
            return
        for value in range(remaining + 1):
            extend(prefix + (value,), remaining - value)

    extend((), budget)
    return tuple(result)


SLACK_VECTORS = {
    budget: slack_vectors(SHELL_ORDER, budget) for budget in range(5)
}


def compatible(graph: nx.Graph, core_edges: int) -> bool:
    if independent_eight_set(graph):
        return False
    shell_edges = graph.number_of_edges()
    budget = core_edges - 45 - shell_edges
    if budget < 0:
        return False
    degrees = tuple(graph.degree(vertex) for vertex in range(SHELL_ORDER))
    for epsilon in SLACK_VECTORS[budget]:
        if all(
            degrees[first]
            + degrees[second]
            + epsilon[first]
            + epsilon[second]
            >= 8
            for first, second in graph.edges
        ):
            return True
    return False


def generate_endpoint_catalogs(
    geng: Path,
) -> tuple[int, dict[int, tuple[bytes, ...]]]:
    catalogs: dict[int, list[bytes]] = {56: [], 57: []}
    command = [
        str(geng),
        "-q",
        "-k",
        "9",
        f"{MIN_SHELL_EDGES}:{MAX_SHELL_EDGES_57}",
    ]
    lines = subprocess.check_output(command).splitlines()
    for line in lines:
        graph = nx.from_graph6_bytes(line)
        for core_edges in catalogs:
            if compatible(graph, core_edges):
                catalogs[core_edges].append(line)
    return len(lines), {
        level: tuple(sorted(level_lines))
        for level, level_lines in catalogs.items()
    }


def triangles(graph: nx.Graph) -> tuple[int, ...]:
    result = []
    for vertices in itertools.combinations(range(SHELL_ORDER), 3):
        if all(
            graph.has_edge(first, second)
            for first, second in itertools.combinations(vertices, 2)
        ):
            result.append(sum(1 << vertex for vertex in vertices))
    return tuple(result)


def allowed_column_masks(graph: nx.Graph) -> tuple[int, ...]:
    size_cap = graph.number_of_edges() - 6
    triangle_masks = triangles(graph)
    return tuple(
        mask
        for mask in range(1 << SHELL_ORDER)
        if mask.bit_count() <= size_cap
        and all(mask & triangle for triangle in triangle_masks)
    )


def verify_dual(graph6: bytes) -> int:
    graph = nx.from_graph6_bytes(graph6)
    constant, vertices, expected_lower = DUAL_CERTIFICATES[graph6]
    for mask in allowed_column_masks(graph):
        weighted_count = sum(mask >> vertex & 1 for vertex in vertices)
        if constant + weighted_count > mask.bit_count():
            raise AssertionError(
                f"dual inequality fails for {graph6.decode('ascii')} "
                f"at mask={mask}"
            )
    lower = 16 * constant + sum(graph.degree(vertex) for vertex in vertices)
    if lower != expected_lower:
        raise AssertionError(
            f"wrong lower bound for {graph6.decode('ascii')}: {lower}"
        )
    return lower


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    args = parser.parse_args()

    if MIN_SHELL_EDGES != 8 or MAX_SHELL_EDGES_57 != 12:
        raise AssertionError("wrong endpoint shell range")
    raw_count, catalogs = generate_endpoint_catalogs(args.geng)
    if raw_count != 11088:
        raise AssertionError(f"expected 11088 raw shells, found {raw_count}")
    if catalogs != EXPECTED:
        raise AssertionError(f"endpoint catalog mismatch: {catalogs}")

    for level, graph6_lines in catalogs.items():
        excluded = 0
        for graph6 in graph6_lines:
            if graph6 in DUAL_CERTIFICATES:
                lower = verify_dual(graph6)
                graph = nx.from_graph6_bytes(graph6)
                upper = graph.number_of_edges() + level - 45
                if lower <= upper:
                    raise AssertionError(
                        f"certificate does not exclude {graph6.decode('ascii')}"
                    )
                excluded += 1
        expected_excluded = 2 if level == 56 else 13
        if excluded != expected_excluded:
            raise AssertionError(
                f"level {level}: excluded={excluded}, "
                f"expected={expected_excluded}"
            )

    remaining_57 = frozenset(EXPECTED[57]) - frozenset(DUAL_CERTIFICATES)
    if remaining_57 != SURVIVORS_57:
        raise AssertionError(f"wrong level-57 survivors: {remaining_57}")

    print(f"raw_shells_checked={raw_count}")
    print(f"level_56_shells={len(catalogs[56])} dual_excluded=2")
    print(f"level_57_shells={len(catalogs[57])} dual_excluded=13")
    print(
        "level_57_survivors="
        + str([line.decode("ascii") for line in sorted(SURVIVORS_57)])
    )
    print("status=PASS")


if __name__ == "__main__":
    main()
