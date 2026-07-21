#!/usr/bin/env python3
"""Solver-free exclusion of the four m=64 cover-number-three states."""

from __future__ import annotations

from collections import Counter
import hashlib
import importlib.util
import itertools
from pathlib import Path
import sys
from typing import Any

import networkx as nx  # type: ignore[import-untyped]


HERE = Path(__file__).resolve().parent
SCALAR_PATH = HERE / "r9_p93_order26_m64_scalar_side_verifier.py"
EXPECTED_CASES = (
    ("H??Ff~}", (3, 3, 3, 3, 2, 2, 7, 7, 7)),
    ("H??Fvrz", (3, 3, 3, 3, 3, 0, 7, 7, 7)),
    ("H??Fvv}", (3, 3, 3, 3, 3, 1, 7, 7, 7)),
    ("H??F~zz", (3, 3, 3, 3, 3, 2, 7, 7, 7)),
)
EXPECTED_ASSIGNMENT_PROFILE: Counter[str] = Counter(
    {
        "H??Ff~}:X:4": 1,
        "H??Ff~}:Y:4": 1,
        "H??Fvrz:X:0": 1,
        "H??Fvrz:Y:0": 1,
        "H??Fvv}:X:1": 1,
        "H??Fvv}:Y:1": 1,
        "H??F~zz:X:2": 2,
        "H??F~zz:Y:2": 2,
    }
)
EXPECTED_RECEIPT_SHA256 = (
    "35a6958c0aca067069497558ea0e09ee90ae00e5bb1903c73c6960cfe402241e"
)


def load_scalar() -> Any:
    spec = importlib.util.spec_from_file_location("erdos617_m64_tau3_scalar", SCALAR_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {SCALAR_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


SCALAR = load_scalar()


def all_minimum_covers(graph: nx.Graph) -> tuple[tuple[int, ...], ...]:
    edges = tuple((int(first), int(second)) for first, second in graph.edges)
    for size in range(graph.number_of_nodes() + 1):
        covers = tuple(
            cover
            for cover in itertools.combinations(range(graph.number_of_nodes()), size)
            if all(first in cover or second in cover for first, second in edges)
        )
        if covers:
            return covers
    raise AssertionError("graph has no vertex cover")


def side_count_assignments(
    graph: nx.Graph, row_sizes: tuple[int, ...]
) -> tuple[tuple[int, ...], ...]:
    domains = tuple(
        tuple(range(max(0, size - 7), min(7, size) + 1)) for size in row_sizes
    )
    edges = tuple((int(first), int(second)) for first, second in graph.edges)
    triangles = SCALAR.triangles(graph)
    result = []
    for x_values in itertools.product(*domains):
        y_values = tuple(
            row_sizes[vertex] - x_values[vertex]
            for vertex in range(graph.number_of_nodes())
        )
        if sum(x_values) < 16 or sum(y_values) < 16:
            continue
        if any(
            x_values[first] + x_values[second] < 8
            and y_values[first] + y_values[second] < 8
            for first, second in edges
        ):
            continue
        if any(
            sum(x_values[vertex] for vertex in triangle) < 8
            or sum(y_values[vertex] for vertex in triangle) < 8
            for triangle in triangles
        ):
            continue
        result.append(tuple(x_values))
    return tuple(result)


def hub_structure(graph: nx.Graph) -> tuple[int, tuple[int, int], tuple[int, ...]]:
    covers = all_minimum_covers(graph)
    if len(covers) != 1 or len(covers[0]) != 3:
        raise AssertionError(f"expected one three-vertex cover, found {covers}")
    hubs = covers[0]
    hub_edges = tuple(
        edge
        for edge in itertools.combinations(hubs, 2)
        if graph.has_edge(*edge)
    )
    if len(hub_edges) != 2:
        raise AssertionError("hub graph is not a two-edge path")
    hub_degrees = Counter(vertex for edge in hub_edges for vertex in edge)
    center = next(vertex for vertex in hubs if hub_degrees[vertex] == 2)
    leaves = tuple(vertex for vertex in hubs if vertex != center)
    universal = tuple(
        vertex
        for vertex in range(graph.number_of_nodes())
        if vertex not in hubs and all(graph.has_edge(vertex, hub) for hub in hubs)
    )
    if len(universal) not in (4, 5):
        raise AssertionError("wrong number of vertices adjacent to all hubs")
    return center, (leaves[0], leaves[1]), universal


def normalized_pattern(
    row_sizes: tuple[int, ...],
    x_values: tuple[int, ...],
    center: int,
    leaves: tuple[int, int],
    universal: tuple[int, ...],
) -> tuple[str, int]:
    hub_x = (x_values[center], x_values[leaves[0]], x_values[leaves[1]])
    if hub_x == (1, 7, 7):
        side = "Y"
        center_side = row_sizes[center] - x_values[center]
        leaf_side = tuple(row_sizes[leaf] - x_values[leaf] for leaf in leaves)
        universal_side = tuple(
            row_sizes[vertex] - x_values[vertex] for vertex in universal
        )
    elif hub_x == (6, 0, 0):
        side = "X"
        center_side = x_values[center]
        leaf_side = tuple(x_values[leaf] for leaf in leaves)
        universal_side = tuple(x_values[vertex] for vertex in universal)
    else:
        raise AssertionError(f"unexpected hub side-count pattern: {hub_x}")
    if center_side != 6 or leaf_side != (0, 0):
        raise AssertionError("normalized hub counts do not have the 6,0,0 form")
    if any(value != 2 for value in universal_side):
        raise AssertionError("all-hub rows do not have the forced two incidences")
    remainder = tuple(
        vertex
        for vertex in range(len(row_sizes))
        if vertex not in {center, *leaves, *universal}
    )
    remainder_capacity = sum(row_sizes[vertex] for vertex in remainder)
    if remainder_capacity >= 6:
        raise AssertionError("remainder has enough capacity to repair six columns")
    return side, remainder_capacity


def main() -> None:
    assignment_profile: Counter[str] = Counter()
    receipt_rows = []
    for graph6, row_sizes in EXPECTED_CASES:
        graph = nx.from_graph6_bytes(graph6.encode("ascii"))
        center, leaves, universal = hub_structure(graph)
        assignments = side_count_assignments(graph, row_sizes)
        if not assignments:
            raise AssertionError("expected scalar survivor has no assignment")
        normalized = Counter(
            normalized_pattern(
                row_sizes, assignment, center, leaves, universal
            )
            for assignment in assignments
        )
        for (side, capacity), count in normalized.items():
            assignment_profile[f"{graph6}:{side}:{capacity}"] += count
        receipt_rows.append(
            f"{graph6}:{','.join(map(str, row_sizes))}:{center}:"
            f"{','.join(map(str, leaves))}:{','.join(map(str, universal))}:"
            f"{len(assignments)}:{sorted(normalized.items())}\n"
        )

    receipt = hashlib.sha256("".join(receipt_rows).encode("ascii")).hexdigest()
    if EXPECTED_ASSIGNMENT_PROFILE and assignment_profile != EXPECTED_ASSIGNMENT_PROFILE:
        raise AssertionError(f"assignment profile mismatch: {assignment_profile}")
    if EXPECTED_RECEIPT_SHA256 and receipt != EXPECTED_RECEIPT_SHA256:
        raise AssertionError(f"receipt digest mismatch: {receipt}")
    if not EXPECTED_ASSIGNMENT_PROFILE or not EXPECTED_RECEIPT_SHA256:
        print("unpinned=1")
    print(f"assignment_profile={dict(sorted(assignment_profile.items()))}")
    print(f"receipt_sha256={receipt}")
    print("tau3_states=4 excluded=4")
    print("status=PASS")


if __name__ == "__main__":
    main()
