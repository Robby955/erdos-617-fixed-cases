#!/usr/bin/env python3
"""Reconstruct the 17-vertex core catalog in the order-26 degree-eight branch."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import math
from pathlib import Path
import subprocess

import networkx as nx  # type: ignore[import-untyped]


R = 9
CORE_ORDER = 17
EXPECTED_RAW = 36
EXPECTED_CORES = 14
EXPECTED_LEVEL_PROFILE: Counter[int] = Counter({64: 10, 65: 4})
EXPECTED_CATALOG_SHA256 = (
    "707a0cdf6eb73ff43902ce86bf36d491050363506534d74a2cad02737f1a5829"
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "4a7c7abe0a5c6eea65d98792d33d3d122511964b568d9cf70e168fbb4743ac45"
)
EXPECTED_INDEPENDENT_EIGHT_PROFILE: Counter[int] = Counter({2: 1, 3: 10, 4: 3})
EXPECTED_REDUCED_EDGE_PROFILE: Counter[int] = Counter(
    {59: 1, 60: 5, 61: 4, 62: 3, 63: 1}
)


def p_r(order: int) -> int:
    quotient, remainder = divmod(order, R)
    return (R - remainder) * math.comb(quotient, 2) + remainder * math.comb(
        quotient + 1,
        2,
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


def induced_edge_counts(adjacency: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * (1 << len(adjacency))
    for mask in range(1, 1 << len(adjacency)):
        bit = mask & -mask
        vertex = bit.bit_length() - 1
        rest = mask ^ bit
        result[mask] = result[rest] + (adjacency[vertex] & rest).bit_count()
    return tuple(result)


def valid_core(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != CORE_ORDER:
        return False
    if any(nx.triangles(graph).values()):
        return False
    if max(int(degree) for _, degree in graph.degree()) > R - 1:
        return False
    adjacency = adjacency_masks(graph)
    if any(
        independent(sum(1 << vertex for vertex in vertices), adjacency)
        for vertices in itertools.combinations(range(CORE_ORDER), R)
    ):
        return False
    edge_counts = induced_edge_counts(adjacency)
    for order in range(R + 1, CORE_ORDER + 1):
        required = (R - 1) * p_r(order)
        if any(
            edge_counts[sum(1 << vertex for vertex in vertices)] < required
            for vertices in itertools.combinations(range(CORE_ORDER), order)
        ):
            return False
    return True


def independent_eight_count(graph: nx.Graph) -> int:
    adjacency = adjacency_masks(graph)
    return sum(
        independent(sum(1 << vertex for vertex in vertices), adjacency)
        for vertices in itertools.combinations(range(CORE_ORDER), 8)
    )


def reduced_bipartite_profile(
    graph: nx.Graph,
) -> tuple[int, int, tuple[int, ...]]:
    minimum_degree = min(int(degree) for _, degree in graph.degree())
    candidates = []
    for vertex, degree in graph.degree():
        if int(degree) != minimum_degree:
            continue
        reduced = graph.copy()
        reduced.remove_node(vertex)
        if not nx.is_bipartite(reduced):
            continue
        coloring = nx.algorithms.bipartite.color(reduced)
        side_sizes = tuple(
            sorted(
                sum(color == side for color in coloring.values())
                for side in (0, 1)
            )
        )
        if side_sizes != (8, 8):
            continue
        candidates.append(int(vertex))
    if not candidates:
        raise AssertionError("core lacks the required 8+8 reduction")
    return minimum_degree, graph.number_of_edges() - minimum_degree, tuple(candidates)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--allow-unpinned", action="store_true")
    args = parser.parse_args()

    raw_lines = tuple(
        subprocess.check_output(
            [str(args.geng), "-q", "-t", "-D8", str(CORE_ORDER), "64:65"]
        ).splitlines()
    )
    if len(raw_lines) != EXPECTED_RAW:
        raise AssertionError(f"wrong raw count: {len(raw_lines)}")
    cases = tuple(
        sorted(
            (
                line,
                graph,
            )
            for line in raw_lines
            for graph in (nx.from_graph6_bytes(line),)
            if valid_core(graph)
        )
    )
    if len(cases) != EXPECTED_CORES:
        raise AssertionError(f"wrong core count: {len(cases)}")
    level_profile = Counter(graph.number_of_edges() for _, graph in cases)
    if level_profile != EXPECTED_LEVEL_PROFILE:
        raise AssertionError(f"wrong level profile: {level_profile}")

    catalog_digest = hashlib.sha256(
        b"\n".join(line for line, _ in cases) + b"\n"
    ).hexdigest()
    independent_profile: Counter[int] = Counter()
    reduced_profile: Counter[int] = Counter()
    rows = []
    for line, graph in cases:
        independent_count = independent_eight_count(graph)
        minimum_degree, reduced_edges, witnesses = reduced_bipartite_profile(graph)
        independent_profile[independent_count] += 1
        reduced_profile[reduced_edges] += 1
        degrees = ",".join(
            map(str, sorted(int(degree) for _, degree in graph.degree()))
        )
        rows.append(
            f"{line.decode('ascii')}:{graph.number_of_edges()}:{degrees}:"
            f"{independent_count}:{minimum_degree}:{reduced_edges}:"
            f"{','.join(map(str, witnesses))}\n"
        )
    classification_digest = hashlib.sha256(
        "".join(rows).encode("ascii")
    ).hexdigest()

    if not args.allow_unpinned:
        expected = (
            EXPECTED_CATALOG_SHA256,
            EXPECTED_CLASSIFICATION_SHA256,
            EXPECTED_INDEPENDENT_EIGHT_PROFILE,
            EXPECTED_REDUCED_EDGE_PROFILE,
        )
        actual = (
            catalog_digest,
            classification_digest,
            independent_profile,
            reduced_profile,
        )
        if actual != expected:
            raise AssertionError(f"unpinned core-catalog receipt: {actual}")

    print(f"raw_graphs={len(raw_lines)} valid_cores={len(cases)}")
    print(f"level_profile={dict(sorted(level_profile.items()))}")
    print(f"independent_eight_profile={dict(sorted(independent_profile.items()))}")
    print(f"reduced_edge_profile={dict(sorted(reduced_profile.items()))}")
    print(f"catalog_sha256={catalog_digest}")
    print(f"classification_sha256={classification_digest}")
    for row in rows:
        print(f"core={row.strip()}")
    print("status=PASS")


if __name__ == "__main__":
    main()
