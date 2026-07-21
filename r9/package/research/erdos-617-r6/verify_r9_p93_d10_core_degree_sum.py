#!/usr/bin/env python3
"""Verify the fixed-r=9 order-27 degree-ten core degree-sum reduction."""

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
CORE_ORDER = 16
EXPECTED_RAW = 336
EXPECTED_CORES = 332
EXPECTED_SURVIVORS = 50
EXPECTED_LEVEL_PROFILE: Counter[int] = Counter(
    {56: 179, 57: 80, 58: 39, 59: 17, 60: 9, 61: 4, 62: 2, 63: 1, 64: 1}
)
EXPECTED_MINIMUM_SUM_PROFILE: Counter[int] = Counter(
    {10: 19, 11: 102, 12: 161, 13: 38, 14: 10, 15: 1, 16: 1}
)
EXPECTED_SURVIVOR_LEVEL_PROFILE: Counter[int] = Counter(
    {56: 8, 57: 8, 58: 10, 59: 9, 60: 7, 61: 4, 62: 2, 63: 1, 64: 1}
)
EXPECTED_CATALOG_SHA256 = (
    "24a2b9d62d8c7612280188c93be9164e7306ae0c83db12a3872c061bde303510"
)
EXPECTED_SURVIVOR_SHA256 = (
    "6d573529569ecc950e4e9e98c89d9ae3c95273089bba8d3cd63b1d83e862f508"
)
EXPECTED_CLASSIFICATION_SHA256 = (
    "f6aa267f6cc54dccc04bbfe66068788cc6f75ea528a04b8d63bdb1b9d5795c2a"
)


def p9(order: int) -> int:
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


def induced_edges(mask: int, adjacency: tuple[int, ...]) -> int:
    return sum(
        (adjacency[vertex] & mask).bit_count()
        for vertex in range(len(adjacency))
        if mask >> vertex & 1
    ) // 2


def valid_core(graph: nx.Graph) -> bool:
    if graph.number_of_nodes() != CORE_ORDER:
        return False
    degrees = [int(degree) for _, degree in graph.degree()]
    if min(degrees) < 5 or max(degrees) > 8:
        return False
    if any(nx.triangles(graph).values()):
        return False
    adjacency = adjacency_masks(graph)
    if any(
        independent(sum(1 << vertex for vertex in vertices), adjacency)
        for vertices in itertools.combinations(range(CORE_ORDER), 9)
    ):
        return False
    for order in range(10, CORE_ORDER + 1):
        required = 8 * p9(order)
        if any(
            induced_edges(
                sum(1 << vertex for vertex in vertices),
                adjacency,
            )
            < required
            for vertices in itertools.combinations(range(CORE_ORDER), order)
        ):
            return False
    return True


def minimum_edge_degree_sum(graph: nx.Graph) -> int:
    return min(
        int(graph.degree(first)) + int(graph.degree(second))
        for first, second in graph.edges
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--allow-unpinned", action="store_true")
    args = parser.parse_args()

    raw_lines = tuple(
        subprocess.check_output(
            [
                str(args.geng),
                "-q",
                "-t",
                "-d5",
                "-D8",
                str(CORE_ORDER),
                "56:64",
            ]
        ).splitlines()
    )
    if len(raw_lines) != EXPECTED_RAW:
        raise AssertionError(f"wrong raw count: {len(raw_lines)}")
    cases = tuple(
        sorted(
            (line, graph)
            for line in raw_lines
            for graph in (nx.from_graph6_bytes(line),)
            if valid_core(graph)
        )
    )
    if len(cases) != EXPECTED_CORES:
        raise AssertionError(f"wrong core count: {len(cases)}")

    level_profile = Counter(graph.number_of_edges() for _, graph in cases)
    minimum_sum_profile: Counter[int] = Counter()
    classification_rows = []
    survivors = []
    for line, graph in cases:
        minimum_sum = minimum_edge_degree_sum(graph)
        minimum_sum_profile[minimum_sum] += 1
        degrees = ",".join(
            map(str, sorted(int(degree) for _, degree in graph.degree()))
        )
        classification_rows.append(
            f"{line.decode('ascii')}:{graph.number_of_edges()}:"
            f"{minimum_sum}:{degrees}\n"
        )
        if minimum_sum >= 13:
            survivors.append((line, graph))

    survivor_level_profile = Counter(
        graph.number_of_edges() for _, graph in survivors
    )
    if (
        level_profile != EXPECTED_LEVEL_PROFILE
        or minimum_sum_profile != EXPECTED_MINIMUM_SUM_PROFILE
        or len(survivors) != EXPECTED_SURVIVORS
        or survivor_level_profile != EXPECTED_SURVIVOR_LEVEL_PROFILE
    ):
        raise AssertionError(
            (
                level_profile,
                minimum_sum_profile,
                len(survivors),
                survivor_level_profile,
            )
        )

    catalog_sha256 = hashlib.sha256(
        b"\n".join(line for line, _ in cases) + b"\n"
    ).hexdigest()
    survivor_sha256 = hashlib.sha256(
        b"\n".join(line for line, _ in survivors) + b"\n"
    ).hexdigest()
    classification_sha256 = hashlib.sha256(
        "".join(classification_rows).encode("ascii")
    ).hexdigest()

    if not args.allow_unpinned:
        expected = (
            EXPECTED_CATALOG_SHA256,
            EXPECTED_SURVIVOR_SHA256,
            EXPECTED_CLASSIFICATION_SHA256,
        )
        actual = (catalog_sha256, survivor_sha256, classification_sha256)
        if actual != expected:
            raise AssertionError(f"unpinned degree-sum receipt: {actual}")

    print(f"raw_graphs={len(raw_lines)} valid_cores={len(cases)}")
    print(f"level_profile={dict(sorted(level_profile.items()))}")
    print(f"minimum_sum_profile={dict(sorted(minimum_sum_profile.items()))}")
    print(f"survivors={len(survivors)}")
    print(
        f"survivor_level_profile={dict(sorted(survivor_level_profile.items()))}"
    )
    print(f"catalog_sha256={catalog_sha256}")
    print(f"survivor_sha256={survivor_sha256}")
    print(f"classification_sha256={classification_sha256}")
    for line, graph in survivors:
        print(
            f"survivor={line.decode('ascii')}:"
            f"{graph.number_of_edges()}:"
            f"{minimum_edge_degree_sum(graph)}"
        )
    print("status=PASS")


if __name__ == "__main__":
    main()
