#!/usr/bin/env python3
"""Verify the order-26 degree-eight two-row exclusion for fixed r=9."""

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
EXPECTED_WITNESS_SHA256 = (
    "7b0d00a101125f19cb722f1c07d17ff547b7bc42eafc466bc39fe6b6854a26ac"
)
EXPECTED_ARITHMETIC_SHA256 = (
    "e14703c21b0e040c986831e3dacc74c3ff0a0588dd02ae47540454457afb1ae0"
)
EXPECTED_COVER_MASKS_CHECKED = 2_228_224


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
    counts = [0] * (1 << len(adjacency))
    for mask in range(1, 1 << len(adjacency)):
        bit = mask & -mask
        vertex = bit.bit_length() - 1
        rest = mask ^ bit
        counts[mask] = counts[rest] + (adjacency[vertex] & rest).bit_count()
    return tuple(counts)


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


def canonical_sides(
    graph: nx.Graph,
    vertex: int,
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    reduced = graph.copy()
    reduced.remove_node(vertex)
    if not nx.is_bipartite(reduced):
        return None
    colors = nx.algorithms.bipartite.color(reduced)
    first = tuple(sorted(node for node, color in colors.items() if color == 0))
    second = tuple(sorted(node for node, color in colors.items() if color == 1))
    sides = tuple(sorted((first, second)))
    if tuple(map(len, sides)) != (8, 8):
        return None
    return sides[0], sides[1]


def arithmetic_holds(p: int, q: int, h: int) -> bool:
    degree = p + q
    if not (p >= 1 and q >= 1 and degree <= 5 and h <= degree):
        return False
    inside_cover_gap = (6 - p) * (6 - q) - h
    outside_cover_gap = p * q + (5 - p) * (5 - q) - h
    return inside_cover_gap > 0 and outside_cover_gap > 0


def compatible_cover_count(
    graph: nx.Graph,
    vertex: int,
    first: tuple[int, ...],
    second: tuple[int, ...],
    p: int,
    q: int,
) -> int:
    adjacency = adjacency_masks(graph)
    all_vertices = (1 << CORE_ORDER) - 1
    first_mask = sum(1 << node for node in first)
    second_mask = sum(1 << node for node in second)
    vertex_bit = 1 << vertex
    compatible = 0
    for cover_mask in range(1 << CORE_ORDER):
        if not independent(all_vertices ^ cover_mask, adjacency):
            continue
        contains_vertex = int(bool(cover_mask & vertex_bit))
        first_count = (cover_mask & first_mask).bit_count()
        second_count = (cover_mask & second_mask).bit_count()
        if (
            first_count + contains_vertex <= p + 3
            and second_count + contains_vertex <= q + 3
        ):
            compatible += 1
    return compatible


def witness_rows(line: bytes, graph: nx.Graph) -> tuple[tuple[str, ...], int]:
    rows = []
    cover_masks_checked = 0
    for vertex in range(CORE_ORDER):
        sides = canonical_sides(graph, vertex)
        if sides is None:
            continue
        first, second = sides
        p = sum(graph.has_edge(vertex, node) for node in first)
        q = sum(graph.has_edge(vertex, node) for node in second)
        degree = p + q
        missing = sum(
            not graph.has_edge(x_vertex, y_vertex)
            for x_vertex in first
            for y_vertex in second
        )
        rectangle_missing = all(
            not graph.has_edge(x_vertex, y_vertex)
            for x_vertex in first
            if graph.has_edge(vertex, x_vertex)
            for y_vertex in second
            if graph.has_edge(vertex, y_vertex)
        )
        if not rectangle_missing:
            raise AssertionError("triangle-free neighborhood rectangle failed")
        if missing != 64 - graph.number_of_edges() + degree:
            raise AssertionError("cross-edge ledger failed")
        if arithmetic_holds(p, q, missing):
            compatible = compatible_cover_count(
                graph,
                vertex,
                first,
                second,
                p,
                q,
            )
            cover_masks_checked += 1 << CORE_ORDER
            if compatible:
                raise AssertionError(
                    f"two-row cover counterexample: {line!r}, {vertex}, "
                    f"count={compatible}"
                )
            rows.append(
                f"{line.decode('ascii')}:{vertex}:"
                f"{','.join(map(str, first))}:"
                f"{','.join(map(str, second))}:"
                f"{p}:{q}:{missing}\n"
            )
    if not rows:
        raise AssertionError(f"core has no two-row witness: {line!r}")
    return tuple(sorted(rows)), cover_masks_checked


def corruption_tests() -> int:
    checks = 0
    for p in range(1, 5):
        for q in range(1, 5):
            degree = p + q
            if degree > 5:
                continue
            if not arithmetic_holds(p, q, degree):
                raise AssertionError((p, q, degree))
            checks += 1
    if arithmetic_holds(1, 5, 6):
        raise AssertionError("degree-six boundary was incorrectly accepted")
    checks += 1
    if arithmetic_holds(0, 4, 4):
        raise AssertionError("zero-side neighborhood was incorrectly accepted")
    checks += 1
    if arithmetic_holds(2, 2, 5):
        raise AssertionError("h>d corruption was incorrectly accepted")
    checks += 1
    return checks


def arithmetic_rows() -> tuple[str, ...]:
    rows = []
    for p in range(1, 5):
        for q in range(1, 5):
            degree = p + q
            if degree > 5:
                continue
            inside_gap = (6 - p) * (6 - q) - degree
            outside_gap = p * q + (5 - p) * (5 - q) - degree
            if inside_gap <= 0 or outside_gap <= 0:
                raise AssertionError((p, q, inside_gap, outside_gap))
            rows.append(f"{p}:{q}:{degree}:{inside_gap}:{outside_gap}\n")
    return tuple(rows)


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
            (line, graph)
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

    catalog_sha256 = hashlib.sha256(
        b"\n".join(line for line, _ in cases) + b"\n"
    ).hexdigest()
    checked_witnesses = tuple(witness_rows(line, graph) for line, graph in cases)
    all_rows = tuple(row for rows, _ in checked_witnesses for row in rows)
    cover_masks_checked = sum(count for _, count in checked_witnesses)
    witness_sha256 = hashlib.sha256(
        "".join(all_rows).encode("ascii")
    ).hexdigest()
    exact_arithmetic_rows = arithmetic_rows()
    arithmetic_sha256 = hashlib.sha256(
        "".join(exact_arithmetic_rows).encode("ascii")
    ).hexdigest()
    corruption_count = corruption_tests()

    if not args.allow_unpinned:
        expected = (
            EXPECTED_CATALOG_SHA256,
            EXPECTED_WITNESS_SHA256,
            EXPECTED_ARITHMETIC_SHA256,
            EXPECTED_COVER_MASKS_CHECKED,
        )
        actual = (
            catalog_sha256,
            witness_sha256,
            arithmetic_sha256,
            cover_masks_checked,
        )
        if actual != expected:
            raise AssertionError(f"unpinned two-row receipt: {actual}")

    print(f"raw_graphs={len(raw_lines)} valid_cores={len(cases)}")
    print(f"level_profile={dict(sorted(level_profile.items()))}")
    print(f"witness_rows={len(all_rows)}")
    print(f"cover_masks_checked={cover_masks_checked}")
    print(f"arithmetic_cases={len(exact_arithmetic_rows)}")
    print(f"corruption_tests={corruption_count}")
    print(f"catalog_sha256={catalog_sha256}")
    print(f"witness_sha256={witness_sha256}")
    print(f"arithmetic_sha256={arithmetic_sha256}")
    for row in all_rows:
        print(f"witness={row.strip()}")
    print("status=PASS")


if __name__ == "__main__":
    main()
