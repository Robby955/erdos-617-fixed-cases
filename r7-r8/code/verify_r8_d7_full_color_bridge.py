#!/usr/bin/env python3
"""Arithmetic audit for R8_D7_FULL_COLOR_BRIDGE.md.

This script checks the split equality cores, their minimum covers, the
star-shell equality arithmetic, and the strengthened colored recursion.
It is not a substitute for the human proof or its source dependency.
"""

from __future__ import annotations

from functools import lru_cache
from itertools import combinations
from math import comb


def ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def turan_complement_floor(parts: int, order: int) -> int:
    quotient, remainder = divmod(order, parts)
    return (parts - remainder) * comb(quotient, 2) + remainder * comb(
        quotient + 1, 2
    )


def colored_cap(order: int) -> int:
    return comb(order, 2) - 7 * turan_complement_floor(8, order)


def exact_thresholds() -> dict[int, int | None]:
    thresholds: dict[int, int | None] = {2: 0}
    for layer in range(3, 8):
        previous = thresholds[layer - 1]
        if previous is None:
            thresholds[layer] = None
            continue
        coefficient = 8 * (layer + 1) - 2 * layer - previous + 1
        constant = 8 * layer * (layer + previous - 2) - 14 * (layer - 1)
        threshold = max(1, constant // coefficient + 1)
        thresholds[layer] = threshold if threshold < 8 else None
    return thresholds


def scalar_floor(independence_cap: int, order: int) -> int:
    value = turan_complement_floor(independence_cap, order)
    if order >= 8 * independence_cap + 1:
        return value + order // independence_cap
    if order > 7 * independence_cap:
        return value + order // independence_cap - 1
    return value


def star_floor(degree: int) -> int:
    if degree < 7:
        return comb(degree + 1, 2)
    if degree == 7:
        return 29
    return degree + ceil_div(10 * comb(degree, 2), 8)


def recursive_floor(
    p3_23: int | None = None,
    p3_24: int | None = None,
):
    thresholds = exact_thresholds()

    @lru_cache(maxsize=None)
    def floor(independence_cap: int, order: int) -> int | None:
        if order < 0:
            return None
        if independence_cap == 0:
            return 0 if order == 0 else None
        if independence_cap == 1:
            return comb(order, 2) if order <= 7 else None

        threshold = thresholds.get(independence_cap)
        if (
            threshold is not None
            and order >= 8 * independence_cap + threshold
        ):
            return None

        branches: list[int] = []
        for degree in range(order):
            remainder = floor(independence_cap - 1, order - 1 - degree)
            if remainder is None:
                continue
            branches.append(
                max(
                    remainder + star_floor(degree),
                    ceil_div(order * degree, 2),
                )
            )
        if not branches:
            return None

        value = max(scalar_floor(independence_cap, order), min(branches))
        if (independence_cap, order) == (3, 23) and p3_23 is not None:
            value = max(value, p3_23)
        if (independence_cap, order) == (3, 24) and p3_24 is not None:
            value = max(value, p3_24)
        return None if value > colored_cap(order) else value

    return floor


def split_core(split_size: int) -> set[tuple[int, int]]:
    """Return the 15-vertex Kang-Pikhurko equality core L."""
    p_vertices = tuple(range(6))
    q_vertices = tuple(range(6, 13))
    x_vertex = 13
    y_vertex = 14
    x_neighbors = set(q_vertices[:split_size])
    edges: set[tuple[int, int]] = set()
    vertices = (*p_vertices, *q_vertices, x_vertex, y_vertex)
    for first, second in combinations(vertices, 2):
        edge = (first, second)
        if (
            (first in p_vertices and second in q_vertices)
            or (second in p_vertices and first in q_vertices)
            or set(edge) == {x_vertex, y_vertex}
            or (
                x_vertex in edge
                and next(vertex for vertex in edge if vertex != x_vertex)
                in x_neighbors
            )
            or (
                y_vertex in edge
                and next(vertex for vertex in edge if vertex != y_vertex)
                in set(q_vertices) - x_neighbors
            )
        ):
            edges.add(edge)
    return edges


def induced_edges(vertices: set[int], edges: set[tuple[int, int]]) -> int:
    return sum(u in vertices and v in vertices for u, v in edges)


def independent(vertices: set[int], edges: set[tuple[int, int]]) -> bool:
    return induced_edges(vertices, edges) == 0


def check_split_core_classification() -> None:
    optimal_old_parts = [
        (first, 14 - first)
        for first in range(2, 8)
        if first <= 14 - first <= first + 1
    ]
    assert optimal_old_parts == [(7, 7)]

    expected_cover_edges = {
        1: [1, 1, 6, 6],
        2: [1, 2, 5],
        3: [1, 3, 4],
    }
    expected_high_counts = {1: 2, 2: 1, 3: 0}

    for split_size in range(1, 4):
        edges = split_core(split_size)
        assert len(edges) == 50

        degrees = [sum(vertex in edge for edge in edges) for vertex in range(15)]
        assert sorted(degrees) == sorted(
            [7] * 13 + [split_size + 1, 8 - split_size]
        )
        assert all(
            not all(tuple(sorted(edge)) in edges for edge in combinations(triple, 2))
            for triple in combinations(range(15), 3)
        )
        assert not any(
            independent(set(vertices), edges)
            for vertices in combinations(range(15), 8)
        )

        p_vertex = 0
        q_in_x = 6
        q_in_y = 6 + split_size
        x_vertex = 13
        y_vertex = 14
        odd_cycle = (x_vertex, y_vertex, q_in_y, p_vertex, q_in_x)
        assert all(
            tuple(sorted((odd_cycle[index], odd_cycle[(index + 1) % 5]))) in edges
            for index in range(5)
        )

        independent_sevens = [
            set(vertices)
            for vertices in combinations(range(15), 7)
            if independent(set(vertices), edges)
        ]
        covers = [set(range(15)) - vertices for vertices in independent_sevens]
        cover_edges = sorted(induced_edges(cover, edges) for cover in covers)
        assert cover_edges == expected_cover_edges[split_size]

        high_covers = [cover for cover in covers if induced_edges(cover, edges) >= 5]
        assert len(high_covers) == expected_high_counts[split_size]

        for high_cover in high_covers:
            witnesses = []
            for low_cover in covers:
                low_edges = induced_edges(low_cover, edges)
                overlap = len(high_cover & low_cover)
                if overlap > 2 * (1 + low_edges):
                    witnesses.append((low_edges, overlap))
            assert witnesses


def check_star_shell_equality() -> None:
    for leaves in range(1, 7):
        possible: list[tuple[int, tuple[int, ...], int]] = []
        for center_degree in range(leaves, 16):
            leaf_minimum = max(1, 8 - center_degree)
            leaf_degrees = (leaf_minimum,) * leaves
            total = center_degree + sum(leaf_degrees)
            possible.append((total, leaf_degrees, center_degree))

        minimum = min(total for total, _, _ in possible)
        assert minimum == leaves + 7
        equality_rows = [row for row in possible if row[0] == minimum]
        assert equality_rows
        for _, leaf_degrees, center_degree in equality_rows:
            assert all(center_degree + degree == 8 for degree in leaf_degrees)


def check_outer_budgets_and_propagation() -> None:
    assert colored_cap(10) == 31
    assert exact_thresholds() == {
        2: 0,
        3: 1,
        4: 2,
        5: 4,
        6: None,
        7: None,
    }

    baseline = recursive_floor()
    p324_only = recursive_floor(p3_24=106)
    strengthened = recursive_floor(p3_23=91, p3_24=106)

    outer_nodes = ((7, 57), (6, 49), (5, 41), (4, 33))
    assert [baseline(*node) for node in outer_nodes] == [228, 199, 170, 141]
    assert [p324_only(*node) for node in outer_nodes] == [229, 200, 171, 149]
    assert [strengthened(*node) for node in outer_nodes] == [235, 206, 177, 149]

    propagated = {
        (4, 31): 120,
        (4, 32): 134,
        (4, 33): 149,
        (5, 40): 163,
        (5, 41): 177,
        (5, 42): 189,
        (5, 43): 203,
        (6, 48): 192,
        (6, 49): 206,
        (6, 50): 218,
        (7, 57): 235,
    }
    assert {node: strengthened(*node) for node in propagated} == propagated

    least_color_edges = 260
    degree = 7
    first_upper = least_color_edges - degree - comb(degree, 2)
    peel_uppers = [first_upper - blocks * comb(8, 2) for blocks in range(4)]
    assert first_upper == 232
    assert peel_uppers == [232, 204, 176, 148]
    assert all(
        strengthened(*node) > upper
        for node, upper in zip(outer_nodes, peel_uppers, strict=True)
    )
    assert 8 - 4 == 4


def main() -> None:
    check_split_core_classification()
    check_star_shell_equality()
    check_outer_budgets_and_propagation()
    print("r8_d7_split_equality_cores=VERIFIED")
    print("r8_d7_star_shell_arithmetic=VERIFIED")
    print("r8_d7_proposed_floor=P3(23):91")
    print("r8_d7_imported_floor=P3(24):106")
    print("r8_d7_outer_floors=235,206,177,149")
    print("r8_d7_peel_uppers=232,204,176,148")
    print("r8_d7_full_color_bridge_arithmetic=VERIFIED")


if __name__ == "__main__":
    main()
