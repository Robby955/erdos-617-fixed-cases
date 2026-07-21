#!/usr/bin/env python3
"""Replay the fixed-r=9 degree-eight neighborhood-defect wall."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from itertools import combinations


R = 9
TARGET = 0
ALL_COLORS = frozenset(range(R))
OTHER_COLORS = tuple(range(1, R))
V = 0
B = tuple(range(9))
N = tuple(range(1, 9))
U = tuple(range(9, 82))
MISSING_EDGE_ORDER = (
    (1, 2),
    (3, 4),
    (5, 6),
    (7, 8),
    (1, 3),
)
BOUNDS = (332, 295, 258, 221, 184)
UPPERS = (333, 297, 261, 225, 189)


def edge(left: int, right: int) -> tuple[int, int]:
    assert left != right
    return (left, right) if left < right else (right, left)


@dataclass
class Witness:
    block_count: int
    defect: int
    colors: dict[tuple[int, int], int]
    blocks: tuple[tuple[int, ...], ...]
    reservoir: tuple[int, ...]
    stub_edges: tuple[tuple[int, int], ...]


def cyclic_color(difference: int) -> int:
    residue = difference % 9
    return 1 if residue == 0 else residue


def set_color(
    colors: dict[tuple[int, int], int],
    left: int,
    right: int,
    color: int,
) -> None:
    key = edge(left, right)
    assert key not in colors
    assert color in ALL_COLORS
    colors[key] = color


def colors_on(
    vertices: tuple[int, ...],
    colors: dict[tuple[int, int], int],
) -> frozenset[int]:
    keys = [edge(left, right) for left, right in combinations(vertices, 2)]
    assert all(key in colors for key in keys)
    return frozenset(colors[key] for key in keys)


def target_edges_on(
    vertices: tuple[int, ...],
    colors: dict[tuple[int, int], int],
) -> int:
    keys = [edge(left, right) for left, right in combinations(vertices, 2)]
    assert all(key in colors for key in keys)
    return sum(colors[key] == TARGET for key in keys)


def build_witness(block_count: int, defect: int) -> Witness:
    assert 0 <= block_count <= 4
    assert 0 <= defect <= block_count + 1
    colors: dict[tuple[int, int], int] = {}

    missing = frozenset(MISSING_EDGE_ORDER[:defect])
    for neighbor in N:
        set_color(colors, V, neighbor, TARGET)
    for left, right in combinations(N, 2):
        key = edge(left, right)
        if key in missing:
            missing_index = MISSING_EDGE_ORDER.index(key)
            set_color(colors, left, right, 1 + missing_index)
        else:
            set_color(colors, left, right, TARGET)

    block_vertices = U[: 9 * block_count]
    blocks = tuple(
        tuple(block_vertices[9 * index : 9 * (index + 1)])
        for index in range(block_count)
    )
    reservoir = tuple(U[9 * block_count :])
    assert len(reservoir) == 73 - 9 * block_count >= 37

    incidences = tuple(
        endpoint
        for missing_edge in MISSING_EDGE_ORDER[:defect]
        for endpoint in missing_edge
    )
    assert len(incidences) == 2 * defect <= len(reservoir)
    stub_edges = tuple(
        edge(endpoint, reservoir[index])
        for index, endpoint in enumerate(incidences)
    )
    stub_by_reservoir = {
        reservoir[index]: endpoint for index, endpoint in enumerate(incidences)
    }

    # Color B to each peeled block by a cyclic 8-color matrix.
    for block in blocks:
        for b_index, b_vertex in enumerate(B):
            for q_index, q_vertex in enumerate(block):
                set_color(
                    colors,
                    b_vertex,
                    q_vertex,
                    cyclic_color(q_index - b_index),
                )

    # Each reservoir star from B sees all eight non-target colors. A stub
    # vertex has one target edge and exactly eight non-target edges.
    for reservoir_vertex in reservoir:
        target_neighbor = stub_by_reservoir.get(reservoir_vertex)
        available = [b_vertex for b_vertex in B if b_vertex != target_neighbor]
        for b_vertex in B:
            if b_vertex == target_neighbor:
                set_color(colors, b_vertex, reservoir_vertex, TARGET)
            else:
                position = available.index(b_vertex)
                set_color(
                    colors,
                    b_vertex,
                    reservoir_vertex,
                    OTHER_COLORS[position % len(OTHER_COLORS)],
                )

    # Make each peeled block a target K9.
    for block in blocks:
        for left, right in combinations(block, 2):
            set_color(colors, left, right, TARGET)

    # Between two blocks, the cyclic matrix gives all eight colors in every
    # row and column.
    for first_index, second_index in combinations(range(block_count), 2):
        first = blocks[first_index]
        second = blocks[second_index]
        for left_index, left in enumerate(first):
            for right_index, right in enumerate(second):
                set_color(
                    colors,
                    left,
                    right,
                    cyclic_color(right_index - left_index),
                )

    # Every reservoir vertex sees all eight colors from every peeled block.
    for block in blocks:
        for reservoir_vertex in reservoir:
            for block_index, block_vertex in enumerate(block):
                set_color(
                    colors,
                    block_vertex,
                    reservoir_vertex,
                    OTHER_COLORS[block_index % len(OTHER_COLORS)],
                )

    return Witness(
        block_count=block_count,
        defect=defect,
        colors=colors,
        blocks=blocks,
        reservoir=reservoir,
        stub_edges=stub_edges,
    )


def audit_witness(witness: Witness) -> None:
    colors = witness.colors
    defect = witness.defect

    target_n_edges = sum(
        colors[edge(left, right)] == TARGET for left, right in combinations(N, 2)
    )
    assert target_n_edges == 28 - defect

    target_cross = sum(
        colors.get(edge(neighbor, outside)) == TARGET
        for neighbor in N
        for outside in U
    )
    assert target_cross == 2 * defect
    assert len(witness.stub_edges) == target_cross
    assert all(colors[stub] == TARGET for stub in witness.stub_edges)

    for neighbor in N:
        target_degree = sum(
            colors.get(edge(neighbor, other)) == TARGET
            for other in range(82)
            if other != neighbor
        )
        assert target_degree == 8
    assert sum(colors.get(edge(V, other)) == TARGET for other in U + N) == 8

    b_target_edges = target_edges_on(B, colors)
    assert b_target_edges == 36 - defect
    if defect == 0:
        assert b_target_edges == 36

    for outside in U:
        local = B + (outside,)
        assert colors_on(local, colors) == ALL_COLORS
        local_target = target_edges_on(local, colors)
        assert local_target in {36 - defect, 37 - defect}
        assert 1 <= local_target <= 37

    for block in witness.blocks:
        assert target_edges_on(block, colors) == 36
        assert all(
            colors[edge(block_vertex, b_vertex)] != TARGET
            for block_vertex in block
            for b_vertex in B
        )
        for outside in B + tuple(
            vertex for vertex in U if vertex not in frozenset(block)
        ):
            local = block + (outside,)
            assert colors_on(local, colors) == ALL_COLORS
            assert 1 <= target_edges_on(local, colors) <= 37


def check_charge_lemma() -> None:
    for degree in range(1, 9):
        clique_edges = degree * (degree - 1) // 2
        for defect in range(clique_edges + 1):
            target_n_edges = clique_edges - defect
            minimum_cross = degree * (degree - 1) - 2 * target_n_edges
            assert minimum_cross == 2 * defect
            exact_charge = degree + target_n_edges + minimum_cross
            canonical_charge = degree + clique_edges
            assert exact_charge - canonical_charge == defect


def check_survivor_table() -> None:
    assert tuple(
        bound - upper for bound, upper in zip(BOUNDS, UPPERS, strict=True)
    ) == (-1, -2, -3, -4, -5)

    survivor_cells: list[tuple[int, int]] = []
    survivor_triples: list[tuple[int, int, int]] = []
    for block_count in range(5):
        for defect in range(29):
            q_only_margin = defect - block_count - 1
            if q_only_margin <= 0:
                survivor_cells.append((block_count, defect))
                for cross in range(2 * defect, defect + block_count + 2):
                    exact_margin = cross - defect - block_count - 1
                    assert exact_margin <= 0
                    survivor_triples.append((block_count, defect, cross))
            else:
                assert defect >= block_count + 2

    expected = tuple(
        (block_count, defect)
        for block_count in range(5)
        for defect in range(block_count + 2)
    )
    assert tuple(survivor_cells) == expected
    assert len(survivor_cells) == 20
    assert len(survivor_triples) == 55


def expect_assertion(action: Callable[[], None]) -> None:
    try:
        action()
    except AssertionError:
        return
    raise AssertionError("deliberate corruption was not detected")


def corruption_tests() -> None:
    degree_corruption = build_witness(0, 1)
    stub = degree_corruption.stub_edges[0]
    degree_corruption.colors[stub] = 1
    expect_assertion(lambda: audit_witness(degree_corruption))

    color_corruption = build_witness(1, 0)
    first_block_vertex = color_corruption.blocks[0][0]
    color_eight_edge = next(
        edge(b_vertex, first_block_vertex)
        for b_vertex in B
        if color_corruption.colors[edge(b_vertex, first_block_vertex)] == 8
    )
    color_corruption.colors[color_eight_edge] = 1
    expect_assertion(lambda: audit_witness(color_corruption))


def main() -> None:
    check_charge_lemma()
    check_survivor_table()
    witness_count = 0
    for block_count in range(5):
        for defect in range(block_count + 2):
            witness = build_witness(block_count, defect)
            audit_witness(witness)
            witness_count += 1
    corruption_tests()
    print(
        "R9_OUTER_D8_NEIGHBORHOOD_DEFECT PASS "
        f"survivor_cells={witness_count} survivor_triples=55 "
        "q_range_by_j=2,3,4,5,6 "
        "shell_witnesses=20 corruption=2 "
        "scope=partial_shell_not_full_outer_coloring"
    )


if __name__ == "__main__":
    main()
