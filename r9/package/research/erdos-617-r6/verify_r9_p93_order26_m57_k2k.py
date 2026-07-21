#!/usr/bin/env python3
"""Verify the reduced m=57, K_{2,k}-shell obstruction for k=4,5,6.

This verifier is independent of the exploratory fixed-shell SAT runner.  It
reconstructs the 120 unlabelled core graphs, proves the elementary shell
equality reduction arithmetically, and exhausts the remaining minimum-cover
configurations directly.  It emits no claim about the other core levels or
about fixed r=9.
"""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import math
from pathlib import Path
import subprocess

import networkx as nx  # type: ignore[import-untyped]


R = 9
CORE_ORDER = 16
CORE_EDGES = 57
FULL_MASK = (1 << CORE_ORDER) - 1
SURVIVOR_SHELLS = {
    4: b"H???Fbo",
    5: b"H???Frw",
    6: b"H???Fz{",
}


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
    """Check every core condition used in the order-26 reduction."""
    if graph.number_of_nodes() != CORE_ORDER:
        return False
    if graph.number_of_edges() != CORE_EDGES:
        return False
    adjacency = adjacency_masks(graph)
    if any(nx.triangles(graph).values()):
        return False
    if max(dict(graph.degree()).values()) > R - 1:
        return False
    for vertices in itertools.combinations(range(CORE_ORDER), R):
        mask = sum(1 << vertex for vertex in vertices)
        if independent(mask, adjacency):
            return False
    for subset_order in range(R + 1, CORE_ORDER + 1):
        minimum = (R - 1) * p_r(subset_order)
        for vertices in itertools.combinations(
            range(CORE_ORDER), subset_order
        ):
            mask = sum(1 << vertex for vertex in vertices)
            if induced_edges(mask, adjacency) < minimum:
                return False
    return True


def generate_cores(geng: Path) -> tuple[tuple[bytes, nx.Graph], ...]:
    command = [str(geng), "-q", "-t", "-D8", "16", "57:57"]
    cases = []
    for line in subprocess.check_output(command).splitlines():
        graph = nx.from_graph6_bytes(line)
        if valid_core(graph):
            cases.append((line, graph))
    return tuple(sorted(cases, key=lambda case: case[0]))


def verify_shell_shapes() -> None:
    for leaf_count, graph6 in SURVIVOR_SHELLS.items():
        graph = nx.from_graph6_bytes(graph6)
        expected = nx.disjoint_union(
            nx.complete_bipartite_graph(2, leaf_count),
            nx.empty_graph(7 - leaf_count),
        )
        if not nx.is_isomorphic(graph, expected):
            raise AssertionError(
                f"shell {graph6.decode('ascii')} is not K_{{2,{leaf_count}}}"
            )


def verify_forced_equality() -> None:
    """Check the integer step forcing hub size 6 and leaf size 2."""
    for leaf_count in SURVIVOR_SHELLS:
        budget = 12 - 2 * leaf_count
        possible = []
        for hub_excess in range(budget + 1):
            for leaf_excess in range(budget + 1 - hub_excess):
                for isolate_mass in range(
                    budget + 1 - hub_excess - leaf_excess
                ):
                    if (
                        leaf_count * hub_excess + 2 * leaf_excess
                        >= 2 * leaf_count * (6 - leaf_count)
                    ):
                        possible.append(
                            (hub_excess, leaf_excess, isolate_mass)
                        )
        expected = (12 - 2 * leaf_count, 0, 0)
        if possible != [expected]:
            raise AssertionError(
                f"unexpected equality states for k={leaf_count}: {possible}"
            )


def minimum_covers(graph: nx.Graph) -> tuple[int, ...]:
    adjacency = adjacency_masks(graph)
    covers = []
    for vertices in itertools.combinations(range(CORE_ORDER), 8):
        independent_mask = sum(1 << vertex for vertex in vertices)
        if independent(independent_mask, adjacency):
            covers.append(FULL_MASK ^ independent_mask)
    if not covers:
        raise AssertionError("valid core has no independent eight-set")
    return tuple(covers)


def hub_options(covers: tuple[int, ...]) -> dict[int, frozenset[int]]:
    result: dict[int, set[int]] = {}
    for cover in covers:
        vertices = [
            vertex for vertex in range(CORE_ORDER) if cover >> vertex & 1
        ]
        for pair in itertools.combinations(vertices, 2):
            leaf = (1 << pair[0]) | (1 << pair[1])
            hub = cover ^ leaf
            result.setdefault(hub, set()).add(leaf)
    return {hub: frozenset(leaves) for hub, leaves in result.items()}


def demand_after_hubs(
    graph: nx.Graph, first_hub: int, second_hub: int
) -> tuple[int, ...]:
    return tuple(
        max(
            0,
            graph.degree(vertex)
            - 6
            - ((first_hub >> vertex) & 1)
            - ((second_hub >> vertex) & 1),
        )
        for vertex in range(CORE_ORDER)
    )


def apply_leaf(demand: tuple[int, ...], leaf: int) -> tuple[int, ...]:
    return tuple(
        max(0, value - ((leaf >> vertex) & 1))
        for vertex, value in enumerate(demand)
    )


def feasible_configuration(
    graph: nx.Graph, leaf_count: int
) -> tuple[int, int, tuple[int, ...]] | None:
    """Return a feasible reduced configuration, if one exists."""
    covers = minimum_covers(graph)
    options = hub_options(covers)
    zero = (0,) * CORE_ORDER
    for first_hub, first_leaves in options.items():
        for second_hub, second_leaves in options.items():
            common_leaves = tuple(sorted(first_leaves & second_leaves))
            if not common_leaves:
                continue
            states = {demand_after_hubs(graph, first_hub, second_hub)}
            for _ in range(leaf_count):
                states = {
                    apply_leaf(state, leaf)
                    for state in states
                    for leaf in common_leaves
                }
            if zero in states:
                return first_hub, second_hub, common_leaves
    return None


def verify_support_obstruction(graph: nx.Graph) -> int:
    """Check that every possible leaf support misses a demanded column."""
    covers = minimum_covers(graph)
    options = hub_options(covers)
    pairs_checked = 0
    for first_hub, first_leaves in options.items():
        for second_hub, second_leaves in options.items():
            common_leaves = first_leaves & second_leaves
            if not common_leaves:
                continue
            pairs_checked += 1
            maximum_support = first_hub | second_hub
            for leaf in common_leaves:
                maximum_support |= leaf
            missing_demanded = any(
                not (maximum_support >> vertex & 1)
                and graph.degree(vertex) >= 7
                for vertex in range(CORE_ORDER)
            )
            if not missing_demanded:
                raise AssertionError(
                    "hub pair has no support obstruction: "
                    f"first={first_hub} second={second_hub}"
                )
    return pairs_checked


def verify_exception_semantics(
    graph: nx.Graph, covers: tuple[int, ...]
) -> str:
    """Classify and check one of the seven nongeneric cores."""
    if len(covers) == 1:
        outside = FULL_MASK ^ covers[0]
        if any(
            graph.degree(vertex) != 7
            for vertex in range(CORE_ORDER)
            if outside >> vertex & 1
        ):
            raise AssertionError("unique-cover exception has wrong degrees")
        return "unique_cover"

    if len(covers) == 2:
        if (covers[0] & covers[1]).bit_count() != 7:
            raise AssertionError("two-cover exception has wrong intersection")
        outside = FULL_MASK ^ (covers[0] | covers[1])
        if outside.bit_count() != 7 or any(
            graph.degree(vertex) != 7
            for vertex in range(CORE_ORDER)
            if outside >> vertex & 1
        ):
            raise AssertionError("two-cover exception has wrong outside set")
        return "seven_intersection"

    if len(covers) == 3:
        for first_index, second_index in itertools.permutations(range(3), 2):
            first = covers[first_index]
            second = covers[second_index]
            if first & second:
                continue
            third = covers[3 - first_index - second_index]
            removed = first & ~third
            added = third & ~first
            if removed.bit_count() != 1 or added.bit_count() != 1:
                continue
            removed_vertex = removed.bit_length() - 1
            added_vertex = added.bit_length() - 1
            first_rest = first ^ removed
            second_rest = second ^ added
            degree_pattern = (
                graph.degree(removed_vertex),
                graph.degree(added_vertex),
                {
                    graph.degree(vertex)
                    for vertex in range(CORE_ORDER)
                    if first_rest >> vertex & 1
                },
                {
                    graph.degree(vertex)
                    for vertex in range(CORE_ORDER)
                    if second_rest >> vertex & 1
                },
            )
            if degree_pattern == (1, 8, {8}, {7}):
                return "seven_edge_star"
        raise AssertionError("three-cover exception has wrong star structure")

    raise AssertionError(f"unexpected exception cover count: {len(covers)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    args = parser.parse_args()

    verify_shell_shapes()
    verify_forced_equality()
    cores = generate_cores(args.geng)
    if len(cores) != 120:
        raise AssertionError(f"expected 120 cores, found {len(cores)}")

    cover_profile: Counter[tuple[int, int]] = Counter()
    support_profile: Counter[tuple[int, int]] = Counter()
    exception_profile: Counter[str] = Counter()
    support_pairs_checked = 0
    generic_bipartite = 0
    exceptions: list[str] = []
    for line, graph in cores:
        covers = minimum_covers(graph)
        options = hub_options(covers)
        cover_profile[(len(covers), len(options))] += 1
        pair_count = verify_support_obstruction(graph)
        support_profile[(len(covers), pair_count)] += 1
        support_pairs_checked += pair_count
        if (
            len(covers) == 2
            and covers[0] & covers[1] == 0
            and nx.is_bipartite(graph)
        ):
            generic_bipartite += 1
        else:
            exceptions.append(line.decode("ascii"))
            exception_profile[verify_exception_semantics(graph, covers)] += 1
        for leaf_count in SURVIVOR_SHELLS:
            witness = feasible_configuration(graph, leaf_count)
            if witness is not None:
                raise AssertionError(
                    f"feasible k={leaf_count} core={line.decode('ascii')} "
                    f"witness={witness}"
                )

    print(f"cores_verified={len(cores)}")
    print(f"generic_bipartite_cores={generic_bipartite}")
    print(f"exceptional_cores={len(exceptions)}")
    print(f"cover_profile={dict(sorted(cover_profile.items()))}")
    print(f"support_profile={dict(sorted(support_profile.items()))}")
    print(f"support_pairs_checked={support_pairs_checked}")
    print(f"exception_profile={dict(sorted(exception_profile.items()))}")
    print(f"exception_graph6={exceptions}")
    for leaf_count in SURVIVOR_SHELLS:
        print(f"k={leaf_count} feasible=0 excluded={len(cores)}")
    print("status=PASS")


if __name__ == "__main__":
    main()
