#!/usr/bin/env python3
"""Classify the eight-vertex shells in the order-26 degree-eight branch."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import math
from pathlib import Path
import subprocess
from typing import Iterator

import networkx as nx  # type: ignore[import-untyped]


SHELL_ORDER = 8
OFFSETS = (12, 13)
EXPECTED_GRAPHS = 4355
EXPECTED_EDGE_PROFILE: Counter[int] = Counter(
    {
        1: 1,
        2: 2,
        3: 5,
        4: 11,
        5: 24,
        6: 55,
        7: 113,
        8: 214,
        9: 381,
        10: 606,
        11: 849,
        12: 1033,
        13: 1061,
    }
)
EXPECTED_CATALOG_SHA256 = (
    "067d049a8474ad85a7ecc2780530ca00180ebc7765d0e5a5f943a0dc5fa56e45"
)
EXPECTED_RAW_STATES = {12: 1095993, 13: 2378044}
EXPECTED_FEASIBLE_STATES = {12: 5986, 13: 15221}
EXPECTED_CLASSIFICATION_SHA256 = {
    12: "16cf23274b905f0d6ec6595efd70999671ec41afd850d06ecc16e4d8a3bea3cc",
    13: "ae4e194a43f9d66f278e7b5fc6d4bd3bce0d1cef81d17f9a85ecf1fea379048f",
}
EXPECTED_FRONTIER_SHA256 = {
    12: "2c19b1abb5225632aa57f143f030122481129abab245c9e1d9b301a47f88cfa4",
    13: "b3f6c8093c887aa5d9ed6d64b04b3a4afb6ceb647ecce92cb72ea23f6f5c3f59",
}
EXPECTED_SURVIVOR_PROFILE = {
    12: Counter(
        {
            ("G???C?", 2805): 1,
            ("G???E?", 660): 1,
            ("G???F?", 532): 1,
            ("G???F_", 503): 1,
            ("G???Fo", 496): 1,
            ("G???Fw", 495): 1,
            ("G???F{", 495): 1,
        }
    ),
    13: Counter(
        {
            ("G???C?", 6831): 1,
            ("G???E?", 1782): 1,
            ("G???F?", 1415): 1,
            ("G???F_", 1323): 1,
            ("G???Fo", 1295): 1,
            ("G???Fw", 1288): 1,
            ("G???F{", 1287): 1,
        }
    ),
}


def weak_compositions_at_most(
    budget: int,
    length: int,
    prefix: tuple[int, ...] = (),
) -> Iterator[tuple[int, ...]]:
    if length == 0:
        yield prefix
        return
    for value in range(budget + 1):
        yield from weak_compositions_at_most(
            budget - value,
            length - 1,
            prefix + (value,),
        )


def triangles(graph: nx.Graph) -> tuple[tuple[int, int, int], ...]:
    return tuple(
        triple
        for triple in itertools.combinations(range(SHELL_ORDER), 3)
        if all(
            graph.has_edge(first, second)
            for first, second in itertools.combinations(triple, 2)
        )
    )


def feasible_rows(
    graph: nx.Graph,
    compositions: tuple[tuple[int, ...], ...],
) -> tuple[tuple[int, ...], ...]:
    degrees = tuple(int(graph.degree(vertex)) for vertex in range(SHELL_ORDER))
    edges = tuple((int(first), int(second)) for first, second in graph.edges)
    shell_triangles = triangles(graph)
    result = []
    for epsilon in compositions:
        rows = tuple(
            degrees[vertex] + epsilon[vertex]
            for vertex in range(SHELL_ORDER)
        )
        if any(rows[first] + rows[second] < 9 for first, second in edges):
            continue
        if any(sum(rows[vertex] for vertex in triple) < 17 for triple in shell_triangles):
            continue
        result.append(rows)
    return tuple(result)


def is_star_plus_isolates(graph: nx.Graph) -> bool:
    edge_count = graph.number_of_edges()
    degrees = sorted(int(degree) for _, degree in graph.degree())
    return degrees == [0] * (SHELL_ORDER - edge_count - 1) + [1] * edge_count + [
        edge_count
    ]


def catalog_sha256(lines: tuple[bytes, ...]) -> str:
    return hashlib.sha256(b"\n".join(lines) + b"\n").hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", type=Path, required=True)
    parser.add_argument("--allow-unpinned", action="store_true")
    args = parser.parse_args()

    lines = tuple(
        sorted(
            subprocess.check_output(
                [str(args.geng), "-q", "-k", str(SHELL_ORDER), "1:13"]
            ).splitlines()
        )
    )
    graphs = tuple(nx.from_graph6_bytes(line) for line in lines)
    if len(graphs) != EXPECTED_GRAPHS:
        raise AssertionError(f"wrong graph count: {len(graphs)}")
    edge_profile = Counter(graph.number_of_edges() for graph in graphs)
    if edge_profile != EXPECTED_EDGE_PROFILE:
        raise AssertionError(f"wrong edge profile: {edge_profile}")
    catalog_digest = catalog_sha256(lines)

    composition_cache = {
        budget: tuple(weak_compositions_at_most(budget, SHELL_ORDER))
        for budget in range(max(OFFSETS))
    }
    for budget, compositions in composition_cache.items():
        expected_count = math.comb(budget + SHELL_ORDER, SHELL_ORDER)
        if (
            len(compositions) != expected_count
            or len(set(compositions)) != expected_count
        ):
            raise AssertionError(f"weak-composition mismatch at budget {budget}")

    raw_totals: dict[int, int] = {}
    feasible_totals: dict[int, int] = {}
    classification_digests: dict[int, str] = {}
    frontier_digests: dict[int, str] = {}
    survivor_profiles: dict[int, Counter[tuple[str, int]]] = {}
    survivor_names: dict[int, tuple[str, ...]] = {}
    for offset in OFFSETS:
        raw_total = 0
        feasible_total = 0
        classification_rows = []
        frontier_rows = []
        survivor_profile: Counter[tuple[str, int]] = Counter()
        names = []
        for line, graph in zip(lines, graphs, strict=True):
            edge_count = graph.number_of_edges()
            budget = offset - edge_count
            compositions = composition_cache[budget] if budget >= 0 else ()
            feasible = feasible_rows(graph, compositions)
            raw_total += len(compositions)
            feasible_total += len(feasible)
            name = line.decode("ascii")
            classification_rows.append(
                f"{name}:{edge_count}:{len(compositions)}:{len(feasible)}\n"
            )
            for rows in feasible:
                frontier_rows.append(f"{name}:{','.join(map(str, rows))}\n")
            if feasible:
                if not is_star_plus_isolates(graph):
                    raise AssertionError(f"nonstar shell survived: {name}")
                names.append(name)
                survivor_profile[(name, len(feasible))] += 1
        if len(names) != 7:
            raise AssertionError(f"wrong survivor count at offset {offset}: {names}")
        raw_totals[offset] = raw_total
        feasible_totals[offset] = feasible_total
        classification_digests[offset] = hashlib.sha256(
            "".join(classification_rows).encode("ascii")
        ).hexdigest()
        frontier_digests[offset] = hashlib.sha256(
            "".join(frontier_rows).encode("ascii")
        ).hexdigest()
        survivor_profiles[offset] = survivor_profile
        survivor_names[offset] = tuple(names)

    if not args.allow_unpinned:
        expected_receipt = (
            EXPECTED_CATALOG_SHA256,
            EXPECTED_RAW_STATES,
            EXPECTED_FEASIBLE_STATES,
            EXPECTED_CLASSIFICATION_SHA256,
            EXPECTED_FRONTIER_SHA256,
            EXPECTED_SURVIVOR_PROFILE,
        )
        actual = (
            catalog_digest,
            raw_totals,
            feasible_totals,
            classification_digests,
            frontier_digests,
            survivor_profiles,
        )
        if actual != expected_receipt:
            raise AssertionError(f"unpinned shell-classification receipt: {actual}")

    print(f"graphs={len(graphs)} edge_profile={dict(sorted(edge_profile.items()))}")
    print(f"catalog_sha256={catalog_digest}")
    for offset in OFFSETS:
        print(
            f"offset={offset} raw_states={raw_totals[offset]} "
            f"feasible_states={feasible_totals[offset]} "
            f"survivors={survivor_names[offset]}"
        )
        print(
            f"offset={offset} survivor_profile="
            f"{dict(sorted(survivor_profiles[offset].items()))}"
        )
        print(
            f"offset={offset} classification_sha256="
            f"{classification_digests[offset]}"
        )
        print(f"offset={offset} frontier_sha256={frontier_digests[offset]}")
    print("status=PASS")


if __name__ == "__main__":
    main()
