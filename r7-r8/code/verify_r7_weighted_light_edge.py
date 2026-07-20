#!/usr/bin/env python3
"""Exhaustive check of the weighted seven-vertex light-edge lemma."""

from __future__ import annotations

import itertools
from math import comb

VERTICES = tuple(range(7))
EDGES = tuple(itertools.combinations(VERTICES, 2))

EXPECTED_GRAPH_COUNTS = {
    6: 54_257,
    7: 116_280,
    8: 203_490,
    9: 293_930,
}

EXPECTED_MAXIMA = {
    (6, 0): 6,
    (6, 1): 6,
    (6, 2): 6,
    (6, 3): 7,
    (7, 0): 6,
    (7, 1): 6,
    (7, 2): 7,
    (8, 0): 6,
    (8, 1): 6,
    (9, 0): 7,
}


def weak_compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for suffix in weak_compositions(total - first, parts - 1):
            yield (first,) + suffix


def main() -> None:
    maxima = {key: -1 for key in EXPECTED_MAXIMA}
    graph_counts: dict[int, int] = {}
    weighted_cases = 0

    for edge_count in range(6, 10):
        valid_graphs = 0
        weights_by_total = {
            total: tuple(weak_compositions(total, 7))
            for total in range(10 - edge_count)
        }

        for edge_indices in itertools.combinations(range(len(EDGES)), edge_count):
            degrees = [0] * 7
            graph_edges = []
            for edge_index in edge_indices:
                left, right = EDGES[edge_index]
                graph_edges.append((left, right))
                degrees[left] += 1
                degrees[right] += 1

            # On seven vertices, an independent six-set exists exactly when
            # one vertex meets every edge.
            if max(degrees) == edge_count:
                continue

            valid_graphs += 1
            for total, weight_vectors in weights_by_total.items():
                for weights in weight_vectors:
                    weighted_cases += 1
                    lightest = min(
                        degrees[left]
                        + degrees[right]
                        + weights[left]
                        + weights[right]
                        for left, right in graph_edges
                    )
                    maxima[(edge_count, total)] = max(
                        maxima[(edge_count, total)],
                        lightest,
                    )

        graph_counts[edge_count] = valid_graphs

    assert graph_counts == EXPECTED_GRAPH_COUNTS
    assert maxima == EXPECTED_MAXIMA

    expected_weighted_cases = sum(
        EXPECTED_GRAPH_COUNTS[edge_count]
        * sum(comb(total + 6, 6) for total in range(10 - edge_count))
        for edge_count in range(6, 10)
    )
    assert weighted_cases == expected_weighted_cases == 12_618_770

    print("r7_weighted_graph_counts", graph_counts)
    print("r7_weighted_maxima", maxima)
    print(f"r7_weighted_cases={weighted_cases}")
    print("r7_weighted_light_edge=VERIFIED")


if __name__ == "__main__":
    main()
