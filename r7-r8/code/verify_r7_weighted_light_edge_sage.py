#!/usr/bin/env sage
"""Independent nauty reconstruction of the fixed-r=7 weighted lemma."""

from collections import Counter
from math import comb, factorial

from sage.all import graphs


EXPECTED_UNLABELED_COUNTS = {
    6: 40,
    7: 65,
    8: 97,
    9: 131,
}

EXPECTED_LABELED_COUNTS = {
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
    """Yield all ordered nonnegative integer vectors with the given sum."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for suffix in weak_compositions(total - first, parts - 1):
            yield (first,) + suffix


def main() -> None:
    unlabeled_counts: Counter[int] = Counter()
    labeled_counts: Counter[int] = Counter()
    maxima = {key: -1 for key in EXPECTED_MAXIMA}

    for graph in graphs.nauty_geng("7 6:9"):
        edge_count = int(graph.size())

        # This is a separate semantic test for alpha(M) <= 5.
        if int(graph.complement().clique_number()) > 5:
            continue

        unlabeled_counts[edge_count] += 1
        automorphism_order = int(graph.automorphism_group().order())
        labeled_counts[edge_count] += factorial(7) // automorphism_order

        vertices = tuple(sorted(int(vertex) for vertex in graph.vertices()))
        edges = tuple(
            (int(left), int(right))
            for left, right in graph.edges(labels=False)
        )
        degrees = {
            vertex: sum(vertex in edge for edge in edges)
            for vertex in vertices
        }

        for total in range(10 - edge_count):
            for weights in weak_compositions(total, 7):
                lightest = min(
                    degrees[left]
                    + degrees[right]
                    + weights[left]
                    + weights[right]
                    for left, right in edges
                )
                key = (edge_count, total)
                maxima[key] = max(maxima[key], lightest)

    assert dict(unlabeled_counts) == EXPECTED_UNLABELED_COUNTS
    assert dict(labeled_counts) == EXPECTED_LABELED_COUNTS
    assert maxima == EXPECTED_MAXIMA

    weighted_cases = sum(
        EXPECTED_LABELED_COUNTS[edge_count]
        * sum(comb(total + 6, 6) for total in range(10 - edge_count))
        for edge_count in range(6, 10)
    )
    assert weighted_cases == 12_618_770

    print("r7_sage_unlabeled_graph_counts", dict(unlabeled_counts))
    print("r7_sage_labeled_graph_counts", dict(labeled_counts))
    print("r7_sage_weighted_maxima", maxima)
    print(f"r7_sage_weighted_cases={weighted_cases}")
    print("r7_weighted_light_edge_independent=VERIFIED")


if __name__ == "__main__":
    main()
