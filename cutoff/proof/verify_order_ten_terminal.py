"""Replay the 28-vertex coloring and the finite root counts in order-ten-terminal.md."""

from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, product
from math import comb


def coloring():
    """Target is 9. Points 0..8 are columns, 9..16 are A_1..A_8,
    17..25 are B_0..B_8, and 26,27 are the split symbols."""
    edges = [[9] * 28 for _ in range(28)]
    blocks = [[] for _ in range(9)]
    seen = [set() for _ in range(9)]

    def assign(u, v, hue):
        if u == v or edges[u][v] != 9:
            raise ValueError("A nontarget edge was assigned twice.")
        edges[u][v] = edges[v][u] = hue

    for hue in range(9):
        for column in range(9):
            i, j = (hue + column) % 9, (hue + 2 * column) % 9
            if i:
                pair = (8 + i, 17 + j)
            elif j:
                pair = (26 if j <= 4 else 27, 17 + j)
            else:
                pair = (26, 27)
            block = (column, *pair)
            blocks[hue].append(block)
            seen[column].update(pair)
            for u, v in combinations(block, 2):
                assign(u, v, hue)
    for column, points in enumerate(seen):
        (missing,) = set(range(9, 28)) - points
        assign(column, missing, 0)
    return edges, blocks


def adjacency(edges, test):
    return [
        sum(1 << j for j, color in enumerate(row) if i != j and test(color))
        for i, row in enumerate(edges)
    ]


def clique_size(adj):
    @cache
    def best(mask):
        if mask == 0:
            return 0
        bit = mask & -mask
        rest = mask ^ bit
        return max(best(rest), 1 + best(rest & adj[bit.bit_length() - 1]))

    return best((1 << len(adj)) - 1)


def count_balanced_eleven_sets(edges):
    # When a chosen subset already contains all colors, count all its completions.
    # Alternating columns and symbols brings different colors into the prefix early.
    order = []
    for t in range(9):
        order.append(t)
        if t < 8:
            order.append(9 + t)
        order.append(17 + t)
    order.extend((26, 27))
    assert sorted(order) == list(range(28))
    masks = [[1 << edges[u][v] for v in order] for u in order]

    def visit(start, needed, mask, chosen):
        if mask == (1 << 10) - 1:
            return comb(28 - start, needed)
        if needed == 0:
            raise ValueError(f"Eleven-set omits a color: {[order[i] for i in chosen]}")
        result = 0
        for v in range(start, 29 - needed):
            updated = mask
            for u in chosen:
                updated |= masks[v][u]
            chosen.append(v)
            result += visit(v + 1, needed - 1, updated, chosen)
            chosen.pop()
        return result

    return visit(0, 11, 0, [])


def check_coloring():
    edges, blocks = coloring()
    for hue, partition in enumerate(blocks):
        if len({v for block in partition for v in block}) != 27:
            raise ValueError("Factor triangles overlap.")
        for block in partition:
            if any(edges[u][v] != hue for u, v in combinations(block, 2)):
                raise ValueError("A factor triangle has the wrong color.")
    counts = Counter(edges[u][v] for u, v in combinations(range(28), 2))
    assert counts == {0: 36, **dict.fromkeys(range(1, 9), 27), 9: 126}
    independence = [
        clique_size(adjacency(edges, lambda c: c != hue)) for hue in range(10)
    ]
    target_clique = clique_size(adjacency(edges, lambda c: c == 9))
    assert independence == [10] * 9 + [3] and target_clique == 9
    print(
        "28 vertices: target edges 126, target independence 3, largest target clique 9."
    )
    total = count_balanced_eleven_sets(edges)
    assert total == comb(28, 11)
    print(
        f"All nine other independence numbers are 10. All {total:,} eleven-sets see every color."
    )


def root_shapes(k):
    shapes = []
    for b in combinations_with_replacement(range(k + 3), 3):
        exterior = 2 + sum(b)
        for weights in product(range(k + 1), repeat=3):
            if sum(weights) != k:
                continue
            if any(b[i] == b[i + 1] and weights[i] > weights[i + 1] for i in (0, 1)):
                continue
            incidences = [2 + deficit + weight for deficit, weight in zip(b, weights)]
            if (
                max(incidences) <= exterior
                and 2 * exterior <= sum(incidences) <= 3 * exterior
            ):
                shapes.append((b, weights))
    return shapes


def check_terminal_bounds():
    for h in (9, 10):
        cross_cap = 152 - 81 - (55 - h)
        assert 36 - cross_cap >= 10
    shapes = [root_shapes(k) for k in (0, 1)]
    assert [len(s) for s in shapes] == [4, 9]
    for target in range(147, 153):
        excess = 2 * (target - 145)
        assert (154 - target) < 9 and excess // 9 <= 1
        # If every independent triple has positive excess, its zero set has at most 18
        # points, so at least eleven vertices contribute to this even excess.
        assert (excess >= 11) == (target in (151, 152))
    print(
        "29 vertices, minimum target degree ten: four zero-weight root shapes and nine of weight one."
    )


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError(
            "Run without -O so that verification assertions are enabled."
        )
    check_coloring()
    check_terminal_bounds()
