"""Integer replay of order-twelve.md. Run with Python 3.10 or newer."""

from collections import defaultdict
from functools import cache
from itertools import combinations_with_replacement, product
from math import comb, inf


BUDGET = 23
ORDER = {0: 0, 1: 11, 2: 23, 3: 35, 4: 48}


def possible_rows():
    for rows in combinations_with_replacement(product(range(6), (0, 1)), 5):
        k = sum(a for b, a in rows)
        deficit = sum(b for b, a in rows)
        if k <= 2 and deficit <= 3 + k and sum((11 - b) * a for b, a in rows) <= BUDGET:
            yield rows


@cache
def row_costs(b, a, other_deficits):
    """Least permitted row and exterior excess for each number assigned here."""
    size = 11 - b
    incident = 3 + b + a
    degree_cost = {}
    if b:
        degree_cost[0] = 0
    for p in (1, 2, 3):
        outside = [size + (11 - c) - p - t - 13
                   for c in other_deficits for t in range(p, 11 - c)
                   if p + t <= 11 and p * t <= b * c + p + t]
        if outside:
            degree_cost[p] = max(0, min(outside))

    groups = []
    for count in range(incident + 1):
        for misses in combinations_with_replacement(sorted(degree_cost), count):
            if all(sum(misses[:z]) + comb(z, 2) >= 11 * (z - b - 1)
                   for z in range(b + 2, count + 1)):
                groups.append(misses)

    best = [inf] * (incident + 1)
    baseline = size * a
    for inside in range(baseline, BUDGET + 1):
        prices = degree_cost.copy()
        for p in prices:
            if p:
                prices[p] = max(prices[p], size - p - 2 - a - (inside - baseline) // p)
        for group in groups:
            full = group.count(0)
            full_cost = max(0, full - b) * ((size - 1) // 2)
            cost = inside + full_cost + sum(prices[p] for p in group)
            best[len(group)] = min(best[len(group)], cost)
    return best


def ordinary_excess(rows):
    needed = 3 + 2 * sum(b for b, a in rows) - sum(a for b, a in rows)
    # dp[j] is the least charge for hosting at least j ordinary vertices.
    dp = [0] + [inf] * needed
    for i, (b, a) in enumerate(rows):
        other_deficits = tuple(sorted({c for j, (c, _) in enumerate(rows) if j != i}))
        costs = row_costs(b, a, other_deficits)
        dp = [min(cost + dp[max(0, j - count)] for count, cost in enumerate(costs))
              for j in range(needed + 1)]
    return dp[needed]


def check_rows():
    groups = defaultdict(list)
    open_rows = []
    for rows in possible_rows():
        cost = ordinary_excess(rows)
        key = (sum(a for b, a in rows), sum(b for b, a in rows))
        groups[key].append(cost)
        if cost <= BUDGET:
            open_rows.append((rows, cost))
    assert open_rows == [(((0, 0),) * 5, 21)]
    expected = (
        ((1, 21), (1, 25), (2, 29), (3, 28)),
        ((1, 24), (2, 28), (4, 31), (7, 28), (12, 24)),
        ((1, 28), (2, 31), (5, 34), (9, 31), (16, 27), (25, 29)),
    )
    computed = tuple(tuple((len(groups[k, b]), min(groups[k, b])) for b in range(4 + k))
                     for k in range(3))
    assert computed == expected
    assert sum(map(len, groups.values())) == 91
    # In the exceptional profile the host misses one or two points. Each
    # ordinary vertex and those points carry at least seven units together.
    for p in (1, 2):
        assert min(q + p * max(0, 11 - p - 2 - q) for q in range(24)) >= 7
    assert 4 * 7 > 23 and 23 - 3 * 7 == 2
    assert 3 * 11 < 7 * 7 and 2 * 4 + 1 < 11
    print("All 91 root profiles accounted for, including the six-vertex collision.")


def deletion_cost(s, n, d):
    residual = n - 1 - d
    hitting = max(0, residual - ORDER.get(s - 2, residual))
    extra = 0
    if d == 11:
        extra = max(1, hitting - 1)
    elif d == 12:
        extra = max(11, 2 * hitting - 6)
    elif d >= 13:
        extra = 11 * (d - 11)
    return comb(d + 1, 2) + extra


def deletion_table(floors):
    table = {}
    for s in range(1, 12):
        for n in range(134):
            if n > ORDER.get(s, n):
                table[s, n] = inf
            elif not n or s == 1:
                table[s, n] = comb(n, 2)
            else:
                alternatives = (max((n * d + 1) // 2, table[s - 1, n - 1 - d] + deletion_cost(s, n, d))
                                for d in range(n))
                table[s, n] = max(floors.get((s, n), 0), min(alternatives))
    return table


def compatible_degrees(table, s, n, cap):
    return [d for d in range(n) if n * d <= 2 * cap
            and table[s - 1, n - 1 - d] + deletion_cost(s, n, d) <= cap]


def check_stops():
    inputs = {(4, 48): 312}
    base = deletion_table(inputs)
    assert base[3, 35] == 208
    assert compatible_degrees(base, 4, 47, 282) == [12]
    assert compatible_degrees(base, 5, 61, 408) == [13]
    with_47 = deletion_table({**inputs, (4, 47): 283})
    assert compatible_degrees(with_47, 5, 59, 357) == [12]
    only_61 = deletion_table({**inputs, (5, 61): 409})
    assert [only_61[s, 12 * s + 1] for s in (6, 7, 8)] == [474, 539, 606]
    final = deletion_table({**inputs, (4, 47): 283, (5, 59): 358, (5, 61): 409})
    expected = [inf] * 4 + [409, 475, 541, 608, 675, 742, 809]
    for s, floor in enumerate(expected, 1):
        n = 12 * s + 1
        cap = 870 - 66 * (12 - s)
        assert final[s, n] == floor and floor > cap
        for t in range(12):
            raw = 870 - comb(12 - t, 2) - (11 - s) * 66
            assert raw * comb(n, 2) <= cap * comb(n + t, 2)
        if s >= 5:
            print(f"{n} vertices: floor {floor}, cap {cap}.")
    print("All eleven stops and all 132 sampling comparisons pass.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O for an exact replay.")
    check_rows()
    check_stops()
