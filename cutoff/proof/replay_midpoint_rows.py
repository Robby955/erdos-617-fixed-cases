"""Labelled replay of the 56-vertex exclusion and a forward order-eleven ladder."""

from functools import cache
from itertools import combinations, combinations_with_replacement
from math import comb, inf


def distributions(n, size):
    # Stars and bars, with a final bin for all of the exterior excess.
    for dividers in combinations(range(n + size - 1), size - 1):
        endpoints = (-1, *dividers, n + size - 1)
        yield tuple(b - a - 1 for a, b in zip(endpoints, endpoints[1:]))


@cache
def minimum_cost(size_a, size_b, excess_a, excess_b, limit):
    for cost in range(11):
        for hits_a in range(1, size_a + (size_a < 10)):
            for hits_b in range(1, size_b + (size_b < 10)):
                def permitted_miss(size, hits, opposite, excess):
                    missed = size - hits
                    if missed == 0:
                        return True, True
                    bound = max(hits - 2 - cost, opposite - 2, 0)
                    return missed * bound <= excess, bound >= 5

                ok_a, sees_a = permitted_miss(size_a, hits_a, size_b - hits_b, excess_a)
                ok_b, sees_b = permitted_miss(size_b, hits_b, size_a - hits_a, excess_b)
                if not (ok_a and ok_b):
                    continue
                qualifies = (sees_a and size_a - excess_a // 5 >= 3 + 2 * limit)
                qualifies |= (sees_b and size_b - excess_b // 5 >= 3 + 2 * limit)
                if cost > limit or not qualifies:
                    return cost
    return inf


def possible(deficits, budgets, exterior, limit):
    sizes = tuple(10 - b for b in deficits)
    capacity = sum(10 - left for size, d in zip(sizes, budgets)
                   if (left := size - d // 5) >= 3 + 2 * limit)
    wanted = 3 + 2 * sum(deficits)
    if capacity >= wanted:
        return True
    # With the remaining excess, maximize the count of unassigned ordinary
    # vertices. Each root pair supports zero, one or two.
    counts = [0] * (exterior + 1)
    for i, j in combinations(range(5), 2):
        cost = minimum_cost(sizes[i], sizes[j], budgets[i], budgets[j], limit)
        if cost > exterior:
            continue
        before = counts
        counts = [max(before[b - take * cost] + take
                      for take in (0, 1, 2) if take * cost <= b)
                  for b in range(exterior + 1)]
    return capacity + counts[exterior] >= wanted


def check_labelled_rows():
    tested = rescued = 0
    for shape in combinations_with_replacement(range(4), 5):
        if sum(shape) > 3:
            continue
        for *inside, outside in distributions(10, 6):
            tested += 1
            if possible(shape, inside, outside, 2):
                rescued += 1
                assert not possible(shape, inside, outside, 0)
    assert tested == 21021
    print(f"All {tested} labelled row-budget assignments excluded. {rescued} used the second bound.")


def forward_ladder():
    order_caps = {0: 0, 1: 10, 2: 21, 3: 32, 4: 44}
    table = {(0, n): inf if n else 0 for n in range(112)}
    for s in range(1, 11):
        for n in range(112):
            if n > order_caps.get(s, n):
                table[s, n] = inf
            elif s == 1 or not n:
                table[s, n] = comb(n, 2)
            else:
                alternatives = []
                for u in range(n):
                    degree = n - u - 1
                    hitting = max(0, u - order_caps.get(s - 2, u))
                    extra = max(degree - 10, 0) * 10
                    if degree == 10:
                        extra = max(1, hitting - 1)
                    if degree == 11:
                        extra = max(extra, 2 * hitting - 6)
                    deletion = comb(degree + 1, 2) + extra + table[s - 1, u]
                    alternatives.append(max((n * degree + 1) // 2, deletion))
                table[s, n] = min(alternatives)
            if (s, n) == (4, 44):
                table[s, n] = max(table[s, n], 264)
            if (s, n) == (5, 56):
                table[s, n] = max(table[s, n], 342)
    stops = [table[s, 11*s + 1] for s in range(1, 11)]
    assert stops == [inf]*4 + [342, 401, 454, 510, 566, 622]
    assert all(low > 671 - 55 * (11 - s) for s, low in enumerate(stops, 1))
    print("Forward deletion replay excludes all ten stops.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O for an exact replay.")
    check_labelled_rows()
    forward_ladder()
