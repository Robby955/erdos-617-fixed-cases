"""Exact replay of midpoint-row-excess.md. Run with Python 3.10 or later."""

from functools import cache
from itertools import combinations, combinations_with_replacement
from math import comb


def width_test(r, deficit, cutoff, common):
    """Sufficient uniform threshold for the private rows of an odd midpoint."""
    discarded = (r - 1) // (cutoff + 1)
    remaining = r - 1 - common - 2 * cutoff
    return (
        discarded <= deficit + 2
        and r - 1 - deficit - discarded > common + 2 * cutoff
        and remaining > deficit
        and remaining * (remaining - deficit) > r - 1
    )


def check_uniform_range():
    for common, start in ((3, 31), (2, 27)):
        for r in range(start, 101, 2):
            for deficit in range((r - 1) // 2 - 1):
                assert any(width_test(r, deficit, t, common) for t in range(r))


def row_budgets(deficits, remaining=10, partial=()):
    if len(partial) == len(deficits):
        yield partial
        return
    i = len(partial)
    start = partial[-1] if i and deficits[i] == deficits[i - 1] else 0
    for q in range(start, remaining + 1):
        yield from row_budgets(deficits, remaining - q, partial + (q,))


@cache
def ordinary_options(b, c):
    """Possible misses, vertex excess and minimum excess of each missed point."""
    left, right = 10 - b, 10 - c
    options = []
    for p in range(left):
        for t in range(right):
            if (p == 0 and b == 0) or (t == 0 and c == 0):
                continue
            hits_left, hits_right = left - p, right - t
            for q in range(11):
                wl = max(0, hits_left - 2 - q, t - 2)
                wr = max(0, hits_right - 2 - q, p - 2)
                options.append((q, p, t, wl, wr))
    return sorted(options)


@cache
def unassigned_cost(b, c, dl, dr, gate):
    usable_left = 10 - b - dl // 5 > 2 + 2 * gate
    usable_right = 10 - c - dr // 5 > 2 + 2 * gate
    for q, p, t, wl, wr in ordinary_options(b, c):
        if p * wl > dl or t * wr > dr:
            continue
        takes_left = usable_left and (p == 0 or wl > 4)
        takes_right = usable_right and (t == 0 or wr > 4)
        if q > gate or not (takes_left or takes_right):
            return q
    return 11  # Every real vertex has excess at most ten.


def required_excess(b, budgets, gate):
    capacity = sum(
        loss + d // 5 for loss, d in zip(b, budgets)
        if 10 - loss - d // 5 > 2 + 2 * gate
    )
    need = max(0, 3 + 2 * sum(b) - capacity)
    prices = []
    for i, j in combinations(range(5), 2):
        price = unassigned_cost(b[i], b[j], budgets[i], budgets[j], gate)
        prices.extend((price, price))
    return sum(budgets) + sum(sorted(prices)[:need])


def check_five_rows():
    first_pass = second_pass = 0
    exceptions = {}
    for b in combinations_with_replacement(range(4), 5):
        if sum(b) > 3:
            continue
        for budgets in row_budgets(b):
            if required_excess(b, budgets, 2) > 10:
                first_pass += 1
            else:
                floor = required_excess(b, budgets, 0)
                assert floor > 10
                exceptions[b, budgets] = floor
                second_pass += 1
    assert (first_pass, second_pass) == (2900, 3)
    assert exceptions == {
        ((0, 0, 0, 0, 2), (0, 0, 0, 0, 10)): 13,
        ((0, 0, 0, 0, 3), (0, 0, 0, 5, 5)): 14,
        ((0, 0, 0, 1, 2), (0, 0, 0, 0, 10)): 14,
    }
    return first_pass, second_pass


MAX_ORDER = {0: 0, 1: 10, 2: 21, 3: 32, 4: 44}


@cache
def survives(s, n, budget):
    """Budget-first deletion replay at eleven using the two local floors."""
    if budget < 0 or n > MAX_ORDER.get(s, n):
        return False
    if (s, n) == (4, 44) and budget < 264:
        return False
    if (s, n) == (5, 56) and budget < 342:
        return False
    if n == 0:
        return True
    if s == 1:
        return comb(n, 2) <= budget
    for degree in range(min(n - 1, 2 * budget // n) + 1):
        residual = n - degree - 1
        tau = max(0, residual - MAX_ORDER.get(s - 2, residual))
        cost = comb(degree + 1, 2)
        if degree == 10:
            cost += max(1, tau - 1)
        elif degree == 11:
            cost += max(10, 2 * tau - 6)
        elif degree >= 12:
            cost += 10 * (degree - 10)
        if survives(s - 1, residual, budget - cost):
            return True
    return False


def check_outer_stops():
    floors = {5: 342, 6: 401, 7: 454, 8: 510, 9: 566, 10: 622}
    for s in range(1, 11):
        n = 11 * s + 1
        cap = 671 - (11 - s) * 55
        for t in range(11):
            remaining = 671 - comb(11 - t, 2) - (10 - s) * 55
            assert remaining * comb(n, 2) <= cap * comb(n + t, 2)
        assert not survives(s, n, cap)
        if s in floors:
            low = floors[s]
            assert not survives(s, n, low - 1) and survives(s, n, low)
            print(f"{n} vertices: lower bound {low}, cap {cap}.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O for an exact replay.")
    check_uniform_range()
    first, second = check_five_rows()
    print(f"Five rows at eleven: {first} budget profiles excluded at gate two and {second} at zero.")
    check_outer_stops()
    print("All ten stops, 110 sampling comparisons and the finite threshold ranges pass.")
