"""Budget-first replay of the twelve-color proof, independent of verify_order_twelve.py."""

from functools import cache
from itertools import product
from math import comb


@cache
def capacity(deficit, root_weight, partners):
    """Maximum assigned ordinary vertices at each possible row-plus-exterior budget."""
    size = 11 - deficit
    slots = 3 + deficit + root_weight
    best = [-100] * 24
    for inside in range(root_weight * size, 24):
        costs = []
        for missed in range(4):
            price = 24
            for q in range(24 - inside):
                if missed == 0 and deficit == 0:
                    continue
                other = any(
                    missed <= t and missed + t < 12 and missed * t <= deficit * c + missed + t
                    and not (c == 0 and t == 0) and size - missed + 11 - c - t <= 13 + q
                    for c in partners for t in range(11 - c)
                )
                extra = max(0, size - missed - 2 - q - root_weight)
                if other and missed * extra <= inside - size * root_weight:
                    price = q
                    break
            costs.append(price)

        # Choose how many vertices have zero, one, two and three misses.
        def place(p, used, missing_edges, spent):
            if p == 4:
                best[spent] = max(best[spent], used)
                return
            place(p + 1, used, missing_edges, spent)
            for number in range(1, slots - used + 1):
                total = used + number
                holes = missing_edges + number * p
                if holes + comb(total, 2) < 11 * (total - deficit - 1):
                    break  # This forbidden prefix occurs in every extension.
                price = spent + number * costs[p]
                if p == 0:
                    price += max(0, number - deficit) * ((size - 1) // 2)
                if price > 23:
                    break
                place(p + 1, total, holes, price)

        place(0, 0, 0, inside)
    for budget in range(1, 24):
        best[budget] = max(best[budget], best[budget - 1])
    return tuple(best)


def check_labelled_rows():
    seen = set()
    exceptions = []
    count = 0
    for k in range(3):
        roots = (1,) * k + (0,) * (5 - k)
        for deficits in product(range(4 + k), repeat=5):
            if sum(deficits) > 3 + k or sum((11 - b) * a for b, a in zip(deficits, roots)) > 23:
                continue
            count += 1
            seen.add(tuple(sorted(zip(deficits, roots))))
            # Split the total budget of 23 between the five disjoint row charges.
            packed = [0] * 24
            for i, (b, a) in enumerate(zip(deficits, roots)):
                partners = tuple(sorted(set(deficits[:i] + deficits[i + 1:])))
                local = capacity(b, a, partners)
                packed = [max(packed[j] + local[t - j] for j in range(t + 1)) for t in range(24)]
            if packed[23] >= 3 + 2 * sum(deficits) - k:
                exceptions.append((k, deficits, packed[23]))
    assert len(seen) == 91 and exceptions == [(0, (0,) * 5, 3)]
    print(f"{count} labelled choices cover 91 profiles. Only five long rows could host enough points.")


def check_small_sets():
    for s, excess in ((4, 0), (5, 6)):
        for b_total in range(3):
            trim = 0 if s == 4 else (2 if b_total else 3)
            removed = excess // (trim + 1)
            assert 11 - b_total - removed > 2 + 2 * trim
            assert s - 3 + 2 * b_total > b_total + removed
            for b in range(b_total + 1):
                for c in range(b_total - b + 1):
                    for p, t in product(range(11 - b), range(11 - c)):
                        if p * t > 11 + b * c or p * t > b * c + p + t:
                            continue
                        assert max(11 - b - p, 11 - c - t) > 2 + 2 * trim
    print("The row and pair inequalities exclude the 47- and 59-vertex cases at their old budgets.")


ORDER_LIMITS = (0, 11, 23, 35, 48)
FLOORS = {(4, 48): 312, (4, 47): 283, (5, 59): 358, (5, 61): 409}


@cache
def fits(s, n, budget):
    if budget < 0 or (s < len(ORDER_LIMITS) and n > ORDER_LIMITS[s]):
        return False
    if not n:
        return True
    if s == 1:
        return comb(n, 2) <= budget
    if budget < FLOORS.get((s, n), 0):
        return False
    for degree in range(min(n - 1, 2 * budget // n) + 1):
        remaining = n - degree - 1
        hit = max(0, remaining - ORDER_LIMITS[s - 2]) if s - 2 < len(ORDER_LIMITS) else 0
        premium = 11 * max(0, degree - 11)
        if degree == 11:
            premium = max(1, hit - 1)
        if degree == 12:
            premium = max(11, 2 * hit - 6)
        if fits(s - 1, remaining, budget - degree * (degree + 1) // 2 - premium):
            return True
    return False


def check_ladder():
    for s in range(1, 12):
        cap = 66 * s + 78
        n = 12 * s + 1
        assert not fits(s, n, cap)
        if s >= 5:
            floor = (409, 475, 541, 608, 675, 742, 809)[s - 5]
            assert not fits(s, n, floor - 1) and fits(s, n, floor)
    print("The budget-first recursion reproduces every outer exclusion and all seven finite floors.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O for an exact replay.")
    check_labelled_rows()
    check_small_sets()
    check_ladder()
