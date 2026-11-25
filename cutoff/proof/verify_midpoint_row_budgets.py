"""Finite part of the odd-midpoint theorem in midpoint-row-excess.md, Section 5."""

from collections import Counter
from functools import cache
from itertools import combinations


def partitions(total, largest):
    """Write total as a nonincreasing tuple of positive integers."""
    if total == 0:
        yield ()
        return
    for first in range(1, min(largest, total) + 1):
        for tail in partitions(total - first, first):
            yield (first,) + tail


@cache
def pair_options(r, common, b, c):
    """Relaxations for a single ordinary vertex incident to this pair of rows."""
    budget = r - 1
    left, right = budget - b, budget - c
    options = set()
    for p in range(left):
        for t in range(right):
            if (p == 0 and b == 0) or (t == 0 and c == 0):
                continue
            if p + t > budget or p * t > budget + b * c:
                continue
            hits = left + right - p - t
            for q in range(max(0, hits - (r + 1)), budget + 1):
                low_left = max(0, left - p - common - q, t - common)
                low_right = max(0, right - t - common - q, p - common)
                inside = p * low_left + t * low_right
                if inside + q <= budget:
                    options.add((q, inside, p == 0, low_left, t == 0, low_right))
    return sorted(options)


@cache
def cheapest_unassigned(r, common, b, c, inside, cutoff, gate):
    high = inside // (cutoff + 1)
    left_usable = r - 1 - b - high > common + 2 * gate
    right_usable = r - 1 - c - high > common + 2 * gate
    for q, minimum_inside, full_left, low_left, full_right, low_right in pair_options(r, common, b, c):
        if minimum_inside > inside:
            continue
        assigned_left = left_usable and (full_left or low_left > cutoff)
        assigned_right = right_usable and (full_right or low_right > cutoff)
        if q > gate or not (assigned_left or assigned_right):
            return q
    return r  # Every actual vertex has q at most r - 1.


def excludes(r, common, deficits, pairs, inside, cutoff, gate):
    high = inside // (cutoff + 1)
    capacity = high + sum(b for b in deficits if r - 1 - b - high > common + 2 * gate)
    needed = 3 + 2 * sum(deficits) - capacity
    if needed <= 0:
        return False

    costs = sorted(
        (cheapest_unassigned(r, common, b, c, inside, cutoff, gate), common * count)
        for (b, c), count in pairs.items()
    )
    total = inside
    for cost, multiplicity in costs:
        used = min(needed, multiplicity)
        needed -= used
        total += used * cost
        if total > r - 1:
            return True
        if needed == 0:
            return False
    return True  # More unassigned points were required than all pairs can support.


def check_order(r, common):
    s = (r - 1) // 2
    profiles = 0
    for deficit in range(s - 1):
        for partition in partitions(deficit, deficit):
            rows = partition + (0,) * (s - len(partition))
            pairs = Counter(combinations(rows, 2))
            for inside in range(r):
                for cutoff in (r // 3 + 1, r // 3):
                    if any(excludes(r, common, rows, pairs, inside, cutoff, gate)
                           for gate in range(r // 4, -1, -1)):
                        break
                else:
                    raise AssertionError((r, common, rows, inside))
                profiles += 1
    return profiles


if __name__ == "__main__":
    expected = (77, 156, 285, 510, 855, 1407, 2231, 3475, 5265, 7888)
    for r, count in zip(range(11, 31, 2), expected):
        common = 2 if r == 11 else 3
        found = check_order(r, common)
        if found != count:
            raise AssertionError((r, found, count))
        print(f"Order {r}, common bound {common}: all {found} row budgets excluded.")
