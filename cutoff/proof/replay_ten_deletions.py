"""Independent budget-first replay of Theorem 21, Section 12 of overfull-core.md."""

from functools import cache
from math import comb


MAX_ORDER = {0: 0, 1: 9, 2: 19, 3: 29, 4: 40}


@cache
def budget_survives(alpha, vertices, budget):
    """True if the deletion inequalities leave at least one possible degree path."""
    if budget < 0 or (alpha in MAX_ORDER and vertices > MAX_ORDER[alpha]):
        return False
    if vertices == 0:
        return True
    if alpha == 1:
        return budget >= comb(vertices, 2)
    for degree in range(min(vertices - 1, 2 * budget // vertices) + 1):
        residual = vertices - degree - 1
        transversal = max(0, residual - MAX_ORDER.get(alpha - 2, residual))
        cost = comb(degree + 1, 2)
        if degree == 9:
            cost += max(1, transversal - 1)
        elif degree == 10:
            cost += max(9, 2 * transversal - 6)
        elif degree > 10:
            cost += 9 * (degree - 9)
        if budget_survives(alpha - 1, residual, budget - cost):
            return True
    return False


if __name__ == "__main__":
    quoted = {5: 281, 6: 332, 7: 376, 8: 422, 9: 468}
    for alpha in range(1, 10):
        n = 10 * alpha + 1
        cap = 505 - 45 * (10 - alpha)
        for t in range(10):
            remaining = 505 - comb(10 - t, 2) - (9 - alpha) * 45
            assert remaining * comb(n, 2) <= cap * comb(n + t, 2)
        assert not budget_survives(alpha, n, cap)
        if alpha in quoted:
            lower = quoted[alpha]
            assert not budget_survives(alpha, n, lower - 1)
            assert budget_survives(alpha, n, lower)
            print(f"{n} vertices: deletion floor {lower}, outer cap {cap}.")
    print("All nine stops excluded. All 90 outer sampling inequalities pass.")
