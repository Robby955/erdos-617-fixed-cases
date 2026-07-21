#!/usr/bin/env python3
"""Arithmetic checks for COLORED_CORE_LADDER.md."""

from __future__ import annotations

from functools import lru_cache
from math import comb


def p(independence_cap: int, order: int) -> int:
    quotient, remainder = divmod(order, independence_cap)
    return (independence_cap - remainder) * comb(quotient, 2) + remainder * comb(
        quotient + 1, 2
    )


def density_cap(r: int, order: int) -> int:
    return comb(order, 2) - (r - 1) * p(r, order)


def exact_thresholds(r: int) -> dict[int, int | None]:
    thresholds: dict[int, int | None] = {2: 0}
    for s in range(3, r):
        previous = thresholds[s - 1]
        if previous is None:
            thresholds[s] = None
            continue
        coefficient = (s + 1) * r - 2 * s - previous + 1
        constant = (
            r * s * (s + previous - 2) - 2 * (r - 1) * (s - 1)
        )
        if coefficient <= 0:
            thresholds[s] = None
            continue
        threshold = max(1, constant // coefficient + 1)
        thresholds[s] = threshold if threshold < r else None
    return thresholds


def check_induced_density_formulas() -> None:
    for r in range(3, 101):
        for order in range(0, r * r + 2):
            quotient, remainder = divmod(order, r)
            closed = r * comb(quotient, 2) + quotient * remainder
            assert p(r, order) == closed
        assert p(r, 2 * r) == r
        assert p(r, 2 * r + 1) == r + 2
        assert density_cap(r, 2 * r) == r * r
        assert density_cap(r, 2 * r + 1) == r * r + 2

        for d in range(0, r):
            order = r * r - d
            assert p(r, order) == (r - 1) * (r * r - 2 * d) // 2
            expected_cap = r * r * (r - 1) - 2 * r * d + d * (d + 3) // 2
            assert density_cap(r, order) == expected_cap


def check_exact_recursion() -> None:
    for r in range(6, 501):
        thresholds = exact_thresholds(r)
        assert thresholds[2] == 0
        assert thresholds[3] == 1
        for s in range(3, r):
            threshold = thresholds[s]
            previous = thresholds[s - 1]
            if threshold is None or previous is None:
                continue
            degree_cap = (s - 1) * r + previous - 1

            def margin(offset: int) -> int:
                order = s * r + offset
                nonpartite_lower = p(r, order) + s - 1
                return 2 * (r - 1) * nonpartite_lower - order * degree_cap

            assert margin(threshold) > 0
            if threshold > 1:
                assert margin(threshold - 1) <= 0
            first_increment = 2 * (r - 1) * s - degree_cap
            assert first_increment > 0
            # Later increments replace s by floor(order/r) >= s.
            assert margin(r - 1) > 0


def check_closed_form_ladder() -> None:
    for r in range(6, 501):
        for s in range(3, r):
            if 2 * r <= s * s - s + 4:
                continue
            previous = comb(s - 2, 2)
            threshold = comb(s - 1, 2)
            degree_cap = (s - 1) * r + previous - 1
            order = s * r + threshold
            margin = 2 * (r - 1) * p(r, order) - order * degree_cap
            numerator = (s - 2) * (s - 1) * (2 * r - s * s + s - 4)
            assert numerator % 4 == 0
            expected = numerator // 4
            assert margin == expected
            assert margin > 0


def kp_stop_feasible(r: int, d: int, s: int) -> bool:
    t = r - d
    order = s * r + t
    blocks = r - s - 1
    average = r * (r * r + 1) // 2
    upper = average - d - comb(d, 2) - blocks * comb(r, 2)
    lower = p(s, order) + order // s
    return lower <= upper


def check_block_and_kp_gap() -> None:
    for r in range(6, 501):
        thresholds = exact_thresholds(r)
        for d in range(2, r):
            t = r - d
            # A maximal extension of r-4 blocks lands in s <= 3.
            assert t >= thresholds[3]

            # The scalar KP test always leaves the no-block stop s=r-1.
            assert kp_stop_feasible(r, d, r - 1)
            slack = (d * (2 * r - d - 1) - 2 * r) // 2
            assert slack > 0

            feasible = [s for s in range(2, r) if kp_stop_feasible(r, d, s)]
            surviving = [
                s
                for s in feasible
                if thresholds[s] is None or t < thresholds[s]
            ]
            assert surviving


def ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def kp_recursive_baseline(r: int, independence_cap: int, order: int) -> int:
    baseline = p(independence_cap, order)
    if order >= independence_cap * r + 1:
        return baseline + order // independence_cap
    if order > independence_cap * (r - 1):
        return baseline + order // independence_cap - 1
    return baseline


def star_contribution(r: int, degree: int) -> int:
    if degree < r - 1:
        return comb(degree + 1, 2)
    if degree == r - 1:
        return comb(r, 2) + 1
    return degree + ceil_div((r + 2) * comb(degree, 2), r)


def recursive_colored_bound(r: int):
    thresholds = exact_thresholds(r)

    @lru_cache(maxsize=None)
    def bound(independence_cap: int, order: int) -> int | None:
        """Return B_r(a,m); None represents the certified empty family."""
        if order < 0:
            return None
        if independence_cap == 0:
            return 0 if order == 0 else None
        if independence_cap == 1:
            return comb(order, 2) if order <= r - 1 else None

        threshold = thresholds.get(independence_cap)
        if threshold is not None and order >= independence_cap * r + threshold:
            return None

        candidates: list[int] = []
        for degree in range(order):
            previous = bound(independence_cap - 1, order - 1 - degree)
            if previous is None:
                continue
            candidates.append(
                max(
                    previous + star_contribution(r, degree),
                    ceil_div(order * degree, 2),
                )
            )
        if not candidates:
            return None

        lower = max(
            kp_recursive_baseline(r, independence_cap, order), min(candidates)
        )
        if lower > density_cap(r, order):
            return None
        return lower

    return bound


def packing_margin(r: int, d: int, blocks: int, bound) -> int | None:
    independence_cap = r - 1 - blocks
    order = r * r - d - blocks * r
    lower = bound(independence_cap, order)
    if lower is None:
        return None
    least_color_average = r * (r * r + 1) // 2
    upper = (
        least_color_average
        - d
        - comb(d, 2)
        - blocks * comb(r, 2)
    )
    return lower - upper


def check_recursive_block_production() -> None:
    expected_r7 = {
        0: [57, None, None],
        1: [42, None, None],
        2: [25, None, None],
        3: [18, 28, None],
        4: [10, 9, None],
        5: [5, 4, None],
        6: [-1, -2, -3],
    }
    expected_r8 = {
        0: [60, 104, None, None],
        1: [44, 72, None, None],
        2: [35, 41, None, None],
        3: [24, 23, None, None],
        4: [17, 16, None, None],
        5: [8, 7, 6, None],
        6: [3, 2, 1, None],
        7: [-4, -5, -6, -7],
    }

    for r, expected in ((7, expected_r7), (8, expected_r8)):
        bound = recursive_colored_bound(r)
        actual = {
            d: [packing_margin(r, d, blocks, bound) for blocks in range(r - 4)]
            for d in range(r)
        }
        assert actual == expected

    bound7 = recursive_colored_bound(7)
    for d in range(6):
        margins = [packing_margin(7, d, blocks, bound7) for blocks in range(3)]
        assert all(margin is None or margin > 0 for margin in margins)
    unresolved_r7 = [
        packing_margin(7, 6, blocks, bound7) for blocks in range(3)
    ]
    assert unresolved_r7 == [-1, -2, -3]

    bound8 = recursive_colored_bound(8)
    for d in range(7):
        margins = [packing_margin(8, d, blocks, bound8) for blocks in range(4)]
        assert all(margin is None or margin > 0 for margin in margins)
    unresolved_r8 = [
        packing_margin(8, 7, blocks, bound8) for blocks in range(4)
    ]
    assert unresolved_r8 == [-4, -5, -6, -7]


def main() -> None:
    check_induced_density_formulas()
    check_exact_recursion()
    check_closed_form_ladder()
    check_block_and_kp_gap()
    check_recursive_block_production()
    print("colored_induced_density_arithmetic=true")
    print("exact_colored_core_thresholds_r6_500=true")
    print("closed_form_colored_core_ladder_r6_500=true")
    print("r_minus_4_block_arithmetic=true")
    print("kp_scalar_gap_r6_500=true")
    print("recursive_block_production_r7_r8=true")
    print("r7_least_color_degree_reduced_to_six=true")
    print("r8_least_color_degree_reduced_to_seven=true")


if __name__ == "__main__":
    main()
