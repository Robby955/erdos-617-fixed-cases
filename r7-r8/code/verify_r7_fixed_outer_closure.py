#!/usr/bin/env python3
"""Arithmetic replay for R7_FIXED_OUTER_CLOSURE.md."""

from __future__ import annotations

from functools import lru_cache
from math import comb


def ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def turan_complement_floor(independence_cap: int, order: int) -> int:
    quotient, remainder = divmod(order, independence_cap)
    return (
        (independence_cap - remainder) * comb(quotient, 2)
        + remainder * comb(quotient + 1, 2)
    )


def colored_cap(order: int) -> int:
    return comb(order, 2) - 6 * turan_complement_floor(7, order)


def thresholds() -> dict[int, int | None]:
    values: dict[int, int | None] = {2: 0}
    for layer in range(3, 7):
        previous = values[layer - 1]
        if previous is None:
            values[layer] = None
            continue
        coefficient = 7 * (layer + 1) - 2 * layer - previous + 1
        constant = (
            7 * layer * (layer + previous - 2)
            - 12 * (layer - 1)
        )
        threshold = max(1, constant // coefficient + 1)
        values[layer] = threshold if threshold < 7 else None
    return values


def scalar_floor(independence_cap: int, order: int) -> int:
    value = turan_complement_floor(independence_cap, order)
    if order >= 7 * independence_cap + 1:
        return value + order // independence_cap
    if order > 6 * independence_cap:
        return value + order // independence_cap - 1
    return value


def star_floor(degree: int) -> int:
    if degree < 6:
        return comb(degree + 1, 2)
    if degree == 6:
        return 22
    return degree + ceil_div(9 * comb(degree, 2), 7)


def recursive_floor():
    layer_thresholds = thresholds()

    @lru_cache(maxsize=None)
    def floor(independence_cap: int, order: int) -> int | None:
        if order < 0:
            return None
        if independence_cap == 0:
            return 0 if order == 0 else None
        if independence_cap == 1:
            return comb(order, 2) if order <= 6 else None

        threshold = layer_thresholds.get(independence_cap)
        if (
            threshold is not None
            and order >= 7 * independence_cap + threshold
        ):
            return None

        branch_values = []
        for degree in range(order):
            remainder = floor(independence_cap - 1, order - 1 - degree)
            if remainder is None:
                continue
            branch_values.append(
                max(
                    remainder + star_floor(degree),
                    ceil_div(order * degree, 2),
                )
            )
        if not branch_values:
            return None

        value = max(
            scalar_floor(independence_cap, order),
            min(branch_values),
        )
        return None if value > colored_cap(order) else value

    return floor


def main() -> None:
    assert thresholds() == {2: 0, 3: 1, 4: 2, 5: 5, 6: None}

    floor = recursive_floor()
    existing = {
        (3, 20): 63,
        (3, 21): 75,
        (5, 37): 143,
        (5, 38): 153,
        (5, 39): 176,
    }
    assert {
        key: floor(*key)
        for key in existing
    } == existing

    # New P_4 floors. The tuples are
    # (remainder order, remainder floor, fixed star term, cover bound).
    p4_28_branches = {
        6: (21, 75, 21, 4),
        7: (20, 63, 28, 6),
    }
    assert 99 - p4_28_branches[6][1] - p4_28_branches[6][2] == 3
    assert 99 - p4_28_branches[7][1] - p4_28_branches[7][2] == 8
    assert p4_28_branches[6][0] - p4_28_branches[6][3] >= 14
    assert p4_28_branches[7][0] - p4_28_branches[7][3] >= 14

    assert 112 - 75 - 28 == 9
    assert 21 - 7 == 14

    p4 = {28: 100, 29: 113}
    p5 = {
        35: min(p4[29] + star_floor(5), p4[28] + star_floor(6)),
        36: min(p4[29] + star_floor(6), p4[28] + star_floor(7)),
    }
    assert p5 == {35: 122, 36: 134}

    p6_43 = min(
        existing[(5, 39)] + star_floor(3),
        existing[(5, 38)] + star_floor(4),
        existing[(5, 37)] + star_floor(5),
        p5[36] + star_floor(6),
        p5[35] + star_floor(7),
    )
    assert p6_43 == 156

    least_color_edges = 175
    degree = 6
    first_upper = least_color_edges - degree - comb(degree, 2)
    peel_uppers = [
        first_upper - blocks * comb(7, 2)
        for blocks in range(3)
    ]
    assert peel_uppers == [154, 133, 112]
    assert p6_43 > peel_uppers[0]
    assert p5[36] > peel_uppers[1]
    assert p4[29] > peel_uppers[2]

    print("r7_existing_recursive_floors=VERIFIED")
    print("r7_new_floors=P4(28):100,P4(29):113")
    print("r7_new_floors=P5(35):122,P5(36):134,P6(43):156")
    print("r7_peel_uppers=154,133,112")
    print("r7_fixed_outer_closure_arithmetic=VERIFIED")


if __name__ == "__main__":
    main()
