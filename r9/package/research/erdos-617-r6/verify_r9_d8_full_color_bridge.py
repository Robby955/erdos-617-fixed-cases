#!/usr/bin/env python3
"""Verify the fixed-r=9 degree-eight full-color bridge and propagation."""

from __future__ import annotations

from functools import cache
from math import comb


R = 9
CLIQUE_EDGES = comb(R, 2)
LEAST_COLOR_BUDGET = R * (R * R + 1) // 2
P3_ORDER26_FLOOR = 121
P4_ORDER37_FLOOR = 192


def ceil_div(numerator: int, denominator: int) -> int:
    return -(-numerator // denominator)


def turan_floor(independence_cap: int, order: int) -> int:
    quotient, remainder = divmod(order, independence_cap)
    return (
        (independence_cap - remainder) * comb(quotient, 2)
        + remainder * comb(quotient + 1, 2)
    )


def colored_cap(order: int) -> int:
    return comb(order, 2) - (R - 1) * turan_floor(R, order)


def thresholds() -> dict[int, int]:
    result = {2: 0}
    for layer in range(3, R):
        previous = result.get(layer - 1)
        if previous is None:
            break
        coefficient = (layer + 1) * R - 2 * layer - previous + 1
        constant = (
            R * layer * (layer + previous - 2)
            - 2 * (R - 1) * (layer - 1)
        )
        if coefficient <= 0:
            break
        value = max(1, constant // coefficient + 1)
        if value >= R:
            break
        result[layer] = value
    return result


THRESHOLDS = thresholds()


def scalar_floor(independence_cap: int, order: int) -> int:
    value = turan_floor(independence_cap, order)
    if order <= independence_cap * (R - 1):
        return value
    if order <= independence_cap * R:
        return value + order // independence_cap - 1
    return value + order // independence_cap


def star_contribution(degree: int) -> int:
    if degree < R - 1:
        return comb(degree + 1, 2)
    if degree == R - 1:
        return CLIQUE_EDGES + 1
    return degree + ceil_div((R + 2) * comb(degree, 2), R)


class Certificate:
    def __init__(self, p4_floor: int, empty_p3_order27: bool) -> None:
        self.p4_floor = p4_floor
        self.empty_p3_order27 = empty_p3_order27

    @cache
    def bound(self, independence_cap: int, order: int) -> int | None:
        if independence_cap == 0:
            return 0 if order == 0 else None
        if independence_cap == 1:
            return comb(order, 2) if order <= R - 1 else None
        if self.empty_p3_order27 and (independence_cap, order) == (3, 27):
            return None
        threshold = THRESHOLDS.get(independence_cap)
        if threshold is not None and order >= independence_cap * R + threshold:
            return None

        branches = []
        for degree in range(order):
            previous = self.bound(independence_cap - 1, order - 1 - degree)
            if previous is None:
                continue
            branches.append(
                max(
                    previous + star_contribution(degree),
                    ceil_div(order * degree, 2),
                )
            )
        if not branches:
            return None

        value = max(scalar_floor(independence_cap, order), min(branches))
        if (independence_cap, order) == (3, 26):
            value = max(value, P3_ORDER26_FLOOR)
        if (independence_cap, order) == (3, 27):
            value = max(value, ceil_div(27 * P3_ORDER26_FLOOR, 25))
        if (independence_cap, order) == (4, 37):
            value = max(value, self.p4_floor)
        return None if value > colored_cap(order) else value


def outer_upper(degree: int, blocks: int) -> int:
    return (
        LEAST_COLOR_BUDGET
        - degree
        - comb(degree, 2)
        - blocks * CLIQUE_EDGES
    )


def outer_margin(certificate: Certificate, degree: int, blocks: int) -> int | None:
    independence_cap = R - 1 - blocks
    order = R * R - degree - blocks * R
    bound = certificate.bound(independence_cap, order)
    return None if bound is None else bound - outer_upper(degree, blocks)


def check_bridge_arithmetic() -> None:
    assert colored_cap(11) == 39
    assert colored_cap(26) == 125
    assert colored_cap(27) == 135
    minimum_missing_edges = 10 + comb(10, 2) - colored_cap(11)
    assert minimum_missing_edges == 16
    for missing_edges in range(minimum_missing_edges, comb(10, 2) + 1):
        shell_edges = comb(10, 2) - missing_edges
        cross_edges = 2 * missing_edges
        lower = 10 + shell_edges + P3_ORDER26_FLOOR + cross_edges
        assert lower == 176 + missing_edges
        assert lower >= P4_ORDER37_FLOOR
    corrupted_lower = 10 + (comb(10, 2) - 15) + P3_ORDER26_FLOOR + 2 * 15
    assert corrupted_lower == P4_ORDER37_FLOOR - 1
    assert 2 * 191 // 37 == 10


def check_propagation() -> None:
    assert THRESHOLDS == {2: 0, 3: 1, 4: 2, 5: 4, 6: 8}
    certificate = Certificate(P4_ORDER37_FLOOR, True)
    diagonal = [certificate.bound(layer, 9 * layer + 1) for layer in range(4, 9)]
    assert diagonal == [192, 227, 264, 301, 338]
    d8_margins = tuple(outer_margin(certificate, 8, blocks) for blocks in range(5))
    assert d8_margins == (5, 4, 3, 2, 3)

    all_margins = tuple(
        tuple(outer_margin(certificate, degree, blocks) for blocks in range(5))
        for degree in range(9)
    )
    assert all(
        margin is None or margin > 0
        for row in all_margins
        for margin in row
    )

    weak_bridge = Certificate(189, True)
    assert tuple(outer_margin(weak_bridge, 8, block) for block in range(5)) == (
        4,
        3,
        2,
        1,
        0,
    )
    missing_terminal = Certificate(P4_ORDER37_FLOOR, False)
    assert tuple(
        outer_margin(missing_terminal, 8, block) for block in range(5)
    ) == (-1, -2, -3, -4, 3)


def main() -> None:
    check_bridge_arithmetic()
    check_propagation()
    print("fixed-r9 degree-eight full-color bridge: PASS")
    print("P3_26_floor=121 P3_27=EMPTY P4_37_floor=192")
    print("diagonal_P4_to_P8=192,227,264,301,338")
    print("d8_margins_j0_to_j4=5,4,3,2,3")
    print("all_45_outer_cells=STRICT_OR_EMPTY")
    print("bridge_M_range=16..45 lower=176+M")
    print("corrupt_bridge_M_15_lower=191")
    print("corrupt_P4_37_189_last_margin=0")
    print("corrupt_P3_27_finite_d8_margins=-1,-2,-3,-4,3")


if __name__ == "__main__":
    main()
