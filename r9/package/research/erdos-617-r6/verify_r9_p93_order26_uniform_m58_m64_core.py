#!/usr/bin/env python3
"""Check the finite arithmetic in the uniform m=58,...,64 core lemma."""

from __future__ import annotations


def odd_cycle_bound(length: int) -> int:
    outside = 16 - length
    return length + 2 * outside + outside * outside // 4


def main() -> None:
    odd_cycle_rows = {
        length: odd_cycle_bound(length) for length in range(5, 16, 2)
    }
    if max(odd_cycle_rows.values()) != 57:
        raise AssertionError(f"odd-cycle bound mismatch: {odd_cycle_rows}")

    mixed_eight_products = {
        part: part * (8 - part) for part in range(1, 8)
    }
    if min(mixed_eight_products.values()) != 7:
        raise AssertionError(
            f"mixed independent-eight bound mismatch: {mixed_eight_products}"
        )

    thresholds = {}
    for edges in range(58, 65):
        deleted = 64 - edges
        threshold = 14 - deleted
        thresholds[edges] = threshold
        for left in range(1, 9):
            for right in range(1, 9):
                cover_size = 16 - left - right
                if cover_size <= threshold and left * right <= deleted:
                    raise AssertionError(
                        "mixed cover violates threshold: "
                        f"m={edges} d={deleted} cover={cover_size} "
                        f"parts=({left},{right})"
                    )

    m59_mixed_ten = {
        (left, right)
        for left in range(1, 9)
        for right in range(1, 9)
        if 16 - left - right == 10 and left * right <= 5
    }
    if m59_mixed_ten != {(1, 5), (5, 1)}:
        raise AssertionError(f"m=59 mixed ten-cover mismatch: {m59_mixed_ten}")

    m59_through_eleven = {
        (left, right)
        for left in range(1, 9)
        for right in range(1, 9)
        if 16 - left - right <= 11 and left * right <= 5
    }
    expected_through_eleven = {(1, 4), (4, 1), (1, 5), (5, 1)}
    if m59_through_eleven != expected_through_eleven:
        raise AssertionError(
            f"m=59 through-eleven classification mismatch: {m59_through_eleven}"
        )

    m59_through_twelve = {
        (left, right)
        for left in range(1, 9)
        for right in range(1, 9)
        if 16 - left - right <= 12 and left * right <= 5
    }
    expected_through_twelve = expected_through_eleven | {
        (1, 3),
        (3, 1),
        (2, 2),
    }
    if m59_through_twelve != expected_through_twelve:
        raise AssertionError(
            f"m=59 through-twelve classification mismatch: {m59_through_twelve}"
        )

    print(f"odd_cycle_bounds={odd_cycle_rows}")
    print(f"cover_thresholds={thresholds}")
    print(f"m59_mixed_ten={sorted(m59_mixed_ten)}")
    print("uniform_m58_m64_core_arithmetic=VERIFIED")


if __name__ == "__main__":
    main()
