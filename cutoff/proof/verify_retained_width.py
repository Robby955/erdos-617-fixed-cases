"""Exact certificate for retained-width.md, using the previous signed-cut checker."""

from fractions import Fraction as F
from math import isqrt

import verify_weighted_width as previous


EXPONENT = 144
K = previous.K
P_MAX = previous.P_MAX
TAU = previous.TAU


def reserved_fraction(p):
    return (391 + F(1464, 5) * p) / K


def affine_saving(p):
    return (4333 + 737 * p) / 10000


def certified_small_weight_saving(lam):
    scale = 10**7
    root_lower = F(isqrt(int(lam * scale**2)), scale)
    assert 0 <= root_lower**2 <= lam <= 1
    z = 1 + root_lower
    return z - previous.log_bounds(F(2))[1] - previous.log_bounds(z)[1]


def check_endpoint_bounds():
    p_half = (F(K, 2) - 391) / F(1464, 5)
    assert 0 < p_half < P_MAX
    assert 1 - F(1, 8) + 2 - 3 * previous.log_bounds(F(2))[1] > F(3, 4)
    for p in (F(0), P_MAX):
        lam = reserved_fraction(p)
        assert 0 < lam < 1
        assert certified_small_weight_saving(lam) > affine_saving(p)
        assert affine_saving(p) < F(3, 4)
    for p in (p_half, P_MAX):
        lam = reserved_fraction(p)
        assert F(1, 2) + F(3, 5) * (lam - F(1, 2)) >= affine_saving(p)


def band_vertices(lo, hi):
    trapezoid = [(F(0), F(0)), (P_MAX, F(0)),
                 (P_MAX, (1 - P_MAX / 4) / TAU), (F(0), 1 / TAU)]

    def budget(point):
        p, t = point
        return 2 - p / 2 - TAU * t

    vertices = {v for v in trapezoid if lo <= budget(v) <= hi}
    for a, b in zip(trapezoid, trapezoid[1:] + trapezoid[:1]):
        left, right = budget(a), budget(b)
        for cut in (lo, hi):
            if min(left, right) < cut < max(left, right):
                weight = (cut - left) / (right - left)
                vertices.add(tuple(x + weight * (y - x) for x, y in zip(a, b)))
    assert vertices
    return vertices


def check_width_and_cut():
    lo = F(0)
    widths, cuts = [], []
    for hi, b, ai, bi in previous.BANDS:
        alpha, beta = F(ai, 4000), F(bi, 4000)
        penalty = (1 - 2 * TAU - F(1, 256)) / (2 * beta)
        assert penalty * K - 2 >= F(3, 5)
        assert 2**(EXPONENT - b) > (8 * (K + 2 * 1411))**4
        log_lower = (F(EXPONENT - b, 4) - 10) * previous.log_bounds(F(2))[0]
        log_lower -= previous.log_bounds(F(K, 1024))[1]
        margins = []
        for p, t in band_vertices(lo, hi):
            y = 2 - p / 2 - TAU * t
            cost = y / alpha + (p + t) / beta
            margins.extend(log_lower - cost + saving
                           for saving in (reserved_fraction(p), affine_saving(p)))
        widths.append(min(margins))
        for j in range(previous.BINS):
            left, right = F(j, previous.BINS), F(j + 1, previous.BINS)
            peak = min(right, max(left, F(1, 2)))
            cuts.extend(previous.sampling(alpha * right, 2 * beta * right,
                                          4 * beta**2 * peak * (1 - peak), F(2**b), hi))
        lo = hi
    assert lo == 2 and len(cuts) == 1280
    assert min(widths) > F(1, 1000)
    assert min(cuts) > F(3327, 10**7)
    return widths, cuts


def check_next_exponent():
    hi, b, ai, bi = previous.BANDS[0]
    p = P_MAX
    t = (1 - p / 4) / TAU
    y = 2 - p / 2 - TAU * t
    assert 0 <= y <= hi
    alpha, beta = F(ai, 4000), F(bi, 4000)
    log_upper = (F(EXPONENT - 1 - b, 4) - 10) * previous.log_bounds(F(2))[1]
    log_upper -= previous.log_bounds(F(K, 1024))[0]
    margin = log_upper - y / alpha - (p + t) / beta
    margin += min(reserved_fraction(p), affine_saving(p))
    assert margin < -F(17, 100)
    return margin


if __name__ == "__main__":
    check_endpoint_bounds()
    previous.auxiliary_checks()
    widths, cuts = check_width_and_cut()
    print(f"Cutoff 2^{EXPONENT}. Width margins:", ", ".join(f"{float(x):.9f}" for x in widths))
    print(f"All {len(cuts)} signed-cut endpoints pass; minimum {float(min(cuts)):.9f}.")
    print(f"First-band sufficient comparison at 2^{EXPONENT - 1}: at most {float(check_next_exponent()):.9f}.")
