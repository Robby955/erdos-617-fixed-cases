"""Rational width and signed-cut checks for 15 * 2^140, on the revised bands."""
from fractions import Fraction as F

from verify_retained_width import (
    K, P_MAX, TAU, affine_saving, band_vertices, check_endpoint_bounds, reserved_fraction,
)
from verify_weighted_width import BINS, auxiliary_checks, log_bounds, sampling

# Upper end of the incidence interval, exponent, 4000 * alpha, 4000 * beta.
BANDS = (
    (F(501, 1000), 14, 656, 925),
    (F(55, 100), 14, 656, 923),
    (F(65, 100), 14, 653, 918),
    (F(1), 15, 652, 916),
    (F(2), 17, 654, 918),
)


def verify():
    check_endpoint_bounds()
    auxiliary_checks()
    log_two_lo, log_two_hi = log_bounds(F(2))
    log_k_lo, log_k_hi = log_bounds(F(K, 1024))
    loss = log_bounds(F(16, 15))[1] / 4
    widths, cuts = [], []
    lo = F(0)
    for hi, b, ai, bi in BANDS:
        alpha, beta = F(ai, 4000), F(bi, 4000)
        assert 0 < alpha <= beta and TAU * beta <= alpha
        assert (1 - 2 * TAU - F(1, 256)) * K / (2 * beta) >= 2 + F(3, 5)
        assert 15 * 2**140 > 2**b * (8 * (K + 2 * 1411))**4
        log_scale = (F(144 - b, 4) - 10) * log_two_lo - log_k_hi - loss
        band_widths, band_cuts = [], []
        for p, t in band_vertices(lo, hi):
            y = 2 - p / 2 - TAU * t
            band_widths.append(log_scale - y / alpha - (p + t) / beta
                               + min(reserved_fraction(p), affine_saving(p)))
        for j in range(BINS):
            left, right = F(j, BINS), F(j + 1, BINS)
            peak = min(right, max(left, F(1, 2)))
            band_cuts.extend(sampling(alpha * right, 2 * beta * right,
                                      4 * beta**2 * peak * (1 - peak), F(2**b), hi))
        widths.append(min(band_widths))
        cuts.extend(band_cuts)
        print(f"Y up to {hi}: width {float(min(band_widths)):.9f}, "
              f"signed cut {float(min(band_cuts)):.9f}")
        lo = hi
    assert lo == 2 and len(cuts) == 1280
    assert min(widths) > F(1, 100000) and min(cuts) > 0

    # At exponent 143 the first band's width condition still fails at this corner.
    y = 1 - P_MAX / 4
    hi, b, ai, bi = BANDS[0]
    assert 0 <= y <= hi
    gap = ((F(143 - b, 4) - 10) * log_two_hi - log_k_lo
           - y / F(ai, 4000) - (P_MAX + y / TAU) / F(bi, 4000)
           + min(reserved_fraction(P_MAX), affine_saving(P_MAX)))
    assert gap < -F(157, 1000)
    print(f"Minimum width margin (lower bound): {float(min(widths)):.9f}")
    print(f"Minimum of {len(cuts)} signed-cut endpoints: {float(min(cuts)):.9f}")
    print(f"First-band width margin at 2^143 (upper bound): {float(gap):.9f}")


if __name__ == "__main__":
    verify()
