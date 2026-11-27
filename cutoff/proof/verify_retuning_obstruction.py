"""Exact interval proof for the first pruning corner and the half-width cut."""
from fractions import Fraction as F

from verify_retained_width import P_MAX, TAU, K, affine_saving, reserved_fraction
from verify_weighted_width import C, FILL, LAMBDA, STAR, log_bounds


def log_lower(x):
    """Lower bound for ln(x) when x >= 1."""
    assert x >= 1
    e = (x.numerator // x.denominator).bit_length() - 1
    assert 1 <= x / 2**e < 2
    return e * log_bounds(F(2))[0] + log_bounds(x / 2**e)[0]


def check():
    alpha_cap = F(656, 4000)
    p = P_MAX
    y = 1 - p / 4
    t = y / TAU
    saving = min(reserved_fraction(p), affine_saving(p))
    f, c = FILL, C
    a, k = F(5, 2), F(8, 7)
    assert k == F(4, 3) / (a - F(4, 3))
    # At half-width the cap defining a chooses 5/2 throughout this domain.
    max_ncap = F(513, 512) * alpha_cap / (2*f) + F(1, 256) + F(1, 4*K) + STAR
    assert a * max_ncap < F(249, 250)
    b0 = F(3, 4) * a * (1 + 100*f/K)
    noise = k * (1 + a*y/f)**2 / (2*f**2)
    target_exponent = 143 + F(2, 5)
    boundaries = [F(0)] + [F(n, 10000) for n in range(2000, 2501)]
    gaps = []
    impossible = 0
    for low, high in zip(boundaries, boundaries[1:]):
        kap = low**2 / f
        assert 2 - a * F(1, 4)**2 / f > 0
        base_repair = k * (b0 * kap)**2 / (2 - a*kap)
        room = c - LAMBDA*kap - c*base_repair
        if room <= 0:
            impossible += 1
            continue
        r_scale_floor = c * noise / room
        # ln(r) must exceed ln(R) + 4 ln(K) + 4 (cost - saving).
        log_order_floor = (log_lower(r_scale_floor) + 4*log_lower(F(K))
                           + 4*(y/alpha_cap + (p+t)/high - saving))
        gap = log_order_floor - target_exponent*log_bounds(F(2))[1]
        assert gap > F(1738, 100000), (low, high, gap)
        gaps.append(gap)
    assert (len(gaps), impossible) == (350, 151)
    print(f"501 beta intervals: {len(gaps)} width exclusions, "
          f"{impossible} nonpositive cut allowances.")
    print(f"Minimum certified log-order gap above (143 + 2/5) log 2: {float(min(gaps)):.9f}")


if __name__ == "__main__":
    check()
