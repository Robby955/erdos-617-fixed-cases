"""Rational certificates for cutoff-refinement.md. Run with Python 3."""

from fractions import Fraction as F
from itertools import combinations
from math import comb


TAU = F(4, 25)
GAMMA = F(71, 500)
KAPPA = F(1, 81)
C = F(49, 1000)
MIN_S = 2**18
MAX_RHO = F(1, 4 * MIN_S)
INV_R = F(1, 2**20)
SIZE_FACTOR = 2**38  # r >= SIZE_FACTOR * s**4


def pairs(n: int) -> int:
    return n * (n - 1) // 2


def check_row_accounting() -> int:
    size_cutoff = F(17, 25)
    lost = 2 * TAU
    initial_deficit = 1 / TAU + F(1, 2)
    assert initial_deficit == F(27, 4)
    assert initial_deficit / (1 - size_cutoff) < 22
    assert lost / (size_cutoff - lost) == F(8, 9)
    assert 1 - size_cutoff >= lost and 1 - lost >= lost
    assert 21 * (1 + 9 + 8) + 128 <= 512
    assert (1 + 1 / TAU) / 2 >= 1
    assert 1 + 1 / TAU + F(1, 2) == F(31, 4)

    # The exact color budget in an oversized original part, including d=0.
    count = 0
    for r in range(3, 50):
        for oversize in range(r + 1):
            for deficit in range(r + 1):
                cap = pairs(r + oversize) - pairs(r - deficit) - (r - 1) * oversize
                assert cap == r * deficit + pairs(oversize + 1) - pairs(deficit + 1)
                assert pairs(oversize + 1) <= oversize**2
                count += 1
        coefficient = 2 * (1 + 1 / TAU) + F(r, r - 1)
        assert coefficient > 1
        assert coefficient * pairs(r) + r == F(31, 4) * r*r - r / TAU
    return count


def check_width() -> F:
    alpha, beta_squared = GAMMA / 4, KAPPA / 4
    x_squared = alpha**2 / beta_squared
    assert 0 < x_squared < 1
    # Integrate the finite geometric upper bound for 1/(1+t*t).
    kernel = 1 / alpha + alpha / beta_squared * sum(
        (-x_squared)**j / (2*j + 1) for j in range(9)
    )
    assert kernel < F(3841, 100)
    log_two_lower = 2 * sum(F(1, (2*j + 1) * 3**(2*j + 1)) for j in range(3))
    assert log_two_lower > F(693, 1000)
    harmonic_upper = (1 + F(512, MIN_S)) * (1 + F(1, MIN_S)) * kernel * F(31, 4)
    assert harmonic_upper < (450 - 19) * F(693, 1000)
    threshold = SIZE_FACTOR * (2**450 + 513)**4
    assert 2**1838 < threshold < 2**1839
    assert F(1, SIZE_FACTOR * MIN_S**2) < F(1, 2**40)
    return kernel


def check_partition_identity() -> int:
    """Test the coupled loss budget on all six-vertex graphs with independence at most two."""
    vertices = range(6)
    edges = list(combinations(vertices, 2))
    bits = {edge: 1 << i for i, edge in enumerate(edges)}
    triples = [sum(bits[edge] for edge in combinations(triple, 2))
               for triple in combinations(vertices, 3)]
    # Up to relabeling these are all size profiles for two parts, allowing an empty part.
    partitions = []
    for first in range(4):
        internal = sum(bit for (u, v), bit in bits.items() if (u < first) == (v < first))
        variance = 2 * (3 - first)**2
        partitions.append((internal, variance))
    checked = 0
    for graph in range(1 << len(edges)):
        if any(graph & triple == 0 for triple in triples):
            continue
        surplus = graph.bit_count() - 2 * pairs(3)
        for internal, variance in partitions:
            missing = (internal & ~graph).bit_count()
            crossing = (graph & ~internal).bit_count()
            assert 2 * crossing + variance == 2 * (surplus + missing)
            if missing <= surplus:
                assert 2 * crossing + variance <= 4 * surplus
                checked += 1
    assert checked > 0
    return checked


def check_shortfall() -> None:
    delta, aux_degree, large = F(7, 100), F(2, 25), F(73, 200)
    max_arrivals = F(11, 50)
    cross = C**2 + F(1, 2**40)
    assert (2 + F(1, MIN_S)) * C**2 + F(3, 2**40) < delta**2 < aux_degree**2
    # For a signed displacement b, balance the h part sizes by integer division.
    for h in range(1, 30):
        for displacement in range(-3*h, 3*h + 1):
            q, j = divmod(displacement, h)
            variance = (h - j)*q*q + j*(q + 1)**2
            assert h * variance == displacement**2 + j*(h - j)
            assert variance <= F(displacement**2, h) + F(h, 4)
    assert INV_R < C
    assert 1 - delta - 2 * aux_degree > F(1, 2) and 4 * cross < 1
    assert 100 * cross < 1
    ordinary_size = F(255, 256)
    assert 1 - 33 * GAMMA * MAX_RHO >= ordinary_size
    assert 4 * 400**2 * (2 * GAMMA * MAX_RHO + INV_R**2) < 1
    assert ordinary_size - F(1, 4) > F(1, 400)
    assert F(1, 32) < aux_degree
    assert 1 - delta - large - 4 * aux_degree > F(1, 10)
    assert 1 - delta - 2 * large > F(1, 10)
    assert ordinary_size - large - F(1, 4) - F(4, 32) > F(1, 400)
    assert ordinary_size - 2 * large - F(1, 4) > F(1, 400)
    assert large * (max_arrivals - INV_R) > (
        (1 - max_arrivals + INV_R) * delta
        + max_arrivals**2 / 2 + max_arrivals * INV_R / 2
    )
    penalty = (max_arrivals + INV_R) / 2
    for count, list_fraction in [(2, F(9, 125)), (3, F(13, 100)), (4, F(9, 50))]:
        assert comb(count, 2) * (INV_R + delta**2) < list_fraction**2
        assert 1 - delta - list_fraction + (count - 1) * large - count * penalty > 1
    assert 5 * (large - penalty) > 1


def check_sampling() -> F:
    s, rho = MIN_S, MAX_RHO
    inflation = 1 + F(1, 512)
    rep_factor = F(512, 255)
    assert F(255, 256) - F(1, 4) - F(1, 2) - TAU - F(1, 12) > F(1, 400)
    assert 4 * GAMMA * rho * F(256, 255) < F(1, 512)
    assert 7 * inflation * GAMMA + 7 * GAMMA * rho < 1
    assert 4 * 30 * inflation < 124
    assert 7 * 124 + F(7 * 52, 2 * s) < 1200
    assert (1201**2 + F(1200, s)) / 2 < 2**20
    assert 3 * 52 == 156 and 156 * 124 < 2**15
    assert 6 * 30 * inflation + 3 * 52**2 < 2**14
    linear_error = F(2**14, s*s) + 2**20 + F(1, 2*s) + F(7 * 2**15, s)
    assert linear_error < 2**21
    least = min(1 - F(49, 2) * KAPPA - F(1, 4), F(5, 2) - rep_factor)
    assert least == F(145, 324)
    assert 425 * least > 12 + F(81, 2) + 105**2 * KAPPA
    assert 2**21 / least < 2**23
    assert 6 * 425 + 12 == 2562 and 6 * 2**23 + F(2**14, s*s) < 2**26
    assert 2562 + 2 == 2564 and 2**26 + F(1, 2) + F(1, 2*s) < 2**27
    assert 24 * 425 + 12 < 10250 and 24 * 2**23 + F(2**14, s*s) < 2**28
    assert 2 * (2**28 + 1) < 2**30
    assert 20500 * KAPPA**2 * rho**2 + F(2**30, SIZE_FACTOR*s*s) < min(C / 128, F(1, 16))
    eps = F(81, 200)
    assert 2564 * KAPPA**2 + 2 * KAPPA * GAMMA + F(16 * 2**27, SIZE_FACTOR) < eps
    coefficient = 1 - 2 * GAMMA - eps / 2
    assert coefficient > 0 and 2**30 + F(1, s) < 2**31
    gap = (
        coefficient * (C - 2 * KAPPA * rho) - 2 * KAPPA
        - 20500 * KAPPA**2 * rho - F(4 * 2**31, SIZE_FACTOR * s)
    )
    assert gap > F(1, 4096)
    return gap


def check_width_obstructions() -> None:
    log_two_upper = F(7, 10)
    assert 1 + log_two_upper + log_two_upper**2 / 2 + log_two_upper**3 / 6 > 2
    assert (1 + 260 * log_two_upper) / 28 < F(27, 4)
    assert F(1, 28) > GAMMA / 4
    total_centers = (1 + 60 * log_two_upper) / 28 + F(1, 1000)
    assert (2 * TAU + F(1, 1000)) * total_centers < F(999, 2000)
    assert 1 - F(1, 28) - F(1, 1000) > F(17, 25)
    assert F(1, 1000) + 2 * TAU + F(1, 1000) < 1

    # At a small prime, label every vertical pair, prune, and measure the cuts.
    r, active = 59, 3
    centers = [(r + 28*i - 1) // (28*i) for i in range(1, active + 1)]
    donors = range(active, active + (8*r // 25) + 1)
    cross = [[0] * r for _ in range(r)]
    extra = [0] * r
    other = 0
    for col in range(r):
        for left, right in combinations(range(r), 2):
            if left < active and col < centers[left] and right in donors:
                cross[left][col] += 1
                cross[right][col] += 1
                extra[0] += 1
            else:
                extra[1 + other % (r - 1)] += 1
                other += 1
    assert extra[0] == len(donors) * sum(centers) == min(extra)
    assert r**2 * pairs(r) + sum(extra) == pairs(r*r)
    weights = []
    for i, degrees in enumerate(cross):
        removed = [j for j, degree in enumerate(degrees) if 25 * degree > 8 * r]
        deficit = centers[i] if i < active else 0
        assert removed == list(range(deficit))
        cut = deficit * (r - deficit) + sum(degrees[deficit:])
        weights.append(max(F(deficit, r), F(cut, r*r)))
    for i, weight in enumerate(sorted(weights, reverse=True)[:active], start=1):
        assert i * weight >= F(1, 28)


if __name__ == "__main__":
    count = check_row_accounting()
    kernel = check_width()
    partitions = check_partition_identity()
    check_shortfall()
    margin = check_sampling()
    check_width_obstructions()
    print(f"{count:,} local binomial identities checked; row mass at most 31/4.")
    print(f"{partitions:,} six-vertex graph and partition checks of the shared loss budget.")
    print(f"Rational upper bound on width kernel rounds to {float(kernel):.6f}; K = 2^450.")
    print("Auxiliary extraction, list extensions, arrival bounds and sampling checks passed.")
    print(f"Endpoint margin {margin} > 1/4096. Sufficient order in the draft: 2^1839.")
    print("Harmonic obstruction and labeled affine-square checks passed.")
