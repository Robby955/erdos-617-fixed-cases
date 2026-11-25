"""Exact certificates for cutoff-218.md, using only the Python standard library."""

from fractions import Fraction as F
from itertools import combinations, product
from math import comb

FILL = F(7, 30)
STRONG_COST = F(501, 1000)
SMALL_U = F(41, 40)
SHORTAGE = F(89, 1000)
ALPHA = F(1, 6)
BETA = F(11, 60)
MIXED_ROWS = 2**36
LOG2_LO = F(6931, 10000)
LOG2_HI = F(7, 10)
ZERO, ONE = F(0), F(1)


def extraction_and_width() -> F:
    tau, length = F(47, 100), F(19, 20)
    rate = F(61, 250)
    inv_r = F(1, 2**20)
    assert F(1, 4)-F(1, 256)-F(1, 512)-inv_r/2 > rate
    assert (F(1, 256)-inv_r)*rate > F(1, 1200)
    assert 2*tau <= 1 and length < 1
    limit = 1/(2*rate)
    corners = ((ZERO, ZERO), (limit, ZERO), (ZERO, 1/tau),
               (limit, (1-limit/4)/tau))
    costs = []
    for single, total in corners:
        residual = 1-single/4-tau*total
        initial = F(1, 2)+single+total
        pairs = (initial+residual)/(1-2*tau)
        assert pairs < 60
        assert (initial+2*tau*60)/(1-length) < 1200
        defect = initial+2*tau*residual/length**2
        assert defect < F(18, 5)
        cut = 2-single/4-tau*total
        costs.append(1+cut/ALPHA+defect/BETA)
    assert 128+600+60+1200+1 <= 2500

    log2_partial = 2*sum(F(1, (2*i+1)*3**(2*i+1)) for i in range(5))
    assert LOG2_LO < log2_partial
    assert log2_partial+F(2, 11*3**11)*F(9, 8) < LOG2_HI
    assert F(2500, 2**11) == F(625, 512)
    assert max(costs) < F(155, 4)*LOG2_LO-F(113, 512)
    assert F(199, 4)-11 == F(155, 4) and 19+199 == 218

    # Even rounding every deficit down and only counting the first M/8 rows.
    assert F(1, 2)-F(1, 2*(2**33+1)) > F(49, 100)
    assert F(4, 25)*(33*LOG2_LO+F(49, 100))-F(1, 8) > F(18, 5)
    return max(costs)


def shortage_certificate() -> None:
    inv_r = F(1, 2**20)
    delta, tau, theta, price = F(3, 25), F(27, 200), F(93, 250), F(53, 500)
    xi = SHORTAGE**2+inv_r
    raw = SHORTAGE+xi/(2*(1-inv_r))
    squared = (2+F(1, 799))*SHORTAGE**2+3*inv_r
    assert raw < tau and raw+(squared-raw**2)/(2*tau) < delta
    assert 1-delta-2*tau > F(1, 2) and 100*xi < 1
    assert 1-delta-theta-3*tau > F(1, 10) and 1-delta-2*theta > F(1, 10)
    assert F(255, 256)-theta-FILL-F(3, 32) > F(1, 61)
    assert F(255, 256)-2*theta-FILL > F(1, 61)
    assert 2*(theta-price) < 1
    assert 2*(theta-price)*(delta+price)-delta > (theta+2*delta+price)*inv_r
    assert theta-delta-2*price > 0
    assert (1-delta-theta)*(theta-delta-2*price) > delta**2+inv_r
    list_three = F(21, 100)
    assert 3*(delta**2+inv_r) < list_three**2
    assert 1-delta-list_three+2*theta-3*price > 1
    assert 4*(theta-price) > 1


def sampling_margins(cut: F, max_defect: F, squared_tail: F, width: int,
                     size_factor: F, cut_sum: F) -> list[F]:
    """Upper bounds for s max y, s max x and s sum x², with s >= width."""
    gamma = cut/FILL
    g = max_defect/FILL
    kappa = squared_tail/FILL
    rho = FILL/width
    eta = 1/(size_factor*FILL**2)
    x = g*rho
    j = (1+80*rho)/(1-x)
    assert width-1 >= 799 and 1/(size_factor*width**2) < F(1, 2**20)
    assert 4*61**2*gamma*rho < 1
    assert 1-x-FILL > F(1, 61) and 1-x-FILL-F(3, 4) > F(1, 61)
    assert F(1, 40)+x+F(1, 256) < F(1, 32)
    assert (g+40*gamma)*rho < F(1, 256)
    assert x+F(1, 2**20) < F(1, 2) and 2*x/(1-x) < F(1, 1000)
    assert 80*rho < 1 and 40*(1-rho)-1-g > 37
    assert 37*(SMALL_U-1/(1-x)) > STRONG_COST*g
    assert 2*j*x < F(1, 512)

    count = F(513, 512)*cut_sum/FILL+F(5, width)
    a = min(F(7, 2), F(249, 250)/(F(513, 512)*gamma+F(1, 256)+x))
    spare = a-F(4, 3)-a*a*kappa/2
    assert spare > 0
    young = F(9, 20)*spare
    k = F(4, 3)/(spare-young)
    b = j*(1+1/k)
    assert a*(F(513, 512)*gamma+F(1, 256)+x)+2*b*x < 1
    assert k*(a-F(4, 3)-a*a*kappa/2-young) == F(4, 3)
    assert k*(b-j) == j and k*((b/j)**2-1) >= 1
    total = a*count+9*b/width
    binomial = ((1+total)**2+total/width)/2
    size_cost = k*(binomial+F(1, 2*width))

    def repair(u_bound: F, loss: F) -> F:
        z = b*u_bound*kappa+loss
        return k*z*z*(F(1, 2)+a*a*kappa/(4*young))+size_cost*eta

    margins = []
    for u_bound, row_cost, loss in (
        (SMALL_U, STRONG_COST, ZERO), (SMALL_U, STRONG_COST, STRONG_COST*kappa),
        (F(2), ZERO, ZERO),
    ):
        z = 8*repair(u_bound, ZERO)+2*eta
        eps = repair(u_bound, loss)+g*loss+loss**2/2+eta*(F(1, 2)+F(1, 2*width))
        assert SHORTAGE > row_cost*kappa*rho and 0 < eps < 1
        assert z*rho**2 < min(SHORTAGE/128, F(1, 16))
        margin = ((1-eps)*(SHORTAGE-row_cost*kappa*rho)+loss-row_cost*kappa-z*rho
                  -1/(FILL*size_factor*width**2))
        assert margin > F(1, 1000), (width, cut, squared_tail, u_bound, float(margin))
        margins.append(margin)
    return margins


def unconditional_certificate() -> list[F]:
    margins = []
    for i in range(64):
        lo, hi = F(i, 64), F(i+1, 64)
        peak = max(lo, min(F(1, 2), hi))
        margins.extend(sampling_margins(ALPHA*hi, 2*BETA*hi, 4*BETA**2*peak*(1-peak),
                                        2500, F(2**19), F(2)))
    return margins


def old_rows_certificate() -> list[F]:
    # The earlier total-degree extraction has q<=9 and at most 18 short parts.
    assert 2*(F(3, 2)+F(3, 4)*4) == 9
    assert 2*(F(9, 2)+F(9, 2)) == 18
    assert 9+18+128 == 155
    r, s, head = 2**50, 800, 644
    q = F(4, 25)
    assert 155+head == s-1
    assert s*(q/(head+1)+F(1, r)) < F(1, 5)
    assert s*(F(1, 100*(head+1))+F(1, r*r)) < F(13, 1000)
    assert 1+36*LOG2_HI < 27
    assert s*(q*q/head+54*q/r+F(MIXED_ROWS, r*r)) < F(4, 125)
    assert head >= 512 and 27*LOG2_HI/100+F(MIXED_ROWS, r*r) < F(19, 100)
    return sampling_margins(F(13, 1000), F(1, 5), F(4, 125), s,
                            F(r, s**4), F(19, 100))


def check_remaining_profile() -> None:
    limit = 2**24
    p, t, tau, length = F(2), F(4, 5), F(47, 100), F(19, 20)
    residual = 1-p/4-tau*t
    assert p <= F(125, 61) and residual > 0
    # (M+3)/3 < 2^23, and sum_{i=1}^M 1/(i+3) <= ln((M+3)/3).
    assert limit+3 < 3*2**23
    assert 23*LOG2_HI/5 < F(1, 2)+p+t+2*tau*residual/length**2
    assert 23*LOG2_HI/100 < 2-p/4-tau*t
    assert F(1, 25)*(F(2501, 2504)-F(2**19+1, limit+4)) > BETA**2


def check_padded_draws() -> int:
    """Enumerate independent choices including an empty outcome on short lists."""
    rows = ((0, 1), (2,), (3, 4, 5))
    pairs = [(x, y) for i in range(3) for k in range(i+1, 3)
             for x in rows[i] for y in rows[k]]
    assert len(pairs) == 11
    laws = [tuple(row)+(None,)*(3-len(row)) for row in rows]
    outcomes = list(product(*laws))
    for mask in range(2**len(pairs)):
        edges = {pair for bit, pair in enumerate(pairs) if (mask >> bit) & 1}
        available = sum(sum(x is not None for x in draw) for draw in outcomes)
        hits = sum(sum((u, v) in edges for u, v in combinations(draw, 2)) for draw in outcomes)
        assert F(available, len(outcomes)) == sum(len(row) for row in rows)/F(3)
        assert F(hits, len(outcomes)) == F(len(edges), 9)
        best = max(len(keep) for draw in outcomes for n in range(4)
                   for keep in combinations((x for x in draw if x is not None), n)
                   if all(pair not in edges for pair in combinations(keep, 2)))
        assert best*len(outcomes) >= available-hits
    return 2**len(pairs)


if __name__ == "__main__":
    cost = extraction_and_width()
    shortage_certificate()
    main = unconditional_certificate()
    mixed = old_rows_certificate()
    check_remaining_profile()
    graphs = check_padded_draws()
    print(f"General cutoff 2^218. Maximum integral cost {cost}.")
    print(f"{len(main)} rational endpoint checks. Minimum margin {float(min(main)):.9f} > 1/1000.")
    print(f"Earlier rows at 2^50: three exact endpoints, minimum margin {float(min(mixed)):.9f} > 1/1000.")
    print(f"All {graphs:,} tripartite graphs on the three test lists passed the padded draw count.")
