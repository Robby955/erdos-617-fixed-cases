"""Exact constants and finite checks for cutoff-289.md. Requires Python 3.10+."""

from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial

K = 1800
R = 2**19
FILL = F(7, 30)
ALPHA = F(29, 250)
BETA = F(19, 125)
GAMMA = ALPHA / FILL
G = 2 * BETA / FILL
KAPPA = BETA**2 / FILL
RHO = FILL / K
ETA = 1 / (R * FILL**2)
LAMBDA = F(501, 1000)
SHORTAGE = F(13, 200)
U_LOW = F(41, 40)
J = F(1011, 1000)
ZERO = F(0)


def width_and_shortage() -> None:
    assert 1777 + 1 <= K
    assert 1/BETA > 1/(4*ALPHA)
    assert F(256, 225) == F(2048, K)
    log_two_lower = 2 * sum(F(1, (2*i+1) * 3**(2*i+1)) for i in range(5))
    assert log_two_lower > F(6931, 10000)
    assert 1 + 1/ALPHA + F(9, 2)/BETA < F(113, 2)*log_two_lower + F(31, 256)
    assert F(135, 2)-11 == F(113, 2) and R * 2**270 == 2**289
    assert 4*61**2*ALPHA/K < 1
    assert F(1, R*K*K) < F(1, 2**20)
    assert 1-G*RHO-FILL > F(1, 61)
    assert 1-G*RHO-F(3, 4)-FILL > F(1, 61)
    assert F(1, 40)+G*RHO+F(1, 256) < F(1, 32)
    assert (G+40*GAMMA)*RHO < F(1, 256)

    inv_r = F(1, 2**20)
    delta, tau, theta, t = F(43, 500), F(27, 250), F(93, 250), F(133, 500)
    xi = SHORTAGE**2 + inv_r
    raw = SHORTAGE + xi/(2*(1-inv_r))
    squared = (2+F(1, K-1))*SHORTAGE**2 + 3*inv_r
    assert raw < F(6712, 100000) < tau
    assert raw+(squared-raw**2)/(2*tau) < delta
    assert 1-delta-2*tau > F(1, 2) and 100*xi < 1
    assert 1-delta-theta-4*tau > F(1, 10) and 1-delta-2*theta > F(1, 10)
    assert F(255, 256)-theta-FILL-F(4, 32) > F(1, 61)
    assert F(255, 256)-2*theta-FILL > F(1, 61)
    assert theta*(t-inv_r) > (1-t+inv_r)*delta+t**2/2+t*inv_r/2
    assert theta-delta-t-inv_r > 0
    assert (1-delta-theta)*(theta-delta-t-inv_r) > delta**2+inv_r
    penalty = (t+inv_r)/2
    for count, size in ((3, F(153, 1000)), (4, F(43, 200))):
        assert comb(count, 2)*(inv_r+delta**2) < size**2
        assert 1-delta-size+(count-1)*theta-count*penalty > 1
    assert 5*(theta-penalty) > 1


def sender_credit() -> None:
    x = G*RHO
    assert x + F(1, 2**20) < F(1, 2)
    assert 2*x/(1-x) < F(1, 1000)
    assert 80*RHO < 1 and 40*(1-RHO)-1-G > 37
    assert (37/G)*(U_LOW-1/(1-x)) > LAMBDA
    assert (1+80*RHO)/(1-x) < J
    assert 2*J*x < F(1, 512)
    assert 9*J < 10 and J**2*81/2 < 243
    assert SHORTAGE > LAMBDA*KAPPA*RHO
    for rho in (RHO, RHO/10, RHO/2**40):
        for q in (F(1, 2), F(2, 3), F(9, 10), F(999, 1000), F(1)):
            for deficit in (ZERO, G*rho/2, G*rho):
                v = (1-q)*(1+80*rho*q)
                residual = (1-deficit)*q+deficit-(1-v+rho*v+2*deficit*(1-q))
                assert residual == (1-q)*(rho*(80*q*(1-rho)-1)-deficit)
                assert residual >= 37*rho*(1-q)


def check_endpoints() -> list[F]:
    a, b, young, multiplier = F(199, 100), F(1217, 1000), F(19, 100), F(99, 20)
    assert a*(F(513, 512)*GAMMA+F(1, 256)+G*RHO)+2*b*G*RHO < 1
    assert multiplier*(a-F(4, 3)-a*a*KAPPA/2-young) > F(4, 3)
    assert multiplier*(b-J) > J
    count = 2*F(513, 512)/FILL+F(5, K)
    total = a*count+9*b/K
    binomial = ((1+total)**2+total/K)/2
    cost_s = multiplier*(binomial+(10*count*a+F(1, 2))/K+F(243, K*K))+F(243, K*K)

    def repair(bound: F, theta: F) -> F:
        chi = J**2*bound**2/2
        t = b*bound+theta/KAPPA
        cost_w = multiplier*(chi+t**2/2+(a*(t+J*bound))**2*KAPPA/(4*young))+chi
        return cost_w*KAPPA**2+cost_s*ETA

    margins = []
    for bound, row_cost, theta, eps_max, gap_min in (
        (U_LOW, LAMBDA, ZERO, F(229, 1000), F(3, 10000)),
        (U_LOW, LAMBDA, LAMBDA*KAPPA, F(395, 1000), F(39, 1000)),
        (F(2), ZERO, ZERO, F(789, 1000), F(12, 1000)),
    ):
        z = 8*repair(bound, ZERO)+2*ETA
        assert z*RHO**2 < min(SHORTAGE/128, F(1, 16))
        eps = repair(bound, theta)+G*theta+theta**2/2+ETA*(F(1, 2)+F(1, 2*K))
        assert 0 < eps < eps_max < 1
        gap = (1-eps)*(SHORTAGE-row_cost*KAPPA*RHO)+theta-row_cost*KAPPA-z*RHO-1/(FILL*R*K*K)
        assert gap > gap_min
        margins.append(gap)
    return margins


def check_foreign_edges_and_harmonic_tail() -> F:
    s = 4096
    rho = FILL/s
    small = F(1, 32768)
    order = 2**44
    assert 1777+512*F(9, 2) <= s-1
    assert F((s-1)**2, order) < F(1, 2**20)
    assert 4*61**2*small < 1
    assert 1-F(1, 512)-40*small >= F(255, 256)
    assert F(1, 40)+F(1, 512)+F(1, 256) < F(1, 32)
    assert 1-F(1, 512)-FILL > F(1, 61)
    assert 1-F(1, order)-F(1, 512)-F(1, 512) > F(1, 2)
    lower = (SHORTAGE-F(9, 1024))/(2+1/rho)
    assert F(1, 320000) < lower < small

    q = F(11, 80)
    cut = 8192
    max_width = cut+1777+1
    assert max_width == 9970
    # ln 2 < 0.7 follows from exp(0.7)>2 using its first five terms.
    log_upper = F(7, 10)
    assert sum(log_upper**i/factorial(i) for i in range(5)) > 2
    assert 1+44*log_upper < 32
    assert max_width*(q**2/cut+(64*q+1)/order) < BETA**2
    assert max_width*(q/(cut+1)+F(1, order)) < 2*BETA
    assert q/71+F(1, order) < F(1, 512)
    assert (s-1)-1777-70 == 2248
    mass_upper = 1+36*log_upper
    pruning = F(39, 10)
    assert F(4, 25)*mass_upper < pruning+F(1, 2)
    assert mass_upper/100 < 2-pruning/4
    assert F(36-12, 100)*F(6931, 10000) > F(1, 320000)
    assert F(2**32+1, 2**36+1) < F(1, 15)
    assert F(4, 25)**2*F(14, 15) > BETA**2
    return lower


def check_pivot_graphs(order: int) -> int:
    """Check the local payment and its clique form for every pivot tie on labeled graphs."""
    pairs = tuple(combinations(range(order), 2))
    all_vertices = (1 << order)-1
    for mask in range(1 << len(pairs)):
        neighbors = [0]*order
        for bit, (i, j) in enumerate(pairs):
            if mask & (1 << bit):
                neighbors[i] |= 1 << j
                neighbors[j] |= 1 << i
        degree = min(row.bit_count() for row in neighbors)
        for pivot, row in enumerate(neighbors):
            if row.bit_count() != degree:
                continue
            part = row | (1 << pivot)
            later = all_vertices ^ part
            vertices = [i for i in range(order) if part & (1 << i)]
            missing = sum(not (neighbors[i] & (1 << j)) for i, j in combinations(vertices, 2))
            for i in vertices:
                assert len(vertices)-1-(neighbors[i]&part).bit_count() <= (neighbors[i]&later).bit_count()
            core = part
            while core:
                clique = all((neighbors[i]&core).bit_count() == core.bit_count()-1
                             for i in vertices if core & (1 << i))
                if clique:
                    cross = sum((neighbors[i]&later).bit_count() for i in vertices if core & (1 << i))
                    assert missing <= cross+comb((part^core).bit_count(), 2)
                core = (core-1)&part
    return 1 << len(pairs)


if __name__ == "__main__":
    width_and_shortage()
    sender_credit()
    margins = check_endpoints()
    lower = check_foreign_edges_and_harmonic_tail()
    graphs = sum(check_pivot_graphs(n) for n in range(1, 7))
    print("Cutoff 2^289. All three exact endpoint margins exceed 3/10000.")
    print(f"Smallest normalized margin = {min(margins)}.")
    print(f"Retained foreign edge incidence fraction > {lower} > 1/320000.")
    print(f"Checked the minimum-degree row inequalities on all {graphs:,} labeled graphs of orders 1–6.")
