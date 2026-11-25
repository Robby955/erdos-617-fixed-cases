"""Exact constants and finite regression checks for cutoff-320.md (Python 3.10+)."""

from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial


MIN_WIDTH = 2160
SIZE_FACTOR = 2**19
FILL = F(7, 30)
ALPHA = F(8, 75)
BETA = F(33, 250)
GAMMA = ALPHA / FILL
DEFICIT = 2 * BETA / FILL
KAPPA = BETA**2 / FILL
RHO = FILL / MIN_WIDTH
ROW_COST = F(501, 1000)
SHORTAGE = F(121, 2000)
REP = F(1001, 1000)


def check_width_and_lists() -> None:
    assert 1649 + 128 + 1 <= MIN_WIDTH
    assert 1 / BETA > 1 / (4 * ALPHA)
    assert F(MIN_WIDTH, 2**11) == F(135, 128)
    log_two_lower = 2 * sum(F(1, (2*i+1)*3**(2*i+1)) for i in range(5))
    assert log_two_lower > F(6931, 10000)
    cost = 1 + 1/ALPHA + F(9, 2)/BETA
    assert cost < F(257, 4)*F(6931, 10000) - F(7, 128)
    assert 301 - 4*11 == 257 and SIZE_FACTOR * 2**301 == 2**320
    q = F(11, 80)
    log_two_upper = log_two_lower + F(2, 11*3**11)*F(9, 8)
    assert log_two_upper < F(7, 10)
    assert q*(1 + 44*log_two_upper) < F(39, 10) + F(1, 2)
    assert F(2**40+1, 2**44+1) < F(1, 15) and q*q*F(14, 15) > BETA**2
    # At a_i=max(y_i,alpha*x_i/(2*beta)), either branch pays the row integral.
    for x, cut in product((F(i, 19) for i in range(20)), repeat=2):
        weight = max(cut, ALPHA*x/(2*BETA))
        if weight:
            assert weight/ALPHA + ALPHA*x*x/(4*BETA**2*weight) <= cut/ALPHA + x/BETA
    exp_one_upper = sum(F(1, factorial(i)) for i in range(8)) + F(9, 8*factorial(8))
    assert exp_one_upper < F(2719, 1000)
    assert F(2719, 1000)*61**2*(2*GAMMA*RHO + F(1, 2**40)) < 1
    assert 1 - DEFICIT*RHO - F(3, 4) - FILL > F(1, 61)


def check_shortage() -> None:
    inv_r = F(1, 2**20)
    delta, tau, theta, t = F(43, 500), F(9, 100), F(93, 250), F(133, 500)
    xi = SHORTAGE**2 + F(1, 2**40)
    assert MIN_WIDTH - 1 >= 2048
    assert F(1, SIZE_FACTOR*MIN_WIDTH**2) < F(1, 2**40)
    assert (2 + F(1, MIN_WIDTH-1))*SHORTAGE**2 + F(3, 2**40) < delta**2 < tau**2
    assert 1-delta-2*tau > F(1, 2) and 100*xi < 1
    assert F(1, 40) + DEFICIT*RHO + F(1, 256) < F(1, 32)
    assert (DEFICIT + 40*GAMMA)*RHO < F(1, 256)
    assert 1-delta-theta-4*tau > F(1, 10) and 1-delta-2*theta > F(1, 10)
    assert F(255, 256)-theta-FILL-F(4, 32) > F(1, 61)
    assert F(255, 256)-2*theta-FILL > F(1, 61)
    assert theta*(t-inv_r) > (1-t+inv_r)*delta + t**2/2 + t*inv_r/2
    assert theta-delta-t-inv_r > 0
    assert (1-delta-theta)*(theta-delta-t-inv_r) > delta**2+inv_r
    penalty = (t+inv_r)/2
    for j, list_size in ((3, F(153, 1000)), (4, F(43, 200))):
        assert comb(j, 2)*(inv_r+delta**2) < list_size**2
        assert 1-delta-list_size+(j-1)*theta-j*penalty > 1
    assert 5*(theta-penalty) > 1


def check_row_charges() -> int:
    max_x = DEFICIT*RHO
    assert max_x + F(1, 2**20) < F(1, 2)
    assert 3*(1-RHO)-1 > DEFICIT and 6*RHO < 1
    assert F(1, 2) + 2*max_x/(1-max_x) < ROW_COST
    for q in (F(1, 2), F(3, 5), F(11, 12), F(999, 1000), F(1)):
        for rho in (RHO, RHO/10, RHO/100):
            x = DEFICIT*rho
            v = (1-q)*(1+6*rho*q)
            assert (1-x)*q+x >= 1-v+rho*v+2*x*(1-q)
    # Use the exact cut budget in (4), including the endpoints b=0,d,2d.
    tested = 0
    r = 2**18
    for d in range(22):
        assert F(d, r) < max_x
        for b in range(2*d+1):
            degree_budget = (r-1)*d + comb(b+1, 2) - b*d
            assert degree_budget <= r*d
            surplus = max(0, 2*d*(b-F(degree_budget, r-d)))
            for v0 in (F(0), F(1, 4), F(d, 2), F(d), F(3*d, 2), F(2*d+1)):
                assert F(b*b, 2) + (b-d)*v0-surplus <= ROW_COST*d*d + v0*v0/2
                tested += 1
    return tested


def check_same_row_conflicts() -> int:
    # Integrate actual draws, marks, and hits on two exterior points. In this
    # finite check the row is full and the retry marginal is <= REP/r.
    r = 5
    strong = ({0, 1, 2}, {1, 2, 3, 4}, {0, 2, 4})
    outside = ({0, 3}, {1, 4})
    rng = range(r)
    tested = 0
    for p, outside_prob in product((F(0), F(1, 3), F(1)), (F(1, 2), F(1))):
        laws = []
        t = F(0)
        same_cut = F(0)
        for neighbors in strong:
            marginal = p*(1+6*RHO*F(len(neighbors), r))/r
            assert marginal <= REP/r
            law = [(i, marginal) for i in rng if i not in neighbors]
            marked = sum(mass for _, mass in law)
            t += marked
            same_cut += marked*len(neighbors)
            laws.append([(None, 1-marked), *law])
        cost = F(0)
        for draws in product(*laws):
            reps = [i for i, _ in draws if i is not None]
            probability = F(1)
            for _, mass in draws:
                probability *= mass
            for active, ext_mass in ((False, 1-outside_prob), (True, outside_prob)):
                others = outside if active else outside[:1]
                hits = sum(i in neighbors for i in reps for neighbors in others)
                cost += probability*ext_mass*(comb(len(reps), 2)+hits)
                tested += 1
        exterior_cut = len(outside[0]) + outside_prob*len(outside[1])
        assert same_cut >= r*t/2 and t <= len(strong)
        assert cost <= REP*len(strong)*(exterior_cut+same_cut)/r
    return tested


def check_final_bounds() -> F:
    a, b, young = F(54, 25), F(13, 10), F(13, 50)
    chi, multiplier = F(201, 100), F(17, 5)
    assert (1+6*RHO)/(1-DEFICIT*RHO) < REP
    assert 2*REP*DEFICIT*RHO < F(1, 512)
    assert 9*REP < 10 and 2*REP < chi
    assert 2*REP**2 < chi and REP**2*81/2 < 243
    count = F(8591, 1000)
    assert 2*F(513, 512)/FILL + F(5, MIN_WIDTH) <= count
    assert a*(F(513, 512)*GAMMA+F(1, 256)+DEFICIT*RHO)+2*b*DEFICIT*RHO < 1
    total = a*count + 9*b/MIN_WIDTH
    binomial = ((1+total)**2+total/MIN_WIDTH)/2
    t = 2*b + ROW_COST
    assert multiplier*(a-F(4, 3)-a*a*KAPPA/2-young) >= F(4, 3)
    assert multiplier*(b-REP) >= REP
    assert multiplier*(chi+t*t/2+a*a*(t+chi)**2*KAPPA/(4*young))+chi < 55
    assert multiplier*(binomial+(10*count*a+F(1, 2))/MIN_WIDTH
                       +F(243, MIN_WIDTH**2))+F(243, MIN_WIDTH**2) < 651
    eta = 1/(SIZE_FACTOR*FILL**2)
    repair = F(33, 100)
    assert 55*KAPPA**2+651*eta < repair
    assert repair + ROW_COST*KAPPA*DEFICIT + (ROW_COST*KAPPA)**2/2 + eta*(F(1, 2)+F(1, 2*MIN_WIDTH)) < F(3, 8)
    assert 8*repair+2*eta < F(8, 3)
    assert F(8, 3)*RHO**2 < min(SHORTAGE/128, F(1, 16))
    m_floor = SHORTAGE-ROW_COST*KAPPA*RHO
    margin = (1-F(3, 8))*m_floor - ROW_COST*KAPPA - F(8, 3)*RHO - 1/(FILL*SIZE_FACTOR*MIN_WIDTH**2)
    assert margin > F(1, 10000)
    return margin


if __name__ == "__main__":
    check_width_and_lists()
    check_shortage()
    rows = check_row_charges()
    collisions = check_same_row_conflicts()
    margin = check_final_bounds()
    print("Width below 2^(301/4), size factor 2^19, sufficient draft order 2^320.")
    print(f"Exact normalized contradiction margin {margin} > 1/10000.")
    print(f"{rows:,} row-charge cases and {collisions:,} same-row mark and draw outcomes checked.")
