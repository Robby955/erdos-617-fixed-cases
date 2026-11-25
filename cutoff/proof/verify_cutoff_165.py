"""Exact certificates for cutoff-165.md. Run with Python 3.10 or later."""

from fractions import Fraction as F
from itertools import combinations, product

from verify_cutoff_190 import (
    C, FILL, INV, LAMBDA, M, P_MAX, STAR, check_auxiliary, log_bounds,
)

TAU = F(43, 100)
LENGTH = F(124, 125)
K = 2560
BOUNDS = [F(0), F(5, 8), F(3, 4), F(7, 8), F(1), F(9, 8),
          F(5, 4), F(11, 8), F(13, 8), F(2)]
# alpha and beta are in units of 1/4000.
BANDS = [(14, 676, 880), (15, 680, 884), (15, 680, 880),
         (15, 676, 878), (16, 680, 885), (16, 680, 880),
         (16, 680, 880), (16, 676, 872), (17, 680, 880)]


def width_margin(lo, hi, exponent, alpha, beta):
    corners = [(F(0), F(0)), (P_MAX, F(0)),
               (P_MAX, (1-P_MAX/4)/TAU), (F(0), 1/TAU)]
    # The variance term and the untrimmed pair penalty pay all chosen surplus.
    assert 4*(1-2*TAU)*(1/(2*LENGTH**2)+beta/alpha) >= 1
    candidates = corners.copy()
    for (p,t), (q,u) in zip(corners, corners[1:]+corners[:1]):
        y, v = 2-p/2-TAU*t, 2-q/2-TAU*u
        for level in (lo, hi):
            if min(y,v) < level < max(y,v):
                a = (level-y)/(v-y)
                candidates.append((p+a*(q-p), t+a*(u-t)))
        z = 1-p/4-TAU*t
        pairs = (F(1,2)+p+t+z)/(1-2*TAU)
        deficit = F(1,2)+p+t+2*TAU*z/LENGTH**2
        assert deficit < F(37,10)
        assert 729+pairs+deficit/min(1-LENGTH,1-2*TAU) < K/2
    assert F(37,10)+F(1,2)+P_MAX < 7 and 2*F(37,10)<9
    costs = [F(3,4)+y/alpha+(p+t+z/LENGTH**2)/beta
             for p,t in candidates for y,z in [(2-p/2-TAU*t,1-p/4-TAU*t)]
             if lo <= y <= hi]
    log2_lo, _ = log_bounds(F(2))
    _, log_k = log_bounds(F(K, 2048))
    margin = (F(165-exponent,4)-11)*log2_lo-log_k-max(costs)
    assert margin > F(1,400)
    return margin


def sampling(A, X, B, R, cut_mass):
    rho, eta = FILL/K, 1/(R*FILL**2)
    gamma, g, kappa = A/FILL, X/FILL, B/FILL
    x = g*rho
    j = (1+80*rho)/(1-x)
    assert 1/(R*K*K) < INV and 4*61**2*A/K < 1
    assert 1-x-FILL-F(3,4) > F(1,61)
    assert (g+44*gamma)*rho < F(1,256)
    assert F(1,44)+x+F(1,256)+STAR < F(1,32)
    assert 2*j*x < F(1,512) and 2*x/(1-x) < F(1,1000)
    assert 80*rho < 1 and 40*(1-rho)-1-g > 37 and x+INV < F(1,2)
    nmax = F(513,512)*gamma+F(1,256)+x+STAR
    a = min(F(5,2),F(249,250)/nmax)
    assert a > F(4,3) and a*kappa < 2
    k = F(4,3)/(a-F(4,3))
    b = j*(1+1/k)
    assert a*nmax+2*b*x < 1
    assert k*(a-F(4,3)) == F(4,3) and k*(b-j) == j
    assert k*((b/j)**2-1) >= 1
    V = a*(F(513,512)*cut_mass/FILL+F(7,K))+9*b/K
    base = k*eta*(((1+V)**2+V/K)/2+F(1,2*K))

    def repair(W,l):
        return k*(b*W+l)**2/(2-a*kappa)+base

    first = 8*repair(2*kappa,0)+2*eta
    assert first*rho**2 < min(C/128,F(1,16))
    W = (1/(1-x)+LAMBDA*g/37)*kappa+g*first*rho/37
    second = 8*repair(W,0)+2*eta
    assert second*rho**2 < min(C/128,F(1,16))
    assert C-LAMBDA*kappa*rho > 0
    margins = []
    for l in (F(0), LAMBDA*kappa):
        eps = repair(W,l)+g*l+l*l/2+eta*(F(1,2)+F(1,2*K))
        assert 0 < eps < 1
        margin = ((1-eps)*(C-LAMBDA*kappa*rho)+l-LAMBDA*kappa
                  -second*rho-1/(FILL*R*K**2))
        assert margin > F(1,2000), (A,X,B,R,margin)
        margins.append(margin)
    return margins


def floor_total(r):
    """Sum floor(r/(5j)), 4 <= j <= M+3, by runs of identical quotients."""
    n = r//5
    end = min(n,M+3)
    j, total = 4, 0
    while j <= end:
        value = n//j
        last = min(end,n//value)
        total += (last-j+1)*value
        j = last+1
    return total


def floor_certificate(start, stop, denominator, lower):
    count = 0
    while start < stop:
        next_start = min(stop, start+max(1,start//denominator))
        # The unnormalized floor sum increases. This bounds every integer in the block.
        assert F(floor_total(start),next_start-1) > lower
        start = next_start
        count += 1
    return count


def fixed_rows():
    tau, L = F(47,100), F(19,20)
    c = 1-1/(4*tau)
    inv = F(1,M)
    base = F(1,4)-F(1,256)
    small = sum(min(STAR, (F(1,100*j)+inv**2)/(base-F(1,5*j)-inv))
                for j in range(4,256))
    log2,log2_hi = log_bounds(F(2))
    # H_tail <= log((M+3)/255) <= 16 log(2) + log((M+3)/(255*2^16)).
    _, last_log = log_bounds(F(M+3,255*2**16))
    tail = ((16*log2_hi+last_log)/100+inv)/(base-F(1,1280)-inv)
    assert base-F(1,20)-inv > 0 and small+tail < F(609,1000)
    star_cap = F(609,1000)
    top = F(1,2)+1/tau+c*star_cap
    penalty = 1-2*tau-2*c*STAR
    z_cost = 1/tau-2*tau/L**2
    assert c*STAR < 1-L and L > 2*tau and penalty > 0
    assert z_cost > (1-2*tau-c*STAR)/L**2
    assert top < F(2913,1000) and top-5*penalty < F(8,3)
    # At most five short lists, using q <= 4 and discarding both other losses.
    assert top+4*c*STAR-6*(1-L-c*STAR) < F(8,3)
    assert star_cap+9*STAR < F(16,25)
    # Squared deficits, including ceiling errors. H <= 16 for j=4,...,M+3.
    assert (M+3)**2 < 9*2**45 and F(45,2)*log2_hi < 16
    square_mass = F(1,75)+F(32,5)*inv+inv
    assert square_mass < F(14,1000)
    localized = 1/tau+c*F(16,25)+(F(14,1000)+top/256)/tau
    assert F(8,3)-localized > F(9,50)
    assert sum(F(1,5*j)+inv for j in range(4,9)) < F(9,50)
    assert all(floor_total(r)==sum(r//(5*j) for j in range(4,r//5+1))
               for r in range(1,3000))
    blocks = floor_certificate(M,19_000_000,1800,F(8,3))
    ranges = [(19_000_000,25_000_000,4,F(269,100)),
              (25_000_000,33_000_000,3,F(2745,1000)),
              (33_000_000,40_000_000,2,F(280,100)),
              (40_000_000,43_000_000,2,F(284,100)),
              (43_000_000,8*M,1,F(2856,1000))]
    for start,stop,q_limit,lower in ranges:
        assert top-q_limit*penalty < lower
        blocks += floor_certificate(start,stop,1800,lower)
    for lower,count in [(F(280,100),14),(F(284,100),18)]:
        assert sum(F(1,5*j)+inv for j in range(4,4+count-1)) < lower-localized
    # With q=1 and D>2.840 there is exactly one short list.
    late = F(284,100)
    assert top+c*STAR-2*(1-L-c*STAR) < late
    assert top+c*STAR-z_cost*L**2 < late  # no short list would require Z >= L^2
    z_cap = (top+2*c*STAR-(1-L)-late)/z_cost
    assert 0 < z_cap/L < F(13,500)
    # For the infinite tail bound sum_{j=256}^{M+3} 1/j >= log((M+4)/256).
    assert (sum(F(1,j) for j in range(4,256))+16*log2)/5-F(1,8)>F(2856,1000)
    return blocks


def arc_checks():
    """Enumerate grid arcs; check simultaneous filling and actual pair probabilities."""
    cases = 0
    for circumference,baseline in ((6,1),(7,2),(9,2)):
        for loads in product(range(circumference+1), repeat=3):
            lengths = [max(0,t-baseline) for t in loads]
            occupied = [[sum(1 << ((start+k) % circumference) for k in range(length))
                         for start in range(circumference)] for length in lengths]
            for i,j in combinations(range(3),2):
                collisions = sum(bool(occupied[i][0]&other) for other in occupied[j])
                assert collisions <= lengths[i]+lengths[j]
            for b,c in product(range(circumference), repeat=2):
                a1,a2,a3 = occupied[0][0],occupied[1][b],occupied[2][c]
                if not (a1&a2 or a1&a3 or a2&a3):
                    assert sum(loads) <= circumference+3*baseline
            cases += 1
    return cases


if __name__ == '__main__':
    blocks = fixed_rows()
    check_auxiliary(False)
    widths, margins = [], []
    for (lo,hi),(e,ai,bi) in zip(zip(BOUNDS,BOUNDS[1:]),BANDS):
        alpha,beta = F(ai,4000),F(bi,4000)
        widths.append(width_margin(lo,hi,e,alpha,beta))
        for i in range(96):
            left,right = F(i,96),F(i+1,96)
            peak = max(left,min(F(1,2),right))
            margins += sampling(alpha*right,2*beta*right,
                                4*beta**2*peak*(1-peak),F(2**e),hi)
    print(f'Fixed rows excluded from 43,000,000. Checked {blocks:,} whole intervals and the infinite tail.')
    print('Lower band requires 1 to 4 chosen pairs, at most 5 short lists and more than 9r/50 lost neighbors.')
    print(f'General cutoff 2^165. {len(margins):,} exact endpoints. Minimum margin {float(min(margins)):.9f}.')
    print(f'Minimum logarithmic width margin {float(min(widths)):.9f}. {arc_checks():,} arc triples passed.')
