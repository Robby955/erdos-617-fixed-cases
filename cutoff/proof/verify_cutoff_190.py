"""Exact arithmetic and edge-count checks for cutoff-190.md (Python 3.10+)."""

from fractions import Fraction as F
from itertools import combinations, product

ONE = F(1)
INV = F(1, 2**20)
M = 2**24
FILL = F(7, 30)
C = F(1, 8)
LAMBDA = F(501, 1000)
STAR = F(5, 1464)
TAU = F(99, 200)
LENGTH = F(497, 500)
P_MAX = F(125, 61)
BANDS = (
    (F(0), F(5, 8), 2400, 15, F(155, 1000), F(200, 1000)),
    (F(5, 8), F(7, 8), 2600, 16, F(165, 1000), F(198, 1000)),
    (F(7, 8), F(9, 8), 2600, 18, F(170, 1000), F(200, 1000)),
    (F(9, 8), F(11, 8), 2600, 18, F(170, 1000), F(198, 1000)),
    (F(11, 8), F(13, 8), 2600, 18, F(170, 1000), F(198, 1000)),
    (F(13, 8), F(2), 2600, 19, F(170, 1000), F(198, 1000)),
)


def cutoff_budgets(p, t):
    z = 1-p/4-TAU*t
    return F(1, 2)+p+t+2*TAU*z/LENGTH**2, 2-p/2-TAU*t


def log_bounds(x):
    """Enclose log(x) for 1 <= x <= 2 by the positive atanh series."""
    assert 1 <= x <= 2
    u = (x-1)/(x+1)
    lo = 2*sum(u**(2*i+1)/(2*i+1) for i in range(12))
    return lo, lo+2*u**25/(25*(1-u*u))


def check_width(lo, hi, K, exponent, alpha, beta):
    corners = [(F(0), F(0)), (P_MAX, F(0)),
               (P_MAX, (1-P_MAX/4)/TAU), (F(0), 1/TAU)]
    candidates = corners.copy()
    for (p, t), (q, u) in zip(corners, corners[1:]+corners[:1]):
        y, v = cutoff_budgets(p, t)[1], cutoff_budgets(q, u)[1]
        for level in (lo, hi):
            if min(y,v) < level < max(y,v):
                a = (level-y)/(v-y)
                candidates.append((p+a*(q-p), t+a*(u-t)))
    for p, t in corners:
        z = 1-p/4-TAU*t
        q = (F(1,2)+p+t+z)/(1-2*TAU)
        dx, _ = cutoff_budgets(p,t)
        assert dx < F(18,5)
        assert 729+q+dx/min(1-2*TAU, 1-LENGTH) < K
    costs = [1+dy/alpha+dx/beta for p,t in candidates
             for dx,dy in [cutoff_budgets(p,t)] if lo <= dy <= hi]
    log2, _ = log_bounds(F(2))
    _, log_k = log_bounds(F(K,2048))
    assert max(costs) < (F(190-exponent,4)-11)*log2-log_k
    return max(costs)


def check_auxiliary(pure):
    if pure:
        xi = F(100,3199)
        total_raw = xi/(2*(1-INV))
        moment = 2*xi+INV
        tau, theta, price = F(216,1000), F(406,1000), F(77,100)
    else:
        xi = C*C+INV
        total_raw = C+xi/(2*(1-INV))
        moment = (2+F(1,799))*C*C+3*INV
        tau, theta, price = F(206,1000), F(411,1000), F(72,100)
    ordinary_theta, od, q = F(369,1000), F(1,256), F(1,10000)
    delta = total_raw+(moment-total_raw**2)/(2*tau)
    total = total_raw+xi/tau
    w = 1-2*theta
    assert total_raw < tau and w > delta
    assert w*w+(w-total_raw)**2 > moment
    assert w > total_raw
    assert 1-theta-delta-2*tau > 0
    assert (1-theta-total_raw-2*tau)*(1-theta-total_raw) > xi
    assert 1-delta-2*tau > 0 and (1-delta-2*tau)**2 > xi
    assert 1-od-2*ordinary_theta-FILL > F(1,61)
    assert 1-od-ordinary_theta-FILL-F(2,32) > F(1,61)
    types = [(theta,delta)] if pure else [(theta,delta),(ordinary_theta,od)]
    for th,d in types:
        assert 2*(th-price*d-q)*(1+price) > 1
        assert 2*(th-price*d-q)*q > (th+d+F(1,2))*INV
        assert 2*((1+price)*d+q) < 1 and th-price*d-q > 0
    for left,right in product(types, repeat=2):
        th, d = left
        _, e = right
        summed = min(d+e, total) if left[0] == right[0] == theta else d+e
        cap = min(d*e, summed**2/4)
        assert th-e-price*summed-2*q > 0
        assert (1-d-th)*(th-e-price*summed-2*q) > cap+INV
    for triple in product(types, repeat=3):
        ordinary = sum(th != theta for th,_ in triple)
        summed = ordinary*od+min(total,(3-ordinary)*delta)
        assert sum(th for th,_ in triple)-price*summed-3*q > 1


def sampling(A, X, B, K, R, cut_mass):
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
    a = min(F(7,2),F(249,250)/nmax)
    den = a-F(4,3)-a*a*kappa/2
    assert den > 0
    Y = den/2
    k = F(4,3)/(den-Y)
    b = j*(1+1/k)
    assert a*nmax+2*b*x < 1
    assert k*(den-Y) == F(4,3) and k*(b-j) == j
    assert k*((b/j)**2-1) >= 1
    total_n = F(513,512)*cut_mass/FILL+F(7,K)
    V = a*total_n+9*b/K
    base = k*(((1+V)**2+V/K)/2+F(1,2*K))*eta

    def repair(W,l):
        return k*(b*W+l)**2*(F(1,2)+a*a*kappa/(4*Y))+base

    first = 8*repair(2*kappa,0)+2*eta
    assert first*rho**2 < min(C/128,F(1,16))
    W = (1/(1-x)+LAMBDA*g/37)*kappa+g*first*rho/37
    Z = 8*repair(W,0)+2*eta
    assert Z*rho**2 < min(C/128,F(1,16))
    assert C-LAMBDA*kappa*rho > 0
    values = []
    for l in (F(0), LAMBDA*kappa):
        eps = repair(W,l)+g*l+l*l/2+eta*(F(1,2)+F(1,2*K))
        assert 0 < eps < 1
        margin = ((1-eps)*(C-LAMBDA*kappa*rho)+l-LAMBDA*kappa
                  -Z*rho-1/(FILL*R*K**2))
        assert margin > F(1,2000), (K,R,A,X,B,margin)
        values.append(margin)
    return values


def profile_checks():
    log2, log2_hi = log_bounds(F(2))
    assert (M+3)**2 < 9*2**45  # (M+3)/3 < 2^(45/2)
    H = F(45,2)*log2_hi
    inv = F(1,M)
    y = H/100+inv
    xy = F(1,1500)+H*inv/100+H*inv**2/5+inv**2
    assert F(1,4)-F(1,20)-inv > F(4,21)
    assert 4*y+21*xy < F(16,25)
    tau, L = F(499,1000), F(999,1000)
    max_pre = F(1,2)+1/tau
    assert 1-2*tau*tau/L**2 > 0
    assert 728+32+max_pre/(1-2*tau)+max_pre/min(1-2*tau,1-L) < 4600
    d_upper = max_pre+(1-1/(4*tau)+tau/(2*L**2))*F(16,25)
    assert d_upper < F(2984,1000)
    lower = (sum(ONE/j for j in range(4,256))+16*log2)/5
    assert F(2**27,5*(M+4)) > F(4,3)
    assert lower-F(252,2**27)-F(2*(M+4),3*2**27) > d_upper
    assert 10+32*(3+inv) < 110
    assert F(19,5)*log2-F(1,8) > F(3,2)+F(16,25)
    assert 1-110*inv+F(19,5)*log2-F(1,4) > F(5,2)+F(16,25)
    assert F((M+1988)**2,2**53) < F(100,3199)


def colored_edge_check():
    """Check the discounted incidence bound for every cut graph on 2+2+2."""
    parts = ((0,1),(2,3),(4,5))
    owner = {v:i for i,row in enumerate(parts) for v in row}
    pairs = [(v,w) for v,w in combinations(range(6),2) if owner[v] != owner[w]]
    for mask in range(1 << len(pairs)):
        graph = {e for i,e in enumerate(pairs) if mask & (1 << i)}
        live = set(range(6))
        special = set()
        anchors = {i:set() for i in range(3)}
        for v in range(6):
            for i,row in enumerate(parts):
                edges = {tuple(sorted((v,w))) for w in row if w in live} & graph
                if i != owner[v] and len(edges) == 2:
                    special.update(edges)
                    anchors[i].add(v)
                    live.remove(v)
                    break
        other = set()
        for v in sorted(live):
            edges = {e for e in graph if v in e and set(e) <= live}
            if len(edges) >= 2:
                other.update(edges)
                live.remove(v)
        assert special.isdisjoint(other)
        counted = sum(len(set(e)&live) for e in graph-special)
        assert counted <= 2*len(graph)-2*len(special)-len(other)
        for v in live:
            assert sum(v in e for e in special) <= len(anchors[owner[v]])
    return 1 << len(pairs)


if __name__ == '__main__':
    assert STAR == F(1,1200)/F(61,250)
    assert F(18,5)+F(1,2)+P_MAX < 7
    check_auxiliary(False)
    check_auxiliary(True)
    profile_checks()
    margins = []
    for lo,hi,K,e,alpha,beta in BANDS:
        check_width(lo,hi,K,e,alpha,beta)
        for i in range(96):
            left,right = F(i,96),F(i+1,96)
            peak = max(left,min(F(1,2),right))
            margins += sampling(alpha*right,2*beta*right,
                                4*beta**2*peak*(1-peak),K,F(2**e),hi)
    count = colored_edge_check()
    print(f'General cutoff 2^190. {len(margins)} exact endpoint checks.')
    print(f'Minimum margin {float(min(margins)):.9f} > 1/2000.')
    print('Fixed rows at 2^53, same-color alternative at 2^27, color choice at 2^24.')
    print(f'All {count:,} tripartite edge patterns passed the discounted-incidence check.')
