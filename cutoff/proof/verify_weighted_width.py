"""Exact certificate for weighted-width.md. Requires Python 3.10+."""
from fractions import Fraction as F
from itertools import combinations, product

from verify_cutoff_190 import INV, LAMBDA, P_MAX, STAR, log_bounds

EXPONENT = 146
K, H, BINS = 1120, 41, 128
TAU = F(199, 400)
FILL, C = F(9, 40), F(3, 20)
ORD_DEF, ORD_DEG = F(1, 256), F(7, 50)

# Each row gives the upper endpoint (the lower one is the preceding endpoint),
# log2(R), 4000 alpha, and 4000 beta.
BANDS = [
    (F(1, 2), 14, 656, 924),
    (F(55, 100), 14, 656, 922),
    (F(68, 100), 14, 652, 916),
    (F(1), 15, 652, 916),
    (F(2), 17, 654, 918),
]


def width_margin(lo, hi, b, alpha, beta):
    """Clip the pruning trapezoid and bound its affine cost at every vertex."""
    d = 1-2*TAU
    assert 2*(1-INV)*beta >= alpha and TAU*beta <= alpha
    assert (d-F(1, 256))/(2*beta) >= F(2, K)
    assert 729 <= 3*K//4
    length = (1+2*TAU)/2
    assert (length-2*TAU)/INV > 1  # floor(length*r) > 2*tau*r
    corners = [(F(0), F(0)), (P_MAX, F(0)),
               (P_MAX, (1-P_MAX/4)/TAU), (F(0), 1/TAU)]
    max_extra = 0
    for p, t in corners:
        initial = F(1, 2)+p+t
        assert initial < F(37, 10)
        max_extra = max(max_extra, int(2*initial/d))
    assert F(37, 10)+F(1, 2)+P_MAX < 7 and 2*F(37, 10) < 9
    vertices = corners.copy()

    def incidence(p, t):
        return 2-p/2-TAU*t

    for (p, t), (q, u) in zip(corners, corners[1:]+corners[:1]):
        left, right = incidence(p, t), incidence(q, u)
        for level in (lo, hi):
            if min(left, right) < level < max(left, right):
                a = (level-left)/(right-left)
                vertices.append((p+a*(q-p), t+a*(u-t)))
    costs = []
    for p, t in vertices:
        y = incidence(p, t)
        if lo <= y <= hi:
            costs.append(y/alpha+(p+t)/beta)
    log2_lo, _ = log_bounds(F(2))
    _, log_k = log_bounds(F(K, 1024))
    assert 2**(EXPONENT-b) > (2*(K+2*max_extra))**4
    return (F(EXPONENT-b, 4)-10)*log2_lo-log_k+F(1, 4)-max(costs)


def previous_exponent_gap():
    """Exhibit one point where this sufficient width inequality fails at 2^145."""
    hi, b, ai, bi = BANDS[0]
    p = P_MAX
    y = 1-p/4
    t = y/TAU
    assert 0 < y < hi and (y, t) == (F(119, 244), F(11900, 12139))
    cost = y/F(ai, 4000)+(p+t)/F(bi, 4000)-F(1, 4)
    _, log2_hi = log_bounds(F(2))
    log_k_lo, _ = log_bounds(F(K, 1024))
    return cost-((F(EXPONENT-1-b, 4)-10)*log2_hi-log_k_lo)


def ordered_incidence_examples():
    """Check the discarded-incidence inequality on all labeled five-vertex graphs."""
    vertices = range(5)
    pairs = list(combinations(vertices, 2))
    cases = strict = 0
    for mask in range(1 << len(pairs)):
        edges = {edge for i, edge in enumerate(pairs) if mask & (1 << i)}
        neighbors = [{w for w in vertices if tuple(sorted((v, w))) in edges}
                     for v in vertices]
        remaining = set(vertices)
        rows, missing = [], []
        while remaining:
            # Minimum target degree is maximum degree in the residual complement.
            pivot = min(remaining, key=lambda v: (len(neighbors[v] & remaining), v))
            row = {pivot} | (neighbors[pivot] & remaining)
            later = remaining-row
            holes = sum(edge not in edges for edge in combinations(sorted(row), 2))
            assert sum(len(neighbors[v] & later) for v in row) >= 2*holes
            rows.append(row)
            missing.append(holes)
            remaining = later
        owner = {v: i for i, row in enumerate(rows) for v in row}
        crosses = {edge for edge in edges if owner[edge[0]] != owner[edge[1]]}
        for omitted in range(1 << len(rows)):
            dropped = {i for i in range(len(rows)) if omitted & (1 << i)}
            live, stars = set(vertices), set()
            first = second = 0
            for stage in (1, 2):
                while True:
                    for v in sorted(live):
                        if stage == 1:
                            dest = next((row for i, row in enumerate(rows)
                                         if i != owner[v] and i not in dropped
                                         and neighbors[v] & row & live), None)
                            if dest is None:
                                continue
                            stars.update(tuple(sorted((v, w))) for w in neighbors[v] & dest & live)
                            first += 1
                        else:
                            if len((neighbors[v] & live)-rows[owner[v]]) < 2:
                                continue
                            second += 1
                        live.remove(v)
                        break
                    else:
                        break
            kept = {v for v in live if owner[v] not in dropped}
            counted = sum(len(set(edge) & kept) for edge in crosses-stars)
            source_count = sum(owner[v] in dropped for v in set(vertices)-live)
            holes = sum(missing[i] for i in dropped)
            # Stage-one charge 1/2 at both ends, stage-two charge 3/2 at its source.
            baseline = 4*len(crosses)-2*first-3*second
            saving = 4*holes-3*source_count
            assert 2*counted <= baseline-saving
            strict += saving > 0
            cases += 1
    assert strict > 0
    return cases, strict


def check_fractional_pruning_overlap():
    """Replay both stages on 17 vertices, charging the ends of undirected edges."""
    r = 4
    row = (0,)*5 + (1,)*4 + (2,)*4 + (3,)*4
    cross = {(0, 5), (0, 6), (1, 9), (1, 13), (2, 5), (5, 14), (10, 15)}
    live = set(range(len(row)))
    recorded = set()
    payments = {}
    for source, destination in ((0, 1), (5, None), (1, None)):
        star = [edge for edge in cross if source in edge and set(edge) <= live]
        if destination is not None:
            assert 256*row.count(destination) <= 257*r
            star = [edge for edge in star if any(row[v] == destination for v in edge)]
            recorded.update(star)
            quota = F(r, 4)
        else:
            quota = TAU*r
        assert len(star) > quota
        for u, v in star:
            other = v if u == source else u
            assert (source, other) not in payments and (other, source) not in payments
            payments[source, other] = quota / len(star)
            if destination is not None:
                payments[other, source] = quota / len(star)
        live.remove(source)

    assert 256*row.count(0) > 257*r
    ends = {(v, u) for edge in cross for v, u in (edge, edge[::-1])}
    forward = {(v, u) for v, u in ends if row[v] == 0 and row[v] < row[u]}
    ordinary = {(v, u) for v, u in ends if v in live and row[v] != 0
                and tuple(sorted((v, u))) not in recorded}
    overlap = sum(payments.get(end, 0) for end in forward)
    assert (2, 5) in forward and (2, 5) not in payments
    assert payments[5, 2] == TAU*r / 2
    assert (6, 0) not in ordinary and payments[6, 0] == F(1, 2)
    assert (len(ends), len(ordinary), len(forward)) == (14, 5, 5)
    assert sum(payments.values()) == F(299, 50)
    assert overlap == F(299, 100)
    assert len(ordinary) + sum(payments.values()) + len(forward) <= len(ends) + overlap
    assert 2*TAU*r - overlap == F(99, 100)


def auxiliary_checks():
    """Prove all list, rounding and ordered attachment inequalities."""
    tau, theta_a, theta_o = F(43, 200), F(81, 200), F(369, 1000)
    price, q0 = F(77, 100), F(1, 10000)
    xi = C*C+INV
    moment = (1+F(1, 799))*C*C+3*INV
    raw = C+xi/(2*(1-INV))

    def deficit(j):
        if not j:
            return F(0)
        s = min(raw, j*tau/2)
        return s+(moment-s*s/j)/tau

    d = deficit(1)
    assert (1-d-2*tau)**2 > xi and 1-d-2*tau > 0
    w = 1-2*theta_a
    s = min(raw, 2*w/3)
    assert w > d and w*w-w*s+3*s*s/4 > moment
    w = 1-theta_a
    assert w-2*tau > d and w-raw > tau and ORD_DEG < tau
    assert 1-ORD_DEF-2*theta_o-FILL > F(1, H)
    assert 1-ORD_DEF-theta_o-FILL-2*ORD_DEG > F(1, H)
    types = ((theta_o, ORD_DEF), (theta_a, d))
    for theta, cap in types:
        a = price*cap+q0
        assert theta-a > 0 and 2*(cap+a) < 1
        assert 2*(theta-a)*(1+price) > 1
        assert 2*(theta-a)*q0 > (theta+cap+F(1, 2))*INV
    for left, right in product(range(2), repeat=2):
        j = left+right
        theta, d1 = types[left]
        d2 = types[right][1]
        total = deficit(j)+(2-j)*ORD_DEF
        bound = min(d1*d2, total**2/4)
        factor = theta-d2-price*total-2*q0
        assert factor > 0 and 1-d1-theta > 0
        assert (1-d1-theta)*factor > bound+INV
    for j in range(4):
        total = deficit(j)+(3-j)*ORD_DEF
        assert j*theta_a+(3-j)*theta_o-price*total-3*q0 > 1
    return [deficit(j) for j in (1, 2, 3)]


def sampling(A, X, B, R, y_hi):
    """The tested cut and both extremal shortages within one width interval."""
    rho, eta = FILL/K, 1/(R*FILL**2)
    gamma, g, kappa = A/FILL, X/FILL, B/FILL
    x = g*rho
    j = (1+100*rho)/(1-x)
    assert 1/(R*K*K) < INV and K-1 >= 799
    assert 4*H**2*A < K and 1-x-FILL-F(3, 4) > F(1, H)
    assert (X+8*A)/K < ORD_DEF
    assert F(1, 8)+x+F(1, 256)+STAR < ORD_DEG
    assert 2*j*x < F(1, 512) and 2*x/(1-x) < F(1, 1000)
    assert 100*rho < 1 and 50*(1-rho)-1-g > 37 and x+INV < F(1, 2)

    ncap = F(513, 512)*gamma+F(1, 256)+x+STAR
    a = min(F(5, 2), F(249, 250)/ncap)
    assert a > F(4, 3) and a*kappa < 2
    k = F(4, 3)/(a-F(4, 3))
    b = j*(1+1/k)
    assert a*ncap+2*b*x < 1
    assert k*(a-F(4, 3)) == F(4, 3) and k*(b-j) == j
    assert k*((b/j)**2-1) >= 1
    V = a*(F(513, 512)*y_hi/FILL+F(7, K))+9*b/K
    mean_cost = k*eta*(((1+V)**2+V/K)/2+F(1, 2*K))

    def repair(W, l):
        return k*(b*W+l)**2/(2-a*kappa)+mean_cost

    z1 = 8*repair(2*kappa, 0)+2*eta
    W = (1/(1-x)+LAMBDA*g/37)*kappa+g*z1*rho/37
    z2 = 8*repair(W, 0)+2*eta
    assert max(z1, z2)*rho**2 < min(C/128, F(1, 16))
    assert C-LAMBDA*kappa*rho > 0
    margins = []
    for l in (F(0), LAMBDA*kappa):
        eps = repair(W, l)+g*l+l*l/2+eta*(F(1, 2)+F(1, 2*K))
        assert 0 < eps < 1
        margins.append((1-eps)*(C-LAMBDA*kappa*rho)+l-LAMBDA*kappa
                       -z2*rho-1/(FILL*R*K*K))
    return margins


if __name__ == '__main__':
    caps = auxiliary_checks()
    cases, strict = ordered_incidence_examples()
    check_fractional_pruning_overlap()
    widths, margins = [], []
    lo = F(0)
    for hi, b, ai, bi in BANDS:
        assert lo < hi <= 2
        alpha, beta = F(ai, 4000), F(bi, 4000)
        margin = width_margin(lo, hi, b, alpha, beta)
        assert margin > 0, (lo, hi, float(margin))
        widths.append(margin)
        for i in range(BINS):
            left, right = F(i, BINS), F(i+1, BINS)
            peak = max(left, min(F(1, 2), right))
            margins.extend(sampling(alpha*right, 2*beta*right,
                                    4*beta**2*peak*(1-peak), F(2**b), hi))
        lo = hi
    assert lo == 2
    assert min(widths) > F(1427, 100000)
    assert min(margins) > F(3327, 10000000)
    assert previous_exponent_gap() > F(159, 1000)
    print(f'Unrestricted cutoff 2^{EXPONENT}. {len(widths)} width bands, {len(margins):,} exact endpoints.')
    print(f'Minimum log-width margin {float(min(widths)):.9f}. Minimum signed-cut margin {float(min(margins)):.9f}.')
    print('Auxiliary one-, two-, three-row deficit caps:', ', '.join(f'{float(c):.9f}' for c in caps))
    print(f'Discarded-incidence check: {cases:,} graph and omission choices, {strict:,} positive savings.')
    print('17-vertex pruning replay: overlap 299/100, paper allowance 398/100.')
