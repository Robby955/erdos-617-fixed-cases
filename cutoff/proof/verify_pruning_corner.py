"""Color-bundle checks and the five signed cuts used by the third pruning proof."""
from fractions import Fraction as F
from itertools import combinations

from verify_weighted_width import BINS, K, STAR, TAU, auxiliary_checks, log_bounds, sampling

P_CAP = F(2021, 1000)
BASE = 2**143
# Upper Y endpoint, log2 R, 4000 alpha, 4000 beta.
BANDS = (
    (F(501, 1000), 14, 656, 925),
    (F(55, 100), 14, 656, 923),
    (F(65, 100), 14, 653, 918),
    (F(1), 15, 652, 916),
    (F(2), 17, 654, 918),
)


def incidence(pt):
    p, z = pt
    return 1-p/4+z


def width_cost(p, z, alpha, beta):
    t = (1-p/4-z)/TAU
    return incidence((p,z))/alpha+(p+t)/beta


def signed_cuts():
    assert (F(1,4)-STAR/2-F(1,2*BASE))*P_CAP > (1+STAR)/2
    auxiliary_checks()
    margins=[]
    for hi,b,ai,bi in BANDS:
        alpha,beta=F(ai,4000),F(bi,4000)
        assert 0 < alpha <= beta and TAU*beta <= alpha <= 2*(1-F(1,BASE))*beta
        assert (1-2*TAU-F(1,256))*K/(2*beta) >= 2+F(3,5)
        assert BASE > 2**b*(8*(K+2*1411))**4
        for j in range(BINS):
            left,right=F(j,BINS),F(j+1,BINS)
            peak=min(right,max(left,F(1,2)))
            margins.extend(sampling(alpha*right,2*beta*right,
                                    4*beta**2*peak*(1-peak),F(2**b),hi))
    assert len(margins)==1280 and min(margins)>0
    return min(margins)


def local_bundle(r,z):
    """Non-target matchings on r raw vertices and z additional sources."""
    d = r//4
    assert 1 <= z <= r-z-1 and d <= r-z-1
    # Raw anchors 0..z-1, raw pivot r-1, exterior r..r+z-1.
    matchings = []
    for j in range(d):
        matchings.append([(i,z+(i+j)%(r-z-1)) for i in range(z)])
    for j in range(r-1-d):
        matchings.append([((i+j)%r,r+i) for i in range(z)])
    used = set()
    for matching in matchings:
        assert len(set(x for e in matching for x in e)) == 2*z
        assert not used.intersection(matching)
        used.update(matching)
    assert len(matchings) == r-1
    assert sum(y < r for x,y in used) == d*z
    assert all((i,r-1) not in used for i in range(r-1))
    assert all(sum((i,s) not in used for i in range(r)) == d+1 for s in range(r,r+z))
    assert all(e not in used for e in combinations(range(r,r+z),2))
    # Each of these classes is a target clique, hence alpha(target) <= 3.
    for block in (range(z),range(z,r),range(r,r+z)):
        assert all(e not in used for e in combinations(block,2))


def check_two_foreign_rows():
    """Exhaust all cross-edge sets and all allowed lists in two 3-vertex rows."""
    checked=0
    for left in range(8):
        for right in range(8):
            products=sum(1 << (3*i+j) for i in range(3) for j in range(3)
                         if left & (1<<i) and right & (1<<j))
            deleted=6-left.bit_count()-right.bit_count()
            for cross in range(512):
                if products & ~cross == 0:
                    assert 3*deleted >= 9-cross.bit_count()
                checked+=1
    assert checked==32768
    return checked


def interior_test():
    p,z = F(199,100),F(1,1000)
    assert p < P_CAP and 0 < z < 1-p/4 and F(501,1000) < incidence((p,z)) < F(55,100)
    assert p/1000 < STAR and p/4000 < F(1,1200) and p/4 < F(1,2)
    _,b,ai,bi = BANDS[1]
    upper = ((F(143-b,4)-10)*log_bounds(F(2))[1]-log_bounds(F(K,1024))[0]
             -width_cost(p,z,F(ai,4000),F(bi,4000))+
             2-2*log_bounds(F(2))[0])
    # G(1)=2-2 log 2 gives even the maximum of this endpoint guarantee.
    assert upper < -F(9,100)
    return upper


if __name__ == '__main__':
    c = signed_cuts()
    for order in range(8,51):
        for sources in range(1,(order-1)//2+1):
            local_bundle(order,sources)
    tests = check_two_foreign_rows()
    print(f'{tests} concrete two-row list and coloring tests passed.')
    obstruction = interior_test()
    print(f'Minimum of {2*BINS*len(BANDS)} signed cuts {float(c):+.9f}.')
    print(f'Interior width at 2^143, even with G(1): at most {float(obstruction):+.9f}.')
