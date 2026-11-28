"""Exact width-only certificate for cutoff-145-obstruction.md (Python 3.10+)."""
from fractions import Fraction as F
from verify_weighted_width import BANDS, K, P_MAX, TAU, log_bounds


def clip(poly, linear, bound):
    """Clip a convex polygon to linear(point) <= bound, exactly."""
    result = []
    for left, right in zip(poly, poly[1:]+poly[:1]):
        a, b = linear(left)-bound, linear(right)-bound
        if a <= 0:
            result.append(left)
        if a*b < 0:
            u = a/(a-b)
            result.append(tuple(x+u*(y-x) for x, y in zip(left, right)))
    return result


def margins(v=F(0), cross=F(0), wedges=F(0), overlap=F(0), saving=F(0)):
    """Lower width margins; v, cross (=1-X/r²), wedges, overlap are lower bounds."""
    assert 0 <= v <= cross <= 1 and 0 <= v+2*wedges <= 1
    pmax = P_MAX*(1-v-2*wedges)
    poly = [(F(0), cross), (pmax, cross), (pmax, 1-pmax/4), (F(0), F(1))]
    assert cross <= 1-pmax/4  # holds for the inputs tested below
    y = lambda pt: 1-pt[0]/4+pt[1]
    l2, _ = log_bounds(F(2))
    _, lk = log_bounds(F(K, 1024))
    lo = F(0)
    result = []
    for hi, b, ai, bi in BANDS:
        a, beta = F(ai, 4000), F(bi, 4000)
        band = clip(clip(poly, y, hi), lambda pt: -y(pt), -lo)
        lo = hi
        if not band:
            result.append(None)
            continue
        cost = max(y((p,z))/a+(p+(1-p/4-z)/TAU)/beta for p,z in band)
        integral_saving = max(saving, overlap/(2*beta))
        result.append((F(145-b,4)-10)*l2-lk+F(1,4)-cost
                      +2*cross/a+integral_saving)
    return result


def print_test(label, expected_positive=True, **kwargs):
    vals = margins(**kwargs)
    if expected_positive:
        assert all(m is None or m > 0 for m in vals), (label, vals)
    print(label+':', ' '.join('empty' if m is None else f'{float(m):+.9f}' for m in vals))
    return vals


if __name__ == '__main__':
    baseline = print_test('Old relaxation', False)
    assert [x > 0 for x in baseline] == [False, False, False, True, True]
    print_test('Cross slack >= 0.013', cross=F(13,1000))
    print_test('Wedge/surplus charge >= 0.12', wedges=F(3,25))
    print_test('Deficit-incidence overlap >= 0.074', overlap=F(37,500))
    print_test('Exact integral saving >= 0.160 in selected band', saving=F(4,25))
    print_test('Joint example: cross slack >= .006; overlap >= .040',
               cross=F(3,500), overlap=F(1,25))
