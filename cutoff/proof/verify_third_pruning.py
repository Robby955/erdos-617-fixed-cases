"""Rational subdivision for the third pruning pass at r >= 2^143."""
from fractions import Fraction as F
from math import isqrt

from verify_cutoff_145_obstruction import clip
from verify_pruning_corner import BANDS, incidence, width_cost
from verify_retained_width import P_MAX, affine_saving, reserved_fraction
from verify_weighted_width import K, TAU, log_bounds

C = F(9, 25)
D0 = F(1, 400)
ZERO = F(0)
ONE = F(1)


def sqrt_up(x):
    scale = 10**6
    a = isqrt((x.numerator*scale**2)//x.denominator)
    return F(a if a*a*x.denominator == x.numerator*scale**2 else a+1,scale)


def extrema(poly, f):
    values = [f(*pt) for pt in poly]
    return min(values),max(values)


def coordinate(poly, i):
    return extrema(poly, lambda p,z: (p,z)[i])


def split_poly(poly, i, mid):
    return [clip(poly, lambda pt: pt[i], mid),clip(poly, lambda pt: -pt[i], -mid)]


def certify_box(poly, width, a, beta, depths, maxima):
    """Cover p,Z by clipped polygons. Each carries a simplex of edge budgets."""
    zl,zh = coordinate(poly,1)
    wl,_ = extrema(poly,width)
    mass0 = extrema(poly,lambda p,z: p+(1-p/4-z)/TAU)[1]
    # All three later uses spend disjoint portions of Z.
    smax = min(zh,-a*wl/2)
    assert smax >= 0
    # Spare the extra subdivisions in the two planar variables when the
    # entire lifted box already admits a single certificate.
    def boxes(el,eh,kl,kh,sl,sh,depth=0):
        sh = min(sh,zh-el-C*kl)
        eh = min(eh,zh-sl-C*kl)
        kh = min(kh,(zh-sl-el)/C)
        if sh < sl or eh < el or kh < kl:
            return 1
        refund = max(sl+zl-eh,2*sl+C*kl)
        # With no chosen pair a width failure bounds the largest deficit.
        deficit = D0+kh-beta*(wl+refund/a)
        if deficit < D0:
            return 1
        L = 1-deficit
        if L > 0:
            den = L-eh/L-TAU
            if den>0:
                sroot=sqrt_up(sh)
                # A = sum of squared early deletion fractions.
                # A <= deficit*(p+t+k) + sqrt(s*A).
                rad = (sroot+sqrt_up(sh+4*deficit*(mass0+kh)))/2
                rr = rad**2/2
                excess = zh-sl-el-C*kl
                rs = (excess+2*eh*(deficit+sroot))/den
                if den>C:
                    rs=min(rs,excess/(den-C))
                gap = F(1,2)-sh-rr-rs
                if gap>0:
                    maxima['hole_gap']=min(maxima['hole_gap'],gap)
                    return 1
        if depth >= depths:
            return 0
        # Bisect the largest possible edge-budget interval.
        spans = [eh-el,C*(kh-kl),sh-sl]
        idx=spans.index(max(spans))
        if idx==0:
            m=(el+eh)/2
            parts=[(el,m,kl,kh,sl,sh),(m,eh,kl,kh,sl,sh)]
        elif idx==1:
            m=(kl+kh)/2
            parts=[(el,eh,kl,m,sl,sh),(el,eh,m,kh,sl,sh)]
        else:
            m=(sl+sh)/2
            parts=[(el,eh,kl,kh,sl,m),(el,eh,kl,kh,m,sh)]
        total=0
        for args in parts:
            count=boxes(*args,depth+1)
            if not count:return 0
            total+=count
        return total
    return boxes(ZERO,zh,ZERO,zh/C,ZERO,smax)


def verify():
    polygon=[(ZERO,ZERO),(P_MAX,ZERO),(P_MAX,1-P_MAX/4),(ZERO,ONE)]
    lo=ZERO
    total_leaves=0
    for hi,b,ai,bi in BANDS:
        a,beta=F(ai,4000),F(bi,4000)
        logmin=(F(143-b,4)-10)*log_bounds(F(2))[0]-log_bounds(F(K,1024))[1]
        band=clip(clip(polygon,incidence,hi),lambda pt:-incidence(pt),-lo)
        lo=hi
        totals={'leaves':0,'planar':0,'hole_gap':F(100),'q_margin':F(100),'count_margin':ONE}
        for save in (affine_saving,reserved_fraction):
            def width(p,z):
                return logmin-width_cost(p,z,a,beta)+save(p)
            # Failure of min(saving_1,saving_2) lies in this union.
            # All estimates below use the same saving as the old failure.
            def other(p):
                return (reserved_fraction if save is affine_saving else affine_saving)(p)
            active=clip(band,lambda pt:save(pt[0])-other(pt[0]),0)
            active=clip(active,lambda pt:width(*pt),0)
            if not active:continue
            qmargin=extrema(active,lambda p,z:width(p,z)+
                           (2*(TAU-C)-z/C)/beta+z/a)[0]
            assert qmargin>0,(hi,qmargin)
            totals['q_margin']=min(totals['q_margin'],qmargin)
            # Both branches keep the old limits D < 3.53 and n <= 1411.
            fresh=extrema(active,lambda p,z:p+(1-p/4-z)/TAU+z/C)[1]
            cap=fresh+max(ZERO,F(1,2)-2*(TAU-C))
            assert cap < F(353,100) and cap < D0*1412,(hi,cap)
            totals['count_margin']=min(totals['count_margin'],D0*1412-cap)
            def visit(poly,depth):
                count=certify_box(poly,width,a,beta,4 if depth<8 else 11,totals)
                if count:
                    totals['leaves']+=count
                    totals['planar']+=1
                    return
                if depth>=25:raise AssertionError(('undecided',hi,poly))
                pl,ph=coordinate(poly,0)
                zl,zh=coordinate(poly,1)
                axis=0 if ph-pl>4*(zh-zl) else 1
                left,right=(pl,ph) if axis==0 else (zl,zh)
                assert left<right
                for part in split_poly(poly,axis,(left+right)/2):
                    if part:visit(part,depth+1)
            visit(active,0)
        total_leaves+=totals['leaves']
        if not totals['planar']:
            print(f'Y <= {hi}: original width already passes.')
            continue
        print(f'Y <= {hi}: {totals["planar"]} polygons, {totals["leaves"]} leaves, '
              f'q>=1 margin {float(totals["q_margin"]):.8f}, '
              f'hole gap {float(totals["hole_gap"]):.8f}',flush=True)

    assert lo==2 and total_leaves>0
    print(f'{total_leaves} terminal boxes in total.')


if __name__=='__main__':
    verify()
