"""Independent rational linear-arithmetic replay of the third pruning bounds.
Requires the z3-solver Python package. No calls to the subdivision verifier.
"""
from fractions import Fraction as F
from math import isqrt
import z3

CELLS=((0,501,14,656,925),(501,550,14,656,923),(550,650,14,653,918),
       (650,1000,15,652,916),(1000,2000,17,654,918))


def Q(x):
    x=F(x)
    return z3.Q(x.numerator,x.denominator)


def sqrt_upper(x):
    return F(1+isqrt(x.numerator*10**12//x.denominator),10**6)


def check_cell(cell):
    low,high,b,ia,ib=cell
    a,be=F(ia,4000),F(ib,4000)
    tau,c=F(199,400),F(9,25)
    p,t,z,s,e,k,d,h,m=z3.Reals('p t z s e k d h m')
    y=2-p/2-Q(tau)*t
    solver=z3.SolverFor('QF_LRA')
    solver.add(0<=p,p<=Q(F(125,61)),t>=0,z==1-p/4-Q(tau)*t,
               e>=0,s>=0,k>=0,s+e+Q(c)*k<=z,
               Q(F(low,1000))<=y,y<=Q(F(high,1000)))
    # log 2 > .69314718 and log(35/32) < .08963.
    scale=(F(143-b,4)-10)*F(69314718,10**8)-F(8963,10**5)
    base=Q(scale)-y/Q(a)-(p+t)/Q(be)
    savings=[(391+Q(F(1464,5))*p)/1120,(4333+737*p)/10000]
    count=0
    for rebate in savings:
        solver.push()
        solver.add(*[rebate<=x for x in savings])
        w=base+rebate
        solver.add(w+2*s/Q(a)<=0)
        solver.push()
        solver.add(w+(2*Q(tau-c)-k)/Q(be)+(2*s+Q(c)*k)/Q(a)<=0)
        assert solver.check()==z3.unsat
        solver.pop()
        solver.push()
        solver.add(p+t+k+Q(max(F(0),F(1,2)-2*(tau-c)))>=Q(F(353,100)))
        assert solver.check()==z3.unsat
        solver.pop()
        solver.add(d>=0,d<=1,h>=0,m>=0,h+m>=Q(F(1,2))-s,
                   d-Q(F(1,400))<=k-Q(be)*(w+(s+z-e)/Q(a)))
        def split(bounds):
            nonlocal count
            solver.push()
            (dl,du),(el,eu),(sl,su)=bounds
            for var,(lo,hi) in zip((d,e,s),bounds):
                solver.add(Q(lo)<=var,var<=Q(hi))
            for v in (F(1,32),F(1,16),F(1,8),F(1,4)):
                solver.add(Q(2*(1-v))*m<=Q(du)*(p+t+k)+s/Q(4*v))
            if du<1:
                den=1-du-eu/(1-du)-tau
                exc=z-s-e-Q(c)*k
                solver.add(Q(den)*h<=exc+2*Q(du+sqrt_upper(su))*e,
                           Q(den-c)*h<=exc)
            answer=solver.check()
            solver.pop()
            if answer==z3.unsat:
                count+=1
                return
            assert answer==z3.sat
            axis=max(range(3),key=lambda j:bounds[j][1]-bounds[j][0])
            left,right=bounds[axis]
            assert right-left>F(1,2**18),('unresolved',cell,bounds)
            mid=(left+right)/2
            for span in ((left,mid),(mid,right)):
                child=list(bounds)
                child[axis]=span
                split(child)
        split([(F(0),F(1))]*3)
        solver.pop()
    return count


if __name__=='__main__':
    # Positive-series enclosures, independent of the width checker's log helper.
    def bounds(x):
        u=(x-1)/(x+1)
        lo=2*sum(u**j/j for j in range(1,22,2))
        return lo,lo+2*u**23/(23*(1-u*u))
    assert bounds(F(2))[0]>F(69314718,10**8)
    assert bounds(F(35,32))[1]<F(8963,10**5)
    for cell in CELLS:
        print(f'Y <= {cell[1]}/1000: {check_cell(cell)} rational linear boxes excluded.',
              flush=True)
