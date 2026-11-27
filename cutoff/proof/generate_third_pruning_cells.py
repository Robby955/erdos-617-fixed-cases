"""Emit Lean proof terms for the rational subdivisions in the third-pass proof.

Z3 proposes divisions and selects hypotheses. Lean proves every leaf from
those inequalities and checks that both children cover their parent.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import z3


def rat(x):
    return z3.Q(F(x).numerator,F(x).denominator)


def lit(x):
    x=F(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'


CELLS=((0,501,14,656,925),(501,550,14,656,923),(550,650,14,653,918),
       (650,1000,15,652,916),(1000,2000,17,654,918))
VARS='p t z s e k d h m w'


def cell_proof(i,cell):
    low,high,b,ia,ib=cell
    a,be=F(ia,4000),F(ib,4000)
    tau,c=F(199,400),F(9,25)
    p,t,z,s,e,k,d,h,m,w=z3.Reals(VARS)
    y=2-p/2-rat(tau)*t
    base=(F(143-b,4)-10)*F(69314718,10**8)-F(8963,10**5)
    wl=rat(base)-y/rat(a)-(p+t)/rat(be)+(349+114*p)/1000
    solver=z3.SolverFor('QF_LRA')
    fixed={'B.p0':0<=p,'B.p1':p<=rat(F(125,61)),'B.t0':t>=0,
           'B.edge_eq':z==1-p/4-rat(tau)*t,'B.s0':s>=0,'B.e0':e>=0,
           'B.k0':k>=0,'B.spent':s+e+rat(c)*k<=z,'B.old':w+2*s/rat(a)<=0,
           'B.d0':d>=0,'B.d1':d<=1,'B.h0':h>=0,'B.m0':m>=0,'B.holes':rat(F(1,2))-s<=h+m,
           'B.deficit':d-rat(F(1,400))<=k-rat(be)*(w+(s+z-e)/rat(a)),
           'yl':rat(F(low,1000))<=y,'yr':y<=rat(F(high,1000)),'wl':wl<=w}
    for name,con in fixed.items():solver.assert_and_track(con,name)
    out=[f'private theorem zero_cell_{i} {{{VARS} : ℝ}}',
         f'    (B : ZeroBounds {VARS} {lit(a)} {lit(be)})',
         f'    (yl : {lit(F(low,1000))} ≤ 2-p/2-(199/400)*t)',
         f'    (yr : 2-p/2-(199/400)*t ≤ {lit(F(high,1000))})',
         f'    (wl : {lit(base)}-(2-p/2-(199/400)*t)/{lit(a)}-(p+t)/{lit(be)}+(349+114*p)/1000 ≤ w) : False := by',
         '  have es : e ≤ 1 := by linarith only [B.spent,B.edge_eq,B.s0,B.k0,B.p0,B.t0]',
         '  have ss : s ≤ 1 := by linarith only [B.spent,B.edge_eq,B.e0,B.k0,B.p0,B.t0]']
    def split(bounds,labels,level=0,stem='  '):
        solver.push()
        local={}
        prefix='  '*level
        (dl,du),(el,eu),(sl,su)=bounds
        for j,(var,(l,r)) in enumerate(zip((d,e,s),bounds)):
            for sign,condition in enumerate((rat(l)<=var,var<=rat(r))):
                key=f'I{j}{sign}'
                solver.assert_and_track(condition,key)
                local[key]=labels[j][sign]
        for j,u in enumerate((F(1,32),F(1,16),F(1,8),F(1,4))):
            key=f'M{j}'
            solver.assert_and_track(rat(2*(1-u))*m<=rat(du)*(p+t+k)+s/rat(4*u),key)
            local[key]=f'(B.linear_young (D := {lit(du)}) (u := {lit(u)}) {labels[0][1]} (by norm_num) (by norm_num))'
        charge=None
        if du<1:
            root=F(1+isqrt(su.numerator*10**12//su.denominator),10**6)
            den=1-du-eu/(1-du)-tau
            solver.assert_and_track(rat(den)*h<=z-s-e-rat(c)*k+2*rat(du+root)*e,'H1')
            solver.assert_and_track(rat(den-c)*h<=z-s-e-rat(c)*k,'H2')
            local['H1']='ch.1';local['H2']='ch.2'
            charge=(f'have ch := B.linear_charge (D := {lit(du)}) (E := {lit(eu)}) (U := {lit(root)}) '
                    f'{labels[0][1]} (by norm_num) {labels[1][1]} '
                    f'(le_trans {labels[2][1]} (by norm_num)) (by norm_num)')
        ans=solver.check()
        core=[str(x) for x in solver.unsat_core()] if ans==z3.unsat else []
        solver.pop()
        if core:
            if charge and ('H1' in core or 'H2' in core):
                out.append(stem+charge)
                out.append(stem+'norm_num1 at ch')
            for key in core:
                if key.startswith('M') and key in local:
                    out.append(stem+f'have young_{key} := '+local[key])
                    out.append(stem+f'norm_num1 at young_{key}')
                    local[key]=f'young_{key}'
            refs=list(dict.fromkeys(local.get(x,x) for x in core))
            out.append(stem+'linarith only ['+', '.join(refs)+']')
            return
        assert ans==z3.sat
        j=max(range(3),key=lambda j:bounds[j][1]-bounds[j][0])
        l,r=bounds[j];mid=(l+r)/2
        name='cut'+str(level);var=('d','e','s')[j]
        out.append(stem+f'rcases le_total {var} ({lit(mid)}:ℝ) with {name} | {name}')
        for side,interval in enumerate(((l,mid),(mid,r))):
            child=bounds.copy();child[j]=interval
            labs=[list(ls) for ls in labels];labs[j][1-side]=name
            start=len(out);split(child,labs,level+1,stem+'  ')
            out[start]=stem+'· '+out[start][len(stem)+2:]
    split([(F(0),F(1))]*3,[['B.d0','B.d1'],['B.e0','es'],['B.s0','ss']])
    return '\n'.join(out)


def main():
    pre='''import ThirdPruningBounds

/-! Lean replay of the generated linear certificates. Each split is exhaustive
over real inputs. Regenerate with generate_third_pruning_cells.py. -/
namespace Erdos617.ThirdPruning
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 16000000
'''
    content=pre+'\n\n'.join(cell_proof(i,cell) for i,cell in enumerate(CELLS))
    content+='''
/-- No zero-pair configuration can fail both width tests at exponent 143. -/
theorem zero_branch_impossible {p t z s e k d h m w α β b : ℝ}
    (band : RetainedWidth.Band (2-p/2-(199/400)*t) b α β)
    (bounds : ZeroBounds p t z s e k d h m w α β)
    (width : ((143-b)/4-10)*(69314718/100000000)-8963/100000-
      (2-p/2-(199/400)*t)/α-(p+t)/β+(349+114*p)/1000 ≤ w) : False := by
  cases band with
'''
    for i,name in enumerate(('first','second','third','fourth','fifth')):
        content+=f'  | {name} yl yr => exact zero_cell_{i} (by convert bounds using 1 <;> norm_num) (by convert yl using 1 <;> norm_num) (by convert yr using 1 <;> norm_num) (by convert width using 1 <;> ring)\n'
    Path(__file__).with_name('ThirdPruningCells.lean').write_text(content+'\nend\nend Erdos617.ThirdPruning\n')


if __name__=='__main__':
    main()
