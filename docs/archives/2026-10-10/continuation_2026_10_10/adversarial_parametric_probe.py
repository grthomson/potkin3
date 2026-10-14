"""Independent finite challenge to symbolic purity-probe substitution stability."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research_2026_10_10/material_bridge_client'))
import check_bridge as k
import enumerated_validation as g
import island_seal as island


def nhat(t): return t if k.pure(t) else island.normalize(t)
def key(t):return k.key(nhat(t))
def psi(t,x):
    alpha=k.prim('parameter_alpha','parameter',(),'p')
    return (key(t),key(k.substitute(t,x,alpha)))
def fillings():
    d=k.prim('supply_delta','delta',(),'p')
    yield d
    yield k.prim('supply_h','h',('p',),'p',d)
    z=k.var('supply_z','p');yield z
    y=k.var('supply_y','p')
    yield k.app('supply_app',k.lam('supply_lam',y,y),d)
    yield k.prim('supply_h','h',('p',),'p',z)
    h=k.T('hole','supply_hole','p');yield h

def main():
    checked=equations=substitutions=rejected=0
    ctx=((0,'p'),)
    for typ in g.TYPES:
        for n in range(1,9):
            for ast in g.generate(typ,ctx,n):
                t=g.instantiate(ast,'host',ctx);x='host_free_0'
                for u in k.one_steps(t,atomic_beta=True):
                    checked+=1
                    if psi(t,x)!=psi(u,x):rejected+=1;continue
                    equations+=1
                    for p in fillings():
                        a,b=k.substitute(t,x,p),k.substitute(u,x,p)
                        assert key(a)==key(b),(t,u,p,a,b)
                        substitutions+=1
    print({'candidate_edges':checked,'symbolically_accepted':equations,
           'symbolically_rejected':rejected,'actual_filler_tests':substitutions,
           'status':'PASS (bounded one-free-atomic-input probe)'})
if __name__=='__main__':main()
