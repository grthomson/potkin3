"""Independent Nhat actual-hole refill challenge, including island splitting."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research_2026_10_10/material_bridge_client'))
import check_bridge as k
import enumerated_validation as g
import island_seal as island


def nhat(t):return t if k.pure(t) else island.normalize(t)
def fskey(f):return tuple(sorted((k.key(p) for p in f),key=repr))
def holes(t):
    if t.kind=='hole':yield t
    for c in t.children:yield from holes(c)
def refill(t,m):
    if t.kind=='hole':return m.get(t.uid,t)
    return k.T(t.kind,t.uid,t.typ,tuple(refill(c,m) for c in t.children),t.meta)
def provider(h,i,impure):
    stem=f'new_supply_{i}'
    d=k.prim(stem+'d','delta',(),h.typ)
    v=k.var(stem+'x',h.typ)
    return k.app(stem+'a',k.lam(stem+'l',v,v),d) if impure else d

def main():
    terms=states=checks=0
    for ctx in ((),((0,'p'),)):
        for typ in ('p',k.arr('p','p')):
            for n in range(1,9):
                for ast in g.generate(typ,ctx,n):
                    t=g.instantiate(ast,'host',ctx);u=nhat(t);terms+=1
                    left={fskey(f):r for f,r,_ in k.coaction(t)}
                    right={fskey(f):r for f,r,_ in k.coaction(u)}
                    assert left.keys()==right.keys()
                    for key,a in left.items():
                        b=right[key];hs=list(holes(a))
                        if not hs:continue
                        assert {h.uid for h in hs}=={h.uid for h in holes(b)}
                        states+=1
                        for pattern in range(min(1<<len(hs),8)):
                            fillings={h.uid:provider(h,i,bool(pattern&(1<<i))) for i,h in enumerate(hs)}
                            aa,bb=refill(a,fillings),refill(b,fillings)
                            assert k.check(aa)==k.check(bb)
                            assert k.key(nhat(aa))==k.key(nhat(bb)),(a,b,fillings)
                            checks+=1
    print({'terms':terms,'matched_open_states':states,'pure_impure_refill_tests':checks,
           'status':'PASS (bounded, at most8 patterns per state)'})
if __name__=='__main__':main()
