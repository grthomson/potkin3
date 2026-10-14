"""Canonical maximal-material-island sealing; bounded independent validation.

Implementation detail: opaque shell tokens use fresh closed atomic ``hole``
nodes. The proof may instead use fresh nonmaterial Ref constants in an extended
context. Full beta/eta reduction treats either as inert atomic parameters:
neither can head an application, match a bound eta variable, or be captured.
Every token survives once by linearity and is restored. No CK/purity test is
performed on this implementation shell; in particular these temporary nodes
must not be interpreted as eligible material holes in the shell lemma.
"""
from pathlib import Path
import sys,json
from collections import Counter
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research_2026_10_10/material_bridge_client'))
import check_bridge as k
import enumerated_validation as gen
import source_reification as source
from cofree_profile import nf,cases


def normalize(t):
    k.check(t)
    def nodes(u):return {u.uid}|set().union(*(nodes(c) for c in u.children))
    used=nodes(t); serial=0;islands={}
    def fresh():
        nonlocal serial
        while True:
            uid=f'__island_{serial}';serial+=1
            if uid not in used:used.add(uid);return uid
    def hide(u):
        if k.pure(u):
            assert not k.check(u),'actual closed material islands only'
            uid=fresh();islands[uid]=u
            return k.T('hole',uid,u.typ)
        return k.T(u.kind,u.uid,u.typ,tuple(hide(c) for c in u.children),u.meta)
    opaque=nf(hide(t))
    def restore(u):
        if u.kind=='hole' and u.uid in islands:
            p=islands[u.uid];x=k.var(fresh(),p.typ)
            return k.app(fresh(),k.lam(fresh(),x,x),p)
        return k.T(u.kind,u.uid,u.typ,tuple(restore(c) for c in u.children),u.meta)
    result=restore(opaque)
    assert k.check(result)==k.check(t) and result.typ==t.typ
    return result


def profile(t,normalize_right):
    return Counter((tuple(sorted((k.key(p) for p in f),key=repr)),
                    k.key(normalize(r) if normalize_right else r))
                   for f,r,_ in k.coaction(t))


def validate(t):
    pending,seen,terms=[t],set(),0
    while pending:
        u=pending.pop()
        if u in seen:continue
        seen.add(u);nu=normalize(u)
        assert k.key(normalize(nu))==k.key(nu),'not idempotent'
        assert k.key(nf(nu))==k.key(nf(u)),'ordinary proof identity changed'
        assert profile(u,True)==profile(nu,False),'exact coaction failed'
        for _,r,_ in k.coaction(nu):
            assert k.key(normalize(r))==k.key(r),'normal image not material hereditary'
        for _,r,roots in k.coaction(u):
            terms+=1
            if roots:pending.append(r)
    return len(seen),terms


def main():
    totals=Counter();rows=[]
    contexts=((),((0,gen.A),),((0,k.arr(gen.A,gen.A)),),
              ((0,gen.A),(1,gen.P)),((0,k.arr(gen.A,gen.A)),(1,gen.A)))
    for ctx in contexts:
        for typ in gen.TYPES:
            for size in range(1,11):
                for ast in gen.generate(typ,ctx,size):
                    t=gen.instantiate(ast,f'j{totals["terms"]}',ctx)
                    a,b=validate(t)
                    totals['terms']+=1;totals['residual_states']+=a;totals['cut_terms']+=b
    for name,a,b,expected in cases():
        equal=k.key(normalize(a))==k.key(normalize(b))
        assert equal==expected,(name,'wrong equality')
        validate(a);validate(b)
        rows.append({'name':name,'same_canonical_representative':equal})
    sources=[]
    for name,args in [('binary',{}),('repeated',{'repeated':True}),('nested',{'nested':True}),('hypothetical',{'hypothetical':True})]:
        m,decode=source.fixture(**args);t=source.naturalise(m,decode);final=normalize(t)
        exact=Counter()
        for roots in source.antichains(m):
            r,f=source.source_cut(m,set(roots))
            exact[(tuple(sorted((k.key(source.naturalise(p,decode)) for p in f),key=repr)),
                   k.key(normalize(source.naturalise(r,decode))))]+=1
        assert exact==profile(final,False)
        a,b=validate(t)
        sources.append({'name':name,'source_antichain_terms':sum(exact.values()),'residual_states':a,'cut_terms':b})
    result={'status':'BOUNDED_CHECKS_PASS','policy':'hide maximal pure islands; full beta eta normalize opaque shell; restore each as identity seal',
      'totals':dict(totals),'carrier_gates':rows,'shadow_reification':sources,
      'checks':['idempotence','ordinary normal identity','exact material coaction','hereditary normal image'],
      'scope':'finite evidence, not mechanized general theorem'}
    Path(__file__).with_name('island_seal_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
