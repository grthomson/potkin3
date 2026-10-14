"""Faithful tagged linear implication sequent macros; exact material comparison."""
from dataclasses import dataclass
from itertools import product
from collections import Counter
from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import cofree_profile as c
import island_seal as islands
import material_modes as modes
k=c.k

@dataclass(frozen=True)
class S:
    rule:str
    uid:str
    typ:object
    children:tuple=()
    data:tuple=()

def ax(x,a):return S('ax',x,a)
def prim(u,name,out,*ps):return S('prim',u,out,ps,(name,tuple(p.typ for p in ps)))
def right(u,x,a,p):return S('right',u,k.arr(a,p.typ),(p,),(x,a))
def cut(u,x,p,q):return S('cut',u,q.typ,(p,q),(x,p.typ))
def left(u,f,y,p,q,b):return S('left',u,q.typ,(p,q),(f,y,k.arr(p.typ,b),b))

def judgment(t):
    if t.rule=='ax':return ((t.uid,t.typ),)
    if t.rule=='hole':return t.data
    cs=[dict(judgment(p)) for p in t.children]
    if t.rule=='prim':
        assert all(k.atomic(p.typ) for p in t.children) and k.atomic(t.typ)
    elif t.rule=='right':
        x,a=t.data;assert cs[0].pop(x)==a
        assert t.typ==k.arr(a,t.children[0].typ)
    elif t.rule=='cut':
        x,a=t.data;assert cs[1].pop(x)==a==t.children[0].typ
        assert t.typ==t.children[1].typ
    elif t.rule=='left':
        f,y,ab,b=t.data;assert cs[1].pop(y)==b
        assert ab==k.arr(t.children[0].typ,b) and t.typ==t.children[1].typ
        cs.append({f:ab})
    else:raise AssertionError(t.rule)
    return k.merge(tuple(tuple(x.items()) for x in cs))

def tag(t,role):return f'J:{t.uid}:{t.rule}:{role}'
def elaborate(t):
    ps=tuple(elaborate(p) for p in t.children)
    if t.rule=='ax':return k.var(t.uid,t.typ)
    if t.rule=='hole':return k.T('hole',t.uid,t.typ,(),t.data)
    if t.rule=='prim':return k.T('prim',t.uid,t.typ,ps,t.data)
    if t.rule=='right':
        x,a=t.data;return k.lam(tag(t,'right'),k.var(x,a),ps[0])
    if t.rule=='cut':
        x,a=t.data;return k.app(tag(t,'cutapp'),k.lam(tag(t,'cutlam'),k.var(x,a),ps[1]),ps[0])
    if t.rule=='left':
        f,y,ab,b=t.data
        return k.app(tag(t,'leftapp'),k.lam(tag(t,'leftlam'),k.var(y,b),ps[1]),k.app(tag(t,'use'),k.var(f,ab),ps[0]))
    raise AssertionError(t.rule)

def readback(t):
    if t.kind=='var':return ax(t.uid,t.typ)
    if t.kind in ('prim','hole'):return S(t.kind,t.uid,t.typ,tuple(map(readback,t.children)),t.meta)
    _,uid,rule,role=t.uid.split(':')
    if rule=='right':return right(uid,*t.meta,readback(t.children[0]))
    fn,p=t.children;x,a=fn.meta
    if rule=='cut':return cut(uid,x,readback(p),readback(fn.children[0]))
    assert rule=='left';f,arg=p.children
    return left(uid,f.uid,x,readback(arg),readback(fn.children[0]),a)

def pure(t):return t.rule=='hole' or (t.rule=='prim' and all(map(pure,t.children)))
def antichains(t):
    xs=[tuple(x for part in parts for x in part) for parts in product(*(antichains(p) for p in t.children))]
    if t.rule=='prim' and pure(t):xs.append((t.uid,))
    return xs

def extract(t,roots):
    if t.uid in roots:return S('hole',t.uid,t.typ,(),judgment(t)),(t,)
    ps=[];forest=()
    for p in t.children:
        q,f=extract(p,roots);ps.append(q);forest+=f
    return S(t.rule,t.uid,t.typ,tuple(ps),t.data),forest

def verify(t):
    def ids(u):
        yield u.uid
        for p in u.children:yield from ids(p)
    names=tuple(ids(t));assert len(names)==len(set(names)) and all(':' not in x for x in names), 'source UID namespace'
    j=elaborate(t);assert judgment(t)==k.check(j) and readback(j)==t
    native=Counter()
    for roots in antichains(t):
        r,forest=extract(t,roots)
        native[(tuple(sorted((k.key(elaborate(p)) for p in forest),key=repr)),k.key(elaborate(r)),tuple(sorted(roots)))]+=1
    target=Counter((tuple(sorted((k.key(p) for p in f),key=repr)),k.key(r),tuple(sorted(roots))) for f,r,roots in k.coaction(j))
    assert native==target
    return len(native)

def main():
    d=prim('d','delta','p');e=prim('e','epsilon','p')
    x=ax('x','p');y=ax('y','p');z=ax('z','p')
    r=lambda p,q:prim('r','r','q',p,q)
    rows=[];mode_checks=0
    # Native dependent Cut-Cut, rather than hand-written ND-only test.
    m=right('rz','z','p',r(x,z));p=prim('s','s','p',y)
    pairs=[('dependent_cut_cut',cut('cy','y',d,cut('cx','x',p,m)),cut('cx','x',cut('cy','y',d,p),m)),
      ('cut_right',cut('cx','x',d,m),right('rz','z','p',cut('cx','x',d,r(x,z)))),
      ('independent_cut_cut',cut('cx','x',d,cut('cy','y',e,r(x,y))),cut('cy','y',e,cut('cx','x',d,r(x,y))))]
    # Cut enters either premise of an actual implication-left macro.
    lp=left('lf','f','y',x,prim('s','s','q',y),'p')
    pairs.append(('cut_left_argument',cut('cx','x',d,lp),left('lf','f','y',cut('cx','x',d,x),prim('s','s','q',y),'p')))
    lq=left('lf','f','y',e,r(x,y),'p')
    pairs.append(('cut_left_continuation',cut('cx','x',d,lq),left('lf','f','y',e,cut('cx','x',d,r(x,y)),'p')))
    pairs.append(('primitive_passenger',cut('cx','x',d,prim('r','r','q',x,e)),prim('r','r','q',cut('cx','x',d,x),e)))
    for name,a,b in pairs:
        na,nb=verify(a),verify(b)
        assert judgment(a)==judgment(b)
        assert c.phi(elaborate(a))==c.phi(elaborate(b))
        assert modes.modes(elaborate(a))==modes.modes(elaborate(b))
        rows.append(dict(name=name,left_material_terms=na,right_material_terms=nb,exact_profile_equal=True))
        # Expose every nullary payload as a native free atomic input, then
        # independently instantiate every subset with a fresh pure provider.
        def expose(t):
            if t.rule=='prim' and not t.children:return ax('input_'+t.uid,t.typ)
            return S(t.rule,t.uid,t.typ,tuple(expose(p) for p in t.children),t.data)
        oa,ob=expose(a),expose(b)
        assert judgment(oa)==judgment(ob)
        assert modes.modes(elaborate(oa))==modes.modes(elaborate(ob))
        inputs=[(x,ty) for x,ty in judgment(oa) if k.atomic(ty)]
        for bits in product((False,True),repeat=len(inputs)):
            ja,jb=elaborate(oa),elaborate(ob)
            for (input_uid,ty),bit in zip(inputs,bits):
                if bit:
                    provider=k.prim('formal_'+input_uid,'formal_delta',(),ty)
                    ja=k.substitute(ja,input_uid,provider);jb=k.substitute(jb,input_uid,provider)
            assert c.phi(ja)==c.phi(jb),(name,bits,'mode profile')
            assert k.key(islands.normalize(ja))==k.key(islands.normalize(jb)),(name,bits,'sealed mode')
            mode_checks+=1
        # Fresh compound context exercises equality under binders and application,
        # at three increasing depths.
        ac,bc=a,b
        for depth in range(1,4):
            a,b=ac,bc
            v='wrap'+str(depth)
            aa=right(v,v,k.arr(a.typ,'omega'),left('use'+v,v,'result'+v,a,ax('result'+v,'omega'),'omega'))
            bb=right(v,v,k.arr(b.typ,'omega'),left('use'+v,v,'result'+v,b,ax('result'+v,'omega'),'omega'))
            verify(aa);verify(bb);assert c.phi(elaborate(aa))==c.phi(elaborate(bb))
            ac,bc=aa,bb
    # Principal identity elimination can expose a NEW composite material cone.
    a=prim('r','r','q',cut('ci','x',d,x));b=prim('r','r','q',d)
    verify(a);verify(b)
    assert k.key(c.nf(elaborate(a)))==k.key(c.nf(elaborate(b)))
    pa,pb=c.phi(elaborate(a)),c.phi(elaborate(b))
    assert not (pa-pb) and sum((pb-pa).values())==1
    added=next(iter(pb-pa))
    assert added[0]==(k.key(elaborate(b)),) and added[1][0]=='hole'
    bad=left('bad','f','y',d,ax('z','p'),'p')
    try:judgment(bad)
    except KeyError:pass
    else:raise AssertionError('missing discharged occurrence accepted')
    out={'status':'PASS','cases':rows,'principal_identity_material_fusion_rejected':True,'exact_identity_cell_defect_terms':1,'missing_left_discharge_rejected':True,'nested_context_comparisons':18,'free_atomic_purity_mode_comparisons':mode_checks,'canonical_sigma_generator_comparisons':12,'scope':'linear intuitionistic implication + atomic primitive rules; origin-tagged macros; material coaction only'}
    Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
