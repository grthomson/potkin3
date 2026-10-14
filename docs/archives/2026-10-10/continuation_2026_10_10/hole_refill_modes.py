"""Closed material-origin hole filling: island refinement and congruence checks.

Not a BeS engine or universal proof. No new hole purity-mode coordinate is used.
"""
from itertools import product
from collections import Counter
import material_modes as mm
k=mm.k


def walk(t):
    yield t
    for c in t.children:yield from walk(c)


def holes(t):
    return {x.uid:x for x in walk(t) if x.kind=='hole'}


def fill_holes(t,fillers):
    if t.kind=='hole' and t.uid in fillers:
        p=fillers[t.uid]
        assert not t.meta and not k.check(p),'closed complete holes/fillers only'
        assert p.typ==t.typ,'hole conclusion mismatch'
        return p
    return k.T(t.kind,t.uid,t.typ,tuple(fill_holes(c,fillers) for c in t.children),t.meta)


def islands(t):
    if k.pure(t):return (t,)
    return tuple(m for c in t.children for m in islands(c))


def identity(p,tag):
    x=k.var(tag+'_x',p.typ)
    return k.app(tag+'_app',k.lam(tag+'_lam',x,x),p)


def filler(a,tag,mode):
    leaf=lambda s:k.prim(tag+'_'+s,'delta_'+a,(),a)
    if mode==0:return leaf('d')
    if mode==1:return identity(leaf('d'),tag+'_id')
    if mode==2:return k.prim(tag+'_r','r_'+a,(a,a),a,leaf('d'),leaf('e'))
    if mode==3:return k.prim(tag+'_r','r_'+a,(a,a),a,
                             identity(leaf('d'),tag+'_i1'),identity(leaf('e'),tag+'_i2'))
    if mode==4:return k.T('hole',tag+'_newhole',a)
    raise ValueError(mode)


def fixtures():
    p,q='p','q'
    h=[k.T('hole','h'+str(i),p) for i in range(3)]
    m=k.prim('r','r',(p,p),p,k.prim('s','s',(p,p),p,h[0],h[1]),h[2])
    f=k.var('f',k.arr(p,q));x=k.var('x',p)
    first=k.app('outer1',k.lam('lambda1',x,k.app('inner1',f,x)),m)
    second=k.app('outer2',f,m)
    yield 'nested_three_hole_island',first,second
    # Several old islands separated by positive logical wrappers.
    j=[k.T('hole','j'+str(i),p) for i in range(2)]
    left=k.prim('join','join',(p,p),p,identity(j[0],'left'),identity(j[1],'right'))
    yield 'two_separated_islands',left,identity(left,'outside')
    # Pure-root case is handled by exact raw equality, not by stripping a seal.
    yield 'pure_root',m,m
    # Hole outside a nontrivial island, with a binder in the logical shell.
    v=k.var('v',k.arr(p,q));one=k.lam('ll',v,k.app('aa',v,h[0]))
    yield 'bound_logical_shell',identity(one,'oid'),one


def run():
    counts=Counter()
    for name,left,right in fixtures():
        assert k.check(left)==k.check(right) and left.typ==right.typ
        assert k.key(mm.nhat(left))==k.key(mm.nhat(right)),name
        assert mm.modes(left)==mm.modes(right),name
        hs=holes(left)
        assert hs.keys()==holes(right).keys()
        names=sorted(hs)
        for choice in product(range(5),repeat=len(names)):
            fs={h:filler(hs[h].typ,'fill_'+h,mode) for h,mode in zip(names,choice)}
            a,b=fill_holes(left,fs),fill_holes(right,fs)
            assert k.check(a)==k.check(b)
            assert k.key(mm.nhat(a))==k.key(mm.nhat(b)),(name,choice,'Nhat congruence')
            assert mm.modes(a)==mm.modes(b),(name,choice,'Sigma congruence')
            for original,expanded in ((left,a),(right,b)):
                direct=Counter(k.key(m) for m in islands(expanded))
                refinement=Counter(k.key(n) for m in islands(original)
                                   for n in islands(fill_holes(m,fs)))
                assert direct==refinement,(name,choice,'island boundary crossing')
                counts['island_refinement_checks']+=1
            assert mm.island.profile(a,True)==mm.island.profile(b,True)
            counts['refill_coaction_equalities']+=1
            counts['simultaneous_fillings']+=1
            counts['impure_fillings']+=any(mode in (1,3) for mode in choice)
            counts['nested_vacancy_fillings']+=4 in choice
    return {'status':'FINITE_CHECKS_PASS','counts':dict(counts),
            'scope':'closed atomic material-origin holes; no extra hole-mode coordinates',
            'proof':'hole_refill_modes.md'}


if __name__=='__main__':
    print(run())
