"""Independent unit-free linear tensor shell, not full tensor/implication IMLL.
The canonical observer expands indexed tensor inputs into their atomic leaves.
"""
from dataclasses import dataclass
from itertools import product
from collections import Counter
from pathlib import Path
import json

@dataclass(frozen=True)
class T:
    op:str
    uid:str
    typ:object
    cs:tuple=()
    meta:tuple=()
def atom(a):return isinstance(a,str)
def var(x,a):return T('var',x,a)
def prim(u,a,*ps):return T('prim',u,a,ps)
def pair(u,p,q):return T('pair',u,(p.typ,q.typ),(p,q))
def let(u,p,x,y,q):return T('let',u,q.typ,(p,q),(x,y))
def cut(u,p,x,q):return T('cut',u,q.typ,(p,q),(x,))
def merge(*ds):
    out={}
    for d in ds:
        assert not out.keys()&d.keys(),'resource duplicated';out.update(d)
    return out
def check(t,seen=None):
    if seen is None:seen=set()
    assert t.uid not in seen;seen.add(t.uid)
    if t.op=='var':return {t.uid:t.typ}
    if t.op=='hole':assert atom(t.typ);return {}
    envs=[check(p,seen) for p in t.cs]
    if t.op=='prim':assert atom(t.typ) and all(atom(p.typ) for p in t.cs)
    elif t.op=='pair':assert t.typ==tuple(p.typ for p in t.cs)
    elif t.op=='let':
        p,q=t.cs;x,y=t.meta;assert not atom(p.typ)
        assert envs[1].pop(x)==p.typ[0] and envs[1].pop(y)==p.typ[1]
        assert t.typ==q.typ
    elif t.op=='cut':
        p,q=t.cs;x,=t.meta;assert envs[1].pop(x)==p.typ and t.typ==q.typ
    else:raise AssertionError(t.op)
    return merge(*envs)

def expand(uid,typ,path=()):
    if atom(typ):return ('input',uid,path,typ)
    return ('pair',expand(uid,typ[0],path+(0,)),expand(uid,typ[1],path+(1,)))
def nf(t,env=None):
    if env is None:env={x:expand(x,a) for x,a in check(t).items()}
    if t.op=='var':return env[t.uid]
    if t.op=='hole':return ('hole',t.uid,t.typ)
    if t.op=='prim':return ('prim',t.uid,t.typ,tuple(nf(p,env) for p in t.cs))
    if t.op=='pair':return ('pair',*(nf(p,env) for p in t.cs))
    p,q=t.cs;value=nf(p,env);local=dict(env)
    if t.op=='let':
        assert value[0]=='pair';x,y=t.meta;local.update({x:value[1],y:value[2]})
    elif t.op=='cut':local[t.meta[0]]=value
    else:raise AssertionError(t.op)
    return nf(q,local)
def pure(t):return t.op=='hole' or (t.op=='prim' and all(map(pure,t.cs)))
def antichains(t):
    out=[tuple(x for p in ps for x in p) for ps in product(*(antichains(p) for p in t.cs))]
    if t.op=='prim' and pure(t):out.append((t.uid,))
    return out
def extract(t,roots):
    if t.uid in roots:
        assert not check(t);return T('hole',t.uid,t.typ),(t,)
    qs=[];forest=()
    for p in t.cs:
        q,f=extract(p,roots);qs.append(q);forest+=f
    return T(t.op,t.uid,t.typ,tuple(qs),t.meta),forest
def rawkey(t):return (t.op,t.uid,t.typ,t.meta,tuple(map(rawkey,t.cs)))
def phi(t):
    out=Counter()
    for roots in antichains(t):
        r,f=extract(t,roots);assert check(r)==check(t)
        out[(tuple(sorted(map(rawkey,f),key=repr)),nf(r))]+=1
    return out

def subst(t,x,p):
    if t.op=='var' and t.uid==x:assert t.typ==p.typ;return p
    assert x not in t.meta,'fresh bound occurrences required'
    return T(t.op,t.uid,t.typ,tuple(subst(q,x,p) for q in t.cs),t.meta)
def size(t):return 1+sum(map(size,t.cs))

def main():
    a,b='a','b';x=var('x',a);y=var('y',b);z=var('z',a)
    d=prim('d',a);e=prim('e',b);f=prim('f',a)
    r=lambda p,q:prim('r','c',p,q)
    rows=[]
    cases=[]
    # Logical tensor principal reduction may fuse material: must distinguish.
    cases.append(('tensor_principal_material_fusion',let('l',pair('p',d,e),'x','y',r(x,y)),r(d,e),False))
    # Tensor eta: variable pair has no material and is harmless here.
    v=var('v',(a,b))
    cases.append(('tensor_eta',let('l',v,'x','y',pair('p',x,y)),v,True))
    # Passive explicit Cut through tensor introduction (either premise).
    cases.append(('cut_pair_left',cut('c',d,'x',pair('p',x,e)),pair('p',cut('c',d,'x',x),e),True))
    cases.append(('cut_pair_right',cut('c',e,'y',pair('p',d,y)),pair('p',d,cut('c',e,'y',y)),True))
    # Cut through tensor elimination scrutinee and continuation respectively.
    cases.append(('cut_let_scrutinee',cut('c',d,'x',let('l',pair('p',x,e),'z','y',r(z,y))),let('l',cut('c',d,'x',pair('p',x,e)),'z','y',r(z,y)),True))
    body=prim('r','c',x,y,z)
    cases.append(('cut_let_body',cut('c',f,'z',let('l',pair('p',d,e),'x','y',body)),let('l',pair('p',d,e),'x','y',cut('c',f,'z',body)),True))
    # Compound cut, genuinely tensor interface, enters a pair.
    u=var('u',(a,b));payload=pair('p',d,e)
    cases.append(('compound_cut_pair',cut('c',payload,'u',pair('outer',u,f)),pair('outer',cut('c',payload,'u',u),f),True))
    # A principal reduction whose continuation retains a logical boundary.
    cases.append(('tensor_principal_sealed',let('l',pair('p',d,e),'x','y',pair('q',x,y)),pair('q',d,e),True))
    mode_count=0
    for name,p,q,equal in cases:
        assert check(p)==check(q) and p.typ==q.typ
        assert nf(p)==nf(q),(name,'ordinary tensor theory')
        assert (phi(p)==phi(q))==equal,(name,'CK profile')
        rows.append(dict(name=name,ordinary_equal=True,material_profile_equal=equal,left_terms=sum(phi(p).values()),right_terms=sum(phi(q).values())))
        if 'cut_' in name:
            def expose(t):
                if t.op=='prim' and not t.cs:return var('input_'+t.uid,t.typ)
                return T(t.op,t.uid,t.typ,tuple(expose(c) for c in t.cs),t.meta)
            op,oq=expose(p),expose(q);assert check(op)==check(oq)
            inputs=list(check(op).items())
            for flags in product((False,True),repeat=len(inputs)):
                ip,iq=op,oq
                for (uid,ty),flag in zip(inputs,flags):
                    if flag:
                        material=prim('formal_'+uid,ty)
                        ip=subst(ip,uid,material);iq=subst(iq,uid,material)
                assert nf(ip)==nf(iq) and phi(ip)==phi(iq)
                mode_count+=1
    # Tensor variable eta-expanded all the way to atomic components.
    nested=var('nested',((a,b),a));u=var('u',(a,b))
    eta=let('l0',nested,'u','z',let('l1',u,'x','y',pair('p0',pair('p1',x,y),z)))
    assert nf(eta)==nf(nested)
    # Independent elimination scheduling, fixed indexed primitive outputs.
    vv=var('vv',(a,b));ww=var('ww',(a,b));xx=var('xx',a);yy=var('yy',b)
    body=pair('o',r(x,y),prim('s','c',xx,yy))
    l=let('l',vv,'x','y',let('ll',ww,'xx','yy',body))
    rr=let('ll',ww,'xx','yy',let('l',vv,'x','y',body))
    assert check(l)==check(rr) and nf(l)==nf(rr) and phi(l)==phi(rr)
    out={'status':'PASS','scope':'unit-free linear tensor + explicit Cut + atomic primitives; no implication','cases':rows,'free_input_modes':mode_count,'nested_tensor_eta':True,'independent_let_exchange':True}
    Path(__file__).with_name('tensor_results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
