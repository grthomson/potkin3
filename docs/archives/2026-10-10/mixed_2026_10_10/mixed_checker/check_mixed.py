"""Independent bounded mixed IMLL checks, not a completeness proof.

The symbolic evaluator uses neutral tensor projections to test known equations.
No assertion that equality of these keys is complete for an arbitrary carrier.
Material factors, by contrast, retain exact occurrence-marked syntax.
"""
from dataclasses import dataclass
from itertools import product, count
from collections import Counter
from pathlib import Path
import json

def ten(a,b): return ('tensor',a,b)
def arr(a,b): return ('arrow',a,b)
def atomic(a): return isinstance(a,str)
@dataclass(frozen=True)
class T:
    op:str
    uid:object
    typ:object
    cs:tuple=()
    meta:tuple=()
def var(x,a): return T('var',x,a)
def prim(u,a,*ps): return T('prim',u,a,ps)
def pair(u,p,q): return T('pair',u,ten(p.typ,q.typ),(p,q))
def lam(u,x,a,p): return T('lam',u,arr(a,p.typ),(p,),(x,a))
def app(u,p,q):
    assert not atomic(p.typ) and p.typ[0]=='arrow' and p.typ[1]==q.typ
    return T('app',u,p.typ[2],(p,q))
def let(u,p,x,y,q): return T('let',u,q.typ,(p,q),(x,y))
def merge(*ds):
    out={}
    for d in ds:
        assert not out.keys()&d.keys(),'linear resource duplicated'
        out.update(d)
    return out
def check(t,seen=None):
    if seen is None:seen=set()
    assert t.uid not in seen,('occurrence UID reused',t.uid)
    seen.add(t.uid)
    if t.op=='var':return {t.uid:t.typ}
    if t.op=='hole':assert atomic(t.typ);return {}
    envs=[check(p,seen) for p in t.cs]
    if t.op=='prim':assert atomic(t.typ) and all(atomic(p.typ) for p in t.cs)
    elif t.op=='pair':assert t.typ==ten(*(p.typ for p in t.cs))
    elif t.op=='lam':
        x,a=t.meta;assert envs[0].pop(x)==a
        assert t.typ==arr(a,t.cs[0].typ)
    elif t.op=='app':assert t.cs[0].typ==arr(t.cs[1].typ,t.typ)
    elif t.op=='let':
        p,q=t.cs;x,y=t.meta;assert p.typ[0]=='tensor'
        assert envs[1].pop(x)==p.typ[1] and envs[1].pop(y)==p.typ[2]
        assert q.typ==t.typ
    else:raise AssertionError(t.op)
    return merge(*envs)

# NbE semantic values are neutral tuples, pair tuples, or Python closures.
_fresh=count()
def reflect(a,n):
    if atomic(a):return n
    if a[0]=='tensor':return (reflect(a[1],('fst',n)),reflect(a[2],('snd',n)))
    return lambda v:reflect(a[2],('apply',n,quote(a[1],v,0)))
def quote(a,v,depth=0):
    if atomic(a):return v
    if a[0]=='tensor':return ('pair',quote(a[1],v[0],depth),quote(a[2],v[1],depth))
    # Fresh semantic names must not depend on separately quoted argument depth.
    uid=next(_fresh);z=('bound',uid,a[1])
    return ('lambda',uid,a[1],quote(a[2],v(reflect(a[1],z)),depth+1))
def evaluate(t,env):
    if t.op=='var':return env[t.uid]
    if t.op=='hole':return ('hole',t.uid,t.typ)
    if t.op=='prim':return ('prim',t.uid,t.typ,tuple(evaluate(c,env) for c in t.cs))
    if t.op=='pair':return tuple(evaluate(c,env) for c in t.cs)
    if t.op=='lam':
        x,a=t.meta
        return lambda v:evaluate(t.cs[0],dict(env,**{x:v}))
    if t.op=='app':return evaluate(t.cs[0],env)(evaluate(t.cs[1],env))
    if t.op=='let':
        p,q=t.cs;x,y=t.meta;v,w=evaluate(p,env)
        return evaluate(q,dict(env,**{x:v,y:w}))
    raise AssertionError(t.op)
def alpha(k,env=None):
    if env is None:env={}
    if not isinstance(k,tuple):return k
    if k and k[0]=='bound':return ('bound',env[k[1]],k[2])
    if k and k[0]=='lambda':
        new=dict(env);new[k[1]]=len(env)
        return ('lambda',k[2],alpha(k[3],new))
    return tuple(alpha(v,env) for v in k)
def nf(t):
    env={x:reflect(a,('free',x,a)) for x,a in check(t).items()}
    return alpha(quote(t.typ,evaluate(t,env)))
def pure(t):return t.op=='hole' or (t.op=='prim' and all(map(pure,t.cs)))
def antichains(t):
    out=[tuple(x for roots in batch for x in roots) for batch in product(*(antichains(c) for c in t.cs))]
    if t.op=='prim' and pure(t):out.append((t.uid,))
    return out
def extract(t,roots):
    if t.uid in roots:
        assert t.op=='prim' and pure(t) and not check(t)
        return T('hole',t.uid,t.typ),(t,)
    cs=[];forest=()
    for c in t.cs:
        p,f=extract(c,roots);cs.append(p);forest+=f
    return T(t.op,t.uid,t.typ,tuple(cs),t.meta),forest
def raw(t):return (t.op,t.uid,t.typ,t.meta,tuple(map(raw,t.cs)))
def phi(t):
    out=Counter()
    for roots in antichains(t):
        r,f=extract(t,roots);assert check(r)==check(t)
        out[(tuple(sorted(map(raw,f),key=repr)),nf(r))]+=1
    return out
def forestkey(f):return tuple(sorted(map(raw,f),key=repr))
def delta_forest(f):
    choices=[]
    for tree in f:
        rows=[]
        for roots in antichains(tree):
            r,g=extract(tree,roots)
            rows.append((g,() if r.op=='hole' else (r,)))
        choices.append(rows)
    for selected in product(*choices):
        yield tuple(t for g,h in selected for t in g),tuple(t for g,h in selected for t in h)
def coassoc(t):
    left=Counter();right=Counter()
    for roots in antichains(t):
        residual,f=extract(t,roots)
        for g,h in delta_forest(f):left[(forestkey(g),forestkey(h),raw(residual))]+=1
        for nested in antichains(residual):
            rr,g=extract(residual,nested)
            right[(forestkey(f),forestkey(g),raw(rr))]+=1
    assert left==right,('actual coassociativity',left-right,right-left)
    return sum(left.values())
def obs(t):return ('pure',raw(t)) if pure(t) else ('impure',tuple(sorted(phi(t).items(),key=repr)))
def subst(t,x,p):
    if t.op=='var' and t.uid==x:assert t.typ==p.typ;return p
    assert x not in t.meta,'globally fresh binders required'
    return T(t.op,t.uid,t.typ,tuple(subst(c,x,p) for c in t.cs),t.meta)
def modes(t):
    ats=sorted((x,a) for x,a in check(t).items() if atomic(a))
    rows=[]
    for flags in product((False,True),repeat=len(ats)):
        u=t
        for (x,a),flag in zip(ats,flags):
            if flag:u=subst(u,x,prim(('probe',x),a))
        rows.append((flags,obs(u)))
    return tuple(rows)
def identity(u,p):return app(u+'A',lam(u+'L',u+'x',p.typ,var(u+'x',p.typ)),p)

def main():
    a,b,c='a','b','c';ab=ten(a,b)
    x,y,z=var('x',a),var('y',b),var('z',a)
    v=var('v',ab);d=prim('d',a);e=prim('e',b)
    r=lambda p,q:prim('r',c,p,q)
    fixtures=[]
    # A genuinely mixed exchange: tensor elimination across implication intro.
    body=prim('r',c,x,y,z)
    fixtures.append(('let_lambda',let('L',v,'x','y',lam('F','z',a,body)),lam('F','z',a,let('L',v,'x','y',body)),True))
    # Elimination across both application positions; tensor contains an arrow.
    f=var('f',arr(a,c));w=var('w',ten(arr(a,c),b))
    fun=let('L',w,'f','y',lam('F','z',a,prim('r',c,app('A',f,z),y)))
    fixtures.append(('let_app_function',app('O',fun,d),let('L',w,'f','y',app('O',lam('F','z',a,prim('r',c,app('A',f,z),y)),d)),True))
    g=var('g',arr(c,a));arg=let('L',v,'x','y',r(x,y))
    fixtures.append(('let_app_argument',app('A',g,arg),let('L',v,'x','y',app('A',g,r(x,y))),True))
    # Arrow beta with compound tensor payload, retained logical shell.
    fixtures.append(('compound_beta_pair',app('A',lam('F','v',ab,pair('P',v,prim('k',c))),pair('Q',d,e)),pair('P',pair('Q',d,e),prim('k',c)),True))
    fixtures.append(('mixed_eta',lam('F','v',ab,let('L',v,'x','y',app('A',var('h',arr(ab,c)),pair('P',x,y)))),var('h',arr(ab,c)),True))
    # Explicit mixed principal redex creates a binary material region.
    left=app('A',lam('F','v',ab,let('L',v,'x','y',r(x,y))),pair('P',d,e))
    fixtures.append(('mixed_principal_fusion',left,r(d,e),False))
    # Compound ports remain impure even if their future payload is a pair.
    # Inspect raw islands before ordinary normalization; the reverse order is wrong.
    fixtures.append(('compound_port_raw_barrier',let('L',v,'x','y',r(x,y)),let('L',v,'x','y',r(identity('id',x),y)),True))
    ff=var('ff',arr(a,ab));fd=app('FA',ff,d)
    fixtures.append(('tensor_eta_function_result',let('L',fd,'x','y',pair('P',x,y)),fd,True))
    # Atomic free modes expose a beta reduction that would fuse on a pure fill.
    fixtures.append(('atomic_mode_detects_future_fusion',r(identity('id',x),e),r(x,e),False))
    rows=[];mode_checks=0;substitution_checks=0;cut_checks=0;flag_checks=0
    for name,p,q,equal in fixtures:
        assert check(p)==check(q) and p.typ==q.typ
        assert nf(p)==nf(q),(name,'ordinary equation')
        flag_checks+=coassoc(p)+coassoc(q)
        assert (modes(p)==modes(q))==equal,(name,'material modes')
        mode_checks+=len(modes(p))
        rows.append({'name':name,'ordinary_equal':True,'material_mode_equal':equal,'left_cuts':len(antichains(p)),'right_cuts':len(antichains(q))})
        for roots in antichains(p):
            residual,_=extract(p,roots);check(residual);cut_checks+=1
        if not equal:continue
        # Admitted typed, closed and open compound substitutions.
        for port,ty in check(p).items():
            payloads=[]
            if ty==ab:payloads=[pair('pd',prim('pd0',a),prim('pd1',b)),pair('po',var('pa',a),var('pb',b))]
            if ty==arr(c,a):payloads=[lam('pl','pc',c,prim('pr',a,var('pc',c)))]
            if ty==arr(ab,c):payloads=[lam('pl','pv',ab,let('pe',var('pv',ab),'px','py',prim('pr',c,var('px',a),var('py',b))))]
            if ty==ten(arr(a,c),b):payloads=[pair('pp',lam('pl','pa',a,prim('pr',c,var('pa',a))),prim('pb',b))]
            for payload in payloads:
                for fill in (payload,identity('wrap',payload)):
                    sp,sq=subst(p,port,fill),subst(q,port,fill)
                    assert check(sp)==check(sq) and modes(sp)==modes(sq),(name,port,'substitution')
                    substitution_checks+=1
                    flag_checks+=coassoc(sp)+coassoc(sq)
    # Nonprimitive coefficient is exactly the whole binary region, with full seam.
    delta=phi(r(d,e));old=phi(left);difference=delta-old
    assert sum(difference.values())==1
    assert list(difference)[0][0]==(raw(r(d,e)),)
    assert list(difference)[0][1]==('hole','r',c)
    assert not old-delta
    # Joint compound + atomic substitution, including a nonprimitive payload.
    jp=let('JL',v,'x','y',pair('JP',r(x,y),z))
    jq=pair('JP',let('JL',v,'x','y',r(x,y)),z)
    assert modes(jp)==modes(jq)
    joint=0
    vp=[pair('VP',prim('VS',a,prim('VD',a)),prim('VE',b)),pair('VO',var('VA',a),var('VB',b))]
    zp=[prim('ZD',a),identity('ZI',prim('ZD',a))]
    for pv,pz in product(vp,zp):
        sp=subst(subst(jp,'v',pv),'z',pz);sq=subst(subst(jq,'v',pv),'z',pz)
        assert check(sp)==check(sq) and modes(sp)==modes(sq)
        flag_checks+=coassoc(sp)+coassoc(sq);joint+=1
    malformed=[pair('bad',x,x),lam('bad','x',b,x),prim('bad',arr(a,b)),let('bad',d,'x','y',r(x,y))]
    rejected=0
    for term in malformed:
        try:check(term)
        except (AssertionError,KeyError,IndexError):rejected+=1
    assert rejected==len(malformed)
    out={'status':'PASS','scope':'independently typed unit-free mixed tensor/implication; atomic nondischarging selected primitives; explicit fixture equations only; no normalizer completeness assertion','fixtures':rows,'material_mode_checks':mode_checks,'compound_substitution_checks':substitution_checks,'typed_extraction_checks':cut_checks,'exact_nonprimitive_fusion_defect':True,'actual_nested_flag_terms':flag_checks,'malformed_terms_rejected':rejected,'joint_compound_atomic_substitutions':joint}
    Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
