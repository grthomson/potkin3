"""Typed positive exponential terms: exact normal-form material demand.

No higher-order functions, tensor elimination, recursion, or runtime claim.
The independent evaluator produces normal forms; demand never calls it.
"""
from collections import Counter
from itertools import product
import json, random
from pathlib import Path

P = ('p',)
def Bang(a): return ('!', a)
def Pair(a,b): return ('*',a,b)
def V(x): return ('var',x)
def A(): return ('a',)
def G(t): return ('g',t)
def B(t): return ('bang',t)
def T(t,u): return ('pair',t,u)
def M(t,u): return ('merge',t,u)
def L(x,p,q): return ('let',x,p,q)

def typ(t,env):
    op=t[0]
    if op=='a': return P
    if op=='var': return env[t[1]]
    if op=='g':
        assert typ(t[1],env)==P
        return P
    if op=='bang': return Bang(typ(t[1],env))
    if op=='pair': return Pair(typ(t[1],env),typ(t[2],env))
    if op=='merge':
        assert typ(t[1],env)==typ(t[2],env)==P
        return P
    if op=='let':
        assert t[1] not in env, 'fresh binder required'
        a=typ(t[2],env)
        assert a[0]=='!'
        return typ(t[3],{**env,t[1]:a[1]})
    raise ValueError(op)

def normal(t,env):
    op=t[0]
    if op=='a': return t
    if op=='var': return env[t[1]]
    if op=='g': return G(normal(t[1],env))
    if op=='bang': return B(normal(t[1],env))
    if op=='pair': return T(normal(t[1],env),normal(t[2],env))
    if op=='merge': return M(normal(t[1],env),normal(t[2],env))
    if op=='let':
        v=normal(t[2],env)
        assert v[0]=='bang', 'typed closed canonical forms'
        return normal(t[3],{**env,t[1]:v[1]})
    raise ValueError(op)

def gcount(v):
    if v[0]=='a': return 0
    if v[0]=='g': return 1+gcount(v[1])
    if v[0]=='bang': return gcount(v[1])
    if v[0] in ('pair','merge'): return gcount(v[1])+gcount(v[2])
    raise ValueError('not a closed normal value')

def demand(t,cap=None,holes=None):
    clip=(lambda n:n) if cap is None else (lambda n:min(n,cap))
    op=t[0]
    if op=='hole': return holes[t[1]]
    if op=='a': return 0,Counter()
    if op=='var': return 0,Counter({t[1]:1})
    if op=='g':
        c,d=demand(t[1],cap,holes); return clip(c+1),d
    if op=='bang': return demand(t[1],cap,holes)
    if op in ('pair','merge'):
        c,d=demand(t[1],cap,holes); e,f=demand(t[2],cap,holes)
        return clip(c+e),Counter({x:clip(d[x]+f[x]) for x in d.keys()|f.keys()})
    if op=='let':
        c,d=demand(t[2],cap,holes); e,f=demand(t[3],cap,holes)
        n=f[t[1]]
        return clip(e+n*c),Counter({x:clip(f[x]+n*d[x]) for x in d.keys()|f.keys() if x!=t[1]})
    raise ValueError(op)

def ncost(t,values):
    c,d=demand(t)
    return c+sum(n*gcount(values[x]) for x,n in d.items())

def closed(a,n):
    if a==P:
        t=A()
        for _ in range(n): t=G(t)
        return t
    if a[0]=='!': return B(closed(a[1],n))
    return T(closed(a[1],n),closed(a[2],n+1))

rng=random.Random(110326)
serial=0
def gen(a,env,depth):
    global serial
    options=['constructor']+[('var',x) for x,b in env.items() if b==a]
    if depth>0: options+=['let','let']+(['g','merge'] if a==P else [])
    pick=rng.choice(options)
    if isinstance(pick,tuple): return V(pick[1])
    if pick=='g': return G(gen(P,env,depth-1))
    if pick=='merge': return M(gen(P,env,depth-1),gen(P,env,depth-1))
    if pick=='let':
        serial+=1; x='v'+str(serial)
        b=rng.choice([P,Bang(P),Pair(P,P)])
        provider=gen(Bang(b),env,depth-1)
        body=gen(a,{**env,x:b},depth-1)
        return L(x,provider,body)
    if a==P: return A()
    if a[0]=='!': return B(gen(a[1],env,max(0,depth-1)))
    return T(gen(a[1],env,max(0,depth-1)),gen(a[2],env,max(0,depth-1)))


def split_random(t,payloads,prob=.25):
    # Selecting a node swallows the entire subtree, hence exactly antichain cuts.
    if rng.random()<prob:
        i=len(payloads);payloads[i]=t;return ('hole',i)
    op=t[0]
    if op in ('a','var'): return t
    if op=='let': return L(t[1],split_random(t[2],payloads,prob),split_random(t[3],payloads,prob))
    return (op,*(split_random(u,payloads,prob) for u in t[1:]))

def main():
    checks=0
    frontier_checks=0
    env={'x':P,'y':Bang(P),'z':Pair(P,P)}
    vals={x:closed(a,i+1) for i,(x,a) in enumerate(env.items())}
    for _ in range(1000):
        a=rng.choice([P,Bang(P),Pair(P,P),Bang(Pair(P,P))])
        t=gen(a,env,4)
        assert typ(t,env)==a
        nf=normal(t,vals)
        assert typ(nf,{})==a
        assert gcount(nf)==ncost(t,vals)
        c,d=demand(t)
        for _ in range(3):
            payloads={}; skeleton=split_random(t,payloads)
            summaries={i:demand(u) for i,u in payloads.items()}
            assert demand(skeleton,holes=summaries)==(c,d)
            # One more complete decomposition inside every extracted payload.
            staged={}
            for i,u in payloads.items():
                inner={};remainder=split_random(u,inner)
                staged[i]=demand(remainder,holes={j:demand(v) for j,v in inner.items()})
            assert demand(skeleton,holes=staged)==(c,d)
            frontier_checks+=1
        for cap in range(1,7):
            e,f=demand(t,cap)
            assert e==min(c,cap)
            assert all(f[x]==min(d[x],cap) for x in env)
            calculated=min(e+sum(f[x]*min(gcount(vals[x]),cap) for x in env),cap)
            assert calculated==min(gcount(nf),cap)
            checks+=1
    # Concrete antichain holes: provider and consumer of the same let.
    consumers=[V('x'),G(V('x')),A(),G(A()),T(V('x'),V('x')),T(V('x'),G(A()))]
    joints=0
    for n,q in product(range(8),consumers):
        p=B(closed(P,n)); t=L('x',p,q)
        typ(t,{})
        cq,dq=demand(q)
        assert gcount(normal(t,{}))==cq+dq['x']*n
        joints+=1
    # Same material/rule histogram, different binder incidence and cost.
    left=L('x',B(G(A())),T(V('x'),L('y',B(A()),V('y'))))
    right=L('x',B(G(A())),L('y',B(A()),T(V('y'),V('y'))))
    assert typ(left,{})==typ(right,{})==Pair(P,P)
    assert gcount(normal(left,{}))==1 and gcount(normal(right,{}))==0
    def hist(t):
        c=Counter({t[0]:1})
        children=t[2:] if t[0]=='let' else t[1:]
        for u in children:
            if isinstance(u,tuple): c.update(hist(u))
        return c
    assert hist(left)==hist(right)
    # Overflow may be wholly erased by a zero-demand body.
    erased=L('x',B(closed(P,20)),A())
    assert demand(erased,2)[0]==0
    # Let body scalar alone does not determine its provider demand.
    q1=T(V('x'),V('x')); q2=T(A(),A())
    assert demand(q1)[0]==demand(q2)[0]==0
    assert gcount(normal(L('x',B(G(A())),q1),{}))==2
    assert gcount(normal(L('x',B(G(A())),q2),{}))==0
    # Unbounded amplification with fixed p/!p sorts and one local variable.
    dup=M(V('x'),V('x'))
    ampl=G(A())
    for _ in range(7): ampl=L('x',B(ampl),dup)
    assert typ(ampl,{})==P
    assert gcount(normal(ampl,{}))==128
    assert demand(ampl,4)[0]==4
    # Nested normalization has multiplicative demand: 2 then 2.
    inner=L('x',B(G(A())),T(V('x'),V('x')))
    nested=L('y',B(inner),T(V('y'),V('y')))
    assert gcount(normal(nested,{}))==4
    result={'seed':110326,'typed_normalization_comparisons':1000,
            'clipped_semiring_comparisons':checks,'antichain_and_staged_contracts':frontier_checks,'joint_cut_contracts':joints,
            'same_histogram_costs':[1,0],'scalar_summary_counterexample':[2,0],
            'nested_duplication_cost':4,'fixed_type_seven_level_duplication':128,'overflow_erasure_cost':0}
    Path('research_round3/natural_demand_results.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
