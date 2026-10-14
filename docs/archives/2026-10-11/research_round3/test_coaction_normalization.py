"""Integration gate: actual typed coaction inverse + normal-form budget.

Uses the independently implemented occurrence-level coaction, including open
positive providers and edge identities. Closed-source guard is explicit.
"""
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import typed_coaction_inverse as ck
from check_natural_demand import A,G,M,B,L,V,typ,P,Bang,normal,gcount

ck.RULES = {
    'aC':((),'C',True), 'gC':(('C',),'C',True),
    'mC':(('C','C'),'C',True), 'bang':(('C',),'B',True),
    'let':(('B','O'),'C',True), 'aO':((),'O',True),
    'x':((),'O',True), 'gO':(('O',),'O',True),
    'mO':(('O','O'),'O',True)}
for fn in (ck.coact_tree,ck.coact,ck.trees): fn.cache_clear()
N,E=ck.N,ck.Edge
CAP=3
def transition(r,qs):
    complete=all(q[2] for q in qs)
    if r in ('aC','aO'): c,d=0,0
    elif r=='x': c,d=0,1
    elif r.startswith('g'): c,d=qs[0][0]+1,qs[0][1]
    elif r.startswith('m'): c,d=qs[0][0]+qs[1][0],qs[0][1]+qs[1][1]
    elif r=='bang': c,d=qs[0][:2]
    elif r=='let': c,d=qs[1][0]+qs[1][1]*qs[0][0],0
    else: raise ValueError(r)
    return min(c,CAP),min(d,CAP),complete
@lru_cache(None)
def obs(t):
    if isinstance(t,E): return 0,0,False
    return transition(t.rule,tuple(obs(k) for k in t.children))
def term(t):
    if isinstance(t,E): raise ValueError('open metahole')
    r=t.rule; cs=t.children
    if r in ('aC','aO'): return A()
    if r=='x': return V('x')
    if r.startswith('g'): return G(term(cs[0]))
    if r.startswith('m'): return M(term(cs[0]),term(cs[1]))
    if r=='bang': return B(term(cs[0]))
    if r=='let': return L('x',term(cs[0]),term(cs[1]))
    raise ValueError(r)
def saturation():
    allw={s:{(0,0,False):E(s)} for s in ('C','B','O')}
    pos={s:{} for s in allw}; rounds=0
    while True:
        changed=False
        for r,(ins,s,_) in ck.RULES.items():
            for qs in product(*(tuple(allw[a]) for a in ins)):
                q=transition(r,qs)
                t=N(r,tuple(allw[a][b] for a,b in zip(ins,qs)))
                if q not in pos[s]:pos[s][q]=t;changed=True
                if q not in allw[s]:allw[s][q]=t;changed=True
        rounds+=1
        if not changed:return pos,rounds
POS,ROUNDS=saturation()
# DFA accepts a B provider then an O consumer subject to the full joint budget.
# States: initial0, producer-cost states1..4, accepting5, rejecting6.
STATES=range(7)
def step(u,s,q):
    if u==0 and s=='B': return 1+q[0]
    if 1<=u<=4 and s=='O': return 5 if q[0]+q[1]*(u-1)<=2 else 6
    return 6
@lru_cache(None)
def inverse(t):
    if isinstance(t,E):
        out={(u,(0,0,False),u):((),t) for u in STATES}
        for q,p in POS[t.sort].items():
            for u in STATES:out[u,q,step(u,t.sort,q)]=((p,),p)
        return out
    out={}
    for initial in STATES:
        acc={(initial,()):((),())}
        for child in t.children:
            nxt={}
            for (u,qs),(ps,ss) in acc.items():
                for (v,q,w),(p,s) in inverse(child).items():
                    if u==v:nxt[w,qs+(q,)]=(ps+p,ss+(s,))
            acc=nxt
        for (last,qs),(ps,ss) in acc.items():
            out[initial,transition(t.rule,qs),last]=(ps,N(t.rule,ss))
    return out
def safe(r):
    # Full coaction residual of C = not-complete OR normalized-cost<=2.
    return not any(u==0 and v==5 and q[2] and q[0]>2 for u,q,v in inverse(r))
def feasible(r):return any(u==0 and v==5 and q[2] for u,q,v in inverse(r))
def exact_frontier(t,r):
    """Independently validate one cut by its retained address skeleton.

    This avoids enumerating exponentially many unrelated cuts of synthesized
    large witnesses. Bounded forward sources still use the full coproduct.
    """
    assert ck.sort(t)==ck.sort(r)
    if isinstance(r,E):
        return () if isinstance(t,E) else (t,)
    assert isinstance(t,N) and t.rule==r.rule and len(t.children)==len(r.children)
    return tuple(p for a,b in zip(t.children,r.children) for p in exact_frontier(a,b))
def check():
    sources=[t for s in ('C','B','O') for n in range(5) for t in ck.trees(s,n)]
    remainder=set();forward=0
    for t in sources:
        for (ps,(r,)),coefficient in ck.coact((t,)).items():
            u=0
            for p in ps:u=step(u,ck.sort(p),obs(p))
            assert (0,obs(t),u) in inverse(r)
            remainder.add(r);forward+=1
    checks=0;complete=0
    for r in remainder:
        for (u,q,v),(ps,t) in inverse(r).items():
            assert exact_frontier(t,r)==ps and all(ck.pure(p) for p in ps)
            actual=u
            for p in ps:actual=step(actual,ck.sort(p),obs(p))
            assert actual==v and obs(t)==q
            checks+=1
            if q[2]:
                env={} if ck.sort(t)!='O' else {'x':A()}
                assert min(gcount(normal(term(t),env)),CAP)==q[0]
                complete+=1
    r=N('let',(E('B'),E('O')))
    bad=N('gC',(r,))
    assert safe(r) and feasible(r) and not safe(bad) and feasible(bad)
    ps,t=next(w for (u,q,v),w in inverse(bad).items() if u==0 and v==5 and q[2] and q[0]>2)
    assert typ(term(t),{})==P and gcount(normal(term(t),{}))==3
    assert ck.coact((t,))[ps,(bad,)]==1
    result={'source_trees':len(sources),'forward_coaction_terms':forward,
            'inverse_coaction_witness_checks':checks,'complete_witness_normalizations':complete,
            'positive_open_and_complete_states':{s:len(v) for s,v in POS.items()},
            'saturation_rounds':ROUNDS,'actual_coaction_budget_nonvacuous':True,
            'actual_coaction_counterexample_normal_form_cost':3,
            'scope':'Actual typed coaction with positive open providers; complete-source implication guard. Finite-registry paper theorem plus bounded forward and exact-state witness checks.'}
    Path(__file__).with_name('coaction_normalization_results.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
if __name__=='__main__':check()
