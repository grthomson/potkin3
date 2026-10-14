"""Independent exact finite recognizer of the inverse typed material coaction.
Edge sources remain edges; only positive pure trees contribute one coefficient
component. No independent gap insertions or identification edge=forest unit.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from collections import Counter
import json

@dataclass(frozen=True)
class Edge:
    sort:str
@dataclass(frozen=True)
class N:
    rule:str
    children:tuple=()
# name: (input sorts, output sort, is material)
RULES={'a':((),'P',True),'g':(('P',),'P',True),
       'f':(('P',),'P',False),'m':(('P','P'),'P',True),
       'z':((),'Q',True),'lift':(('P',),'Q',True)}
CAP=2

def sort(t): return t.sort if isinstance(t,Edge) else RULES[t.rule][1]
def pure(t): return isinstance(t,Edge) or (RULES[t.rule][2] and all(map(pure,t.children)))
def obs_rule(r,qs):
    height=max((q[0] for q in qs),default=0)
    return min(CAP,height+(r=='g')),all(q[1] for q in qs)
@lru_cache(None)
def obs(t):
    if isinstance(t,Edge): return 0,False
    assert tuple(map(sort,t.children))==RULES[t.rule][0]
    return obs_rule(t.rule,tuple(map(obs,t.children)))

def mul(A,B):
    out=Counter()
    for (p,r),v in A.items():
        for (s,t),w in B.items():out[p+s,r+t]+=v*w
    return out
@lru_cache(None)
def coact_tree(t):
    if isinstance(t,Edge): return Counter({((),(t,)):1})
    out=Counter()
    if pure(t):out[((t,),(Edge(sort(t)),))]+=1
    below=Counter({((),()):1})
    for child in t.children:below=mul(below,coact_tree(child))
    for (p,rs),v in below.items():out[p,(N(t.rule,rs),)]+=v
    return out
@lru_cache(None)
def coact(F):
    out=Counter({((),()):1})
    for t in F:out=mul(out,coact_tree(t))
    return out

# Provider policy: every actual positive extracted tree has g-height <=1.
STATES=(0,1)
def step(u,tq):return int(bool(u or tq[1][0]>1))

def saturation():
    # Sources include edges, but positive witness map never includes them.
    allw={s:{(0,False):Edge(s)} for s in ('P','Q')}
    pos={s:{} for s in allw}
    rounds=0
    while True:
        changed=False
        for r,(ins,s,material) in RULES.items():
            if not material:continue
            for qs in product(*(tuple(allw[a]) for a in ins)):
                q=obs_rule(r,qs)
                t=N(r,tuple(allw[a][b] for a,b in zip(ins,qs)))
                if q not in pos[s]:pos[s][q]=t;changed=True
                if q not in allw[s]:allw[s][q]=t;changed=True
        rounds+=1
        if not changed:return pos,rounds
POS,ROUNDS=saturation()

@lru_cache(None)
def inverse(t):
    """Map relation triples to (actual material tuple, source tree) witnesses."""
    if isinstance(t,Edge):
        out={(u,(0,False),u):((),t) for u in STATES}
        for q,p in POS[t.sort].items():
            for u in STATES:out[(u,q,step(u,(t.sort,q)))]=((p,),p)
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
        for (final,qs),(ps,ss) in acc.items():
            out[initial,obs_rule(t.rule,qs),final]=(ps,N(t.rule,ss))
    return out


def inverse_forest(F):
    # q aggregates maximum ancestry height and complete-all-roots flag.
    out={}
    for initial in STATES:
        acc={(initial,0,True):((),())}
        for root in F:
            nxt={}
            for (u,h,c),(ps,ss) in acc.items():
                for (v,q,w),(p,s) in inverse(root).items():
                    if u==v:nxt[w,max(h,q[0]),c and q[1]]=(ps+p,ss+(s,))
            acc=nxt
        for (v,h,c),witness in acc.items():out[initial,(h,c),v]=witness
    return out


def universal(F,complete_only=True):
    return not any(u==0 and v==0 and (q[1] or not complete_only) and q[0]>1
                   for u,q,v in inverse_forest(F))
def feasible(F):return any(u==v==0 and q[1] for u,q,v in inverse_forest(F))

@lru_cache(None)
def trees(s,n):
    if n==0:return (Edge(s),)
    out=[]
    def compositions(total,k):
        if k==0:
            if total==0:yield ()
            return
        for z in range(total+1):
            for zs in compositions(total-z,k-1):yield (z,)+zs
    for r,(ins,dest,_) in RULES.items():
        if dest!=s:continue
        for ns in compositions(n-1,len(ins)):
            for cs in product(*(trees(a,z) for a,z in zip(ins,ns))):out.append(N(r,cs))
    return tuple(out)


def check():
    sources=[()]
    for s in ('P','Q'):
        sources.extend((t,) for n in range(4) for t in trees(s,n))
    small=[t for n in range(2) for t in trees('P',n)]
    sources.extend(product(small,repeat=2))
    terms=0;remaining=set();witness_checks=0
    for source in sources:
        for (material,R),multiplicity in coact(source).items():
            terms+=1;remaining.add(R)
            assert len(R)==len(source)
            assert all(not isinstance(p,Edge) and pure(p) for p in material)
            u=0
            for p in material:u=step(u,(sort(p),obs(p)))
            q=max((obs(t)[0] for t in source),default=0),all(obs(t)[1] for t in source)
            assert (0,q,u) in inverse_forest(R)
    for R in remaining:
        for (u,q,v),(material,source) in inverse_forest(R).items():
            witness_checks+=1
            assert coact(source)[material,R]>0
            actual=u
            for p in material:actual=step(actual,(sort(p),obs(p)))
            assert actual==v
            assert q==(max((obs(t)[0] for t in source),default=0),all(obs(t)[1] for t in source))
    e=Edge('P')
    assert inverse_forest(())!={k:v for k,v in inverse_forest((e,)).items()}
    assert coact(())==Counter({((),()):1})
    assert coact((e,))==Counter({((),(e,)):1})
    assert feasible((e,)) and universal((e,))
    # An anchored g can receive another g below it: actual positive source,
    # with a accepted coefficient, violates height1.
    R=(N('g',(e,)),)
    assert feasible(R) and not universal(R)
    bad=next((p,s) for (u,q,v),(p,s) in inverse_forest(R).items() if u==v==0 and q[1] and q[0]>1)
    assert coact(bad[1])[bad[0],R]>0
    # Pure OPEN source components really occur and cannot be discarded.
    openp=N('m',(e,e))
    assert coact((openp,))[((openp,),(e,))]==1
    assert (0,(0,False),0) in inverse(e)
    result={'sources_checked':len(sources),'coaction_terms_checked':terms,
            'distinct_remainder_forests':len(remaining),'inverse_witnesses_checked':witness_checks,
            'positive_pure_observer_states':{s:len(w) for s,w in POS.items()},
            'saturation_rounds':ROUNDS,'root_counts_preserved':True,
            'typed_edge_not_forest_unit':True,'positive_open_coefficients_retained':True,
            'complete_source_restriction':'regular implication: not complete OR safe',
            'scope':'Exact finite witness-state saturation; bounded forward sources to three vertices plus two-component forests. No coefficient quotient claimed.'}
    with open('research_round3/typed_coaction_inverse_results.json','w') as f:json.dump(result,f,indent=2)
    print(json.dumps(result,indent=2))

if __name__=='__main__':check()
