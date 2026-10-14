"""Finite independent cut-vs-graft check of the typed P-tree Green identity.

This is an abstract two-state grammar, not a claimed native proof derivation.
No external packages. Positive-node truncation is only the executable bound.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

# operation -> (output state, ordered input states)
OPS = {
    'a': (0, ()),
    'd': (1, ()),
    'u': (1, (0,)),
    'v': (0, (1,)),
    'b': (0, (1, 0)),
    'c': (1, (1, 1)),
}

def edge(i): return ('edge', i)
def node(op, children=()): return (op, tuple(children))
def output(t): return t[1] if t[0]=='edge' else OPS[t[0]][0]
def children(t): return () if t[0]=='edge' else t[1]
def size(t): return 0 if t[0]=='edge' else 1+sum(map(size, children(t)))
def leaves(t):
    if t[0]=='edge': return (t[1],)
    return sum((leaves(x) for x in children(t)), ())
def forest(xs): return tuple(sorted(xs, key=repr))

@lru_cache(None)
def trees(i, n):
    if n==0: return (edge(i),)
    out=[]
    for op,(j,ins) in OPS.items():
        if i!=j: continue
        for sizes in product(range(n), repeat=len(ins)):
            if sum(sizes)!=n-1: continue
            for cs in product(*(trees(k,m) for k,m in zip(ins,sizes))):
                out.append(node(op,cs))
    return tuple(out)

def cuts(t):
    # Trivial tree has one cut, not separate empty and total cut witnesses.
    if t[0]=='edge': return [((t,), t)]
    out=[((t,), edge(output(t)))]
    for pieces in product(*(cuts(x) for x in children(t))):
        crown=forest(sum((p for p,r in pieces), ()))
        remainder=node(t[0],tuple(r for p,r in pieces))
        out.append((crown,remainder))
    return out

def graft(r, inputs):
    it=iter(inputs)
    def go(t):
        if t[0]=='edge':
            x=next(it)
            assert output(x)==t[1]
            return x
        return node(t[0],tuple(go(x) for x in children(t)))
    ans=go(r)
    assert next(it,None) is None
    return ans

def lhs(N):
    return Counter((p,r) for i in (0,1) for n in range(N+1)
                   for t in trees(i,n) for p,r in cuts(t))

def rhs(N):
    counts=Counter()
    for i in (0,1):
      for n in range(N+1):
       for r in trees(i,n):
        ls=leaves(r)
        for sizes in product(range(N-n+1),repeat=len(ls)):
            if sum(sizes)>N-n: continue
            for ps in product(*(trees(k,m) for k,m in zip(ls,sizes))):
                t=graft(r,ps)
                assert size(t)==n+sum(sizes)
                counts[forest(ps),r]+=1
    return counts

def hc(p): return forest(x for x in p if size(x)>0)
def hc_cuts(t): return [(hc(p),r) for p,r in cuts(t)]

def flags_left(t):
    c=Counter()
    for p,r in hc_cuts(t):
        for pcs in product(*(hc_cuts(x) for x in p)):
            top=forest(sum((p1 for p1,r1 in pcs),()))
            mid=forest(r1 for p1,r1 in pcs if size(r1)>0)
            c[top,mid,r]+=1
    return c

def flags_right(t):
    c=Counter()
    for p,r in hc_cuts(t):
        for p1,r1 in hc_cuts(r):
            c[p,p1,r1]+=1
    return c

def main():
    N=3
    a,b=lhs(N),rhs(N)
    assert a==b, (a-b,b-a)
    allts=[t for i in (0,1) for n in range(N+1) for t in trees(i,n)]
    for t in allts:
        assert flags_left(t)==flags_right(t),t
        if size(t)==0:
            assert hc_cuts(t)==[((),t)]
        else:
            assert ((t,),edge(output(t))) in hc_cuts(t)
    # Closed-input specialization: every crown component must have no leaves.
    closed_lhs=Counter((p,r) for t in allts if not leaves(t) for p,r in cuts(t))
    closed_rhs=Counter({(p,r):v for (p,r),v in b.items()
                        if all(not leaves(t) for t in p)})
    assert closed_lhs==closed_rhs
    result={
      'grammar_states':2,'operation_constructors':len(OPS),'max_positive_nodes':N,
      'trees_including_typed_edges':len(allts),
      'physical_cuts':sum(a.values()),'distinct_crown_remainder_pairs':len(a),
      'full_green_cut_graft_identity':True,
      'quotient_leg_comodule_flag_identity_on_all_trees':True,
      'closed_input_specialization':True,
      'zero_node_states_retained':True,
      'native_proof_claim':False,
    }
    path=Path(__file__).with_name('polynomial_bridge_results.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
