"""Finite signature graph/min-cut checks and actual SELL W/C proof macro checker.
Standard library; no general SELL proof search or typed CK implementation.
"""
from collections import deque, Counter
from dataclasses import dataclass
from itertools import product, combinations
from pathlib import Path
import json

def powerset(xs):
    xs=tuple(xs)
    return tuple(frozenset(c) for n in range(len(xs)+1) for c in combinations(xs,n))
def upward(J,R,W):
    return all(b in W for a,b in R if a in J and b in J and a in W)
def conflicts(I,R,W,C):
    return frozenset(frozenset([a,b]) for a,b in R if a!=b and ((a in W and b not in W) or (a in C and b not in C)))
def independent(J,E): return all(not e<=J for e in E)

def mincut_vocabulary(I,W,E,weights):
    S='SOURCE';T='SINK';nodes=(S,T)+tuple(I)
    cap={u:{v:0 for v in nodes} for u in nodes}
    INF=sum(weights.values())+1
    for i in I:
        if i in W: cap[S][i]=weights[i]
        else: cap[i][T]=weights[i]
    for e in E:
        a=next(iter(e&W)); b=next(iter(e-W)); cap[a][b]=INF
    residual={u:dict(vs) for u,vs in cap.items()};flow=0
    while True:
        parent={S:None};todo=deque([S])
        while todo and T not in parent:
            u=todo.popleft()
            for v in nodes:
                if residual[u][v]>0 and v not in parent: parent[v]=u;todo.append(v)
        if T not in parent: break
        amount=INF;v=T
        while v!=S:
            u=parent[v];amount=min(amount,residual[u][v]);v=u
        v=T
        while v!=S:
            u=parent[v];residual[u][v]-=amount;residual[v][u]+=amount;v=u
        flow+=amount
    reachable=set(parent)
    cover=(set(W)-reachable)|((set(I)-set(W))&reachable)
    retained=frozenset(set(I)-cover)
    assert independent(retained,E)
    assert sum(weights[i] for i in cover)==flow
    return retained,flow

def graph_checks():
    I=(0,1,2);states=powerset(I);off=[(a,b) for a in I for b in I if a!=b]
    preorders=[]
    for bits in product((0,1),repeat=len(off)):
        R={(a,a) for a in I}|{edge for edge,on in zip(off,bits) if on}
        if all((a,c) in R for a,b in R for b2,c in R if b==b2):preorders.append(R)
    checks=0
    for R in preorders:
        for W,C in product(states,repeat=2):
            E=conflicts(I,R,W,C)
            for J in states:
                assert independent(J,E)==(upward(J,R,W) and upward(J,R,C));checks+=1
    weights_list=[dict(zip(I,w)) for w in [(1,1,1),(2,5,3),(0,4,1)]]
    mincuts=0;unequal=0
    for R in preorders:
        for W in states:
            E=conflicts(I,R,W,frozenset())
            for weights in weights_list:
                retained,cut=mincut_vocabulary(I,W,E,weights)
                candidates=[J for J in states if upward(J,R,W)]
                optimal=max(sum(weights[i] for i in J) for J in candidates)
                assert sum(weights[i] for i in retained)==optimal
                mincuts+=1
    # Chain preorder restricted to endpoints must keep inherited relation 0<=2.
    R={(0,0),(1,1),(2,2),(0,1),(1,2),(0,2)};J=frozenset([0,2]);W=frozenset([0])
    assert not upward(J,R,W)
    assert not independent(J,conflicts(I,R,W,frozenset()))
    # Cardinality versus weights: star centre1 in W, leaves0,2 outside W.
    R={(0,0),(1,1),(2,2),(1,0),(1,2)};W=frozenset([1]);E=conflicts(I,R,W,frozenset())
    retained,cost=mincut_vocabulary(I,W,E,{0:1,1:10,2:1})
    assert retained==frozenset([1]) and cost==2
    return {'preorders_on_three_labels':len(preorders),'signature_subset_checks':checks,
            'weighted_mincut_vs_exhaustive_checks':mincuts,'zero_weight_cases_included':True,
            'inherited_endpoint_order_counterexample_checked':True,
            'weighted_star_retains':sorted(retained),'weighted_star_deleted_cost':cost}

# Actual proof terms for the intuitionistic multiplicative subexponential fragment.
def at(s):return ('atom',s)
def bang(i,a):return ('bang',i,a)
def tensor(a,b):return ('tensor',a,b)
def ctx(xs):return tuple(sorted(xs,key=repr))
def minus(g,i):return g[:i]+g[i+1:]
@dataclass(frozen=True)
class Proof:
    rule:str
    g:tuple
    c:tuple
    kids:tuple=()
    pos:object=None

class Checker:
    def __init__(self,R,W,C):self.R=set(R);self.W=set(W);self.C=set(C)
    def check(self,p):
        assert p.g==ctx(p.g)
        for q in p.kids:self.check(q)
        g,c,k=p.g,p.c,p.kids
        if p.rule=='id':assert g==(c,) and not k
        elif p.rule=='g':assert g==(at('p'),) and c==at('p') and not k
        elif p.rule=='oneR':assert not g and c==('one',) and not k
        elif p.rule=='oneL':
            assert len(k)==1 and g[p.pos]==('one',) and k[0].g==minus(g,p.pos) and k[0].c==c
        elif p.rule=='tR':
            assert c[0]=='tensor' and len(k)==2 and k[0].c==c[1] and k[1].c==c[2] and g==ctx(k[0].g+k[1].g)
        elif p.rule=='tL':
            a=g[p.pos];assert a[0]=='tensor' and len(k)==1
            assert k[0].g==ctx(minus(g,p.pos)+(a[1],a[2])) and k[0].c==c
        elif p.rule=='derL':
            a=g[p.pos];assert a[0]=='bang' and len(k)==1
            assert k[0].g==ctx(minus(g,p.pos)+(a[2],)) and k[0].c==c
        elif p.rule=='prom':
            assert c[0]=='bang' and len(k)==1 and k[0].g==g and k[0].c==c[2]
            assert all(a[0]=='bang' and (c[1],a[1]) in self.R for a in g)
        elif p.rule=='W':
            a=g[p.pos];assert a[0]=='bang' and a[1] in self.W and len(k)==1
            assert k[0].g==minus(g,p.pos) and k[0].c==c
        elif p.rule=='C':
            a=g[p.pos];assert a[0]=='bang' and a[1] in self.C and len(k)==1
            assert k[0].g==ctx(g+(a,)) and k[0].c==c
        elif p.rule=='cut':
            assert len(k)==2 and k[0].c==k[1].g[p.pos] and c==k[1].c
            assert g==ctx(k[0].g+minus(k[1].g,p.pos))
        else:raise AssertionError(p.rule)
        return True

def ident(a):return Proof('id',(a,),a)
def wrap(p,a,i):
    j=p.g.index(a);g=ctx(minus(p.g,j)+(bang(i,a),));j=g.index(bang(i,a))
    return Proof('derL',g,p.c,(p,),j)
def weaken(p,i,a):
    g=ctx(p.g+(bang(i,a),));return Proof('W',g,p.c,(p,),g.index(bang(i,a)))
def contract(p,i,a):
    A=bang(i,a);j=p.g.index(A);g=minus(p.g,j)
    assert A in g
    return Proof('C',g,p.c,(p,),g.index(A))
def promote(p,i):return Proof('prom',p.g,bang(i,p.c),(p,))
def cut(p,q):
    j=q.g.index(p.c);return Proof('cut',ctx(p.g+minus(q.g,j)),q.c,(p,q),j)
def pair(p,q):return Proof('tR',ctx(p.g+q.g),tensor(p.c,q.c),(p,q))
def count_rule(p,r):return (p.rule==r)+sum(count_rule(q,r) for q in p.kids)
def count_object(p,target):return (p is target)+sum(count_object(q,target) for q in p.kids)
def nodes(p):return 1+sum(nodes(q) for q in p.kids)
def reject(checker,p):
    try:checker.check(p)
    except AssertionError:return
    raise AssertionError('illegal proof accepted')

def derive_wb(p,A):
    # !b A |- !a A, then old Wa and one Cut.
    coercion=promote(wrap(ident(A),A,'b'),'a')
    return cut(coercion,weaken(p,'a',A))
def derive_cb(p,A):
    # Preserve the arbitrary original premise once; wrap both displayed !b A occurrences.
    B=bang('b',A)
    wrapped=wrap(wrap(p,B,'a'),B,'a')
    contracted=contract(wrapped,'a',B)
    provider=promote(ident(B),'a')
    return cut(provider,contracted)

def modal_to_p(A,material=False):
    if A==at('p'):return Proof('g',(A,),A) if material else ident(A)
    assert A[0]=='bang'
    return wrap(modal_to_p(A[2],material),A[2],A[1])

def proof_checks():
    R={('a','a'),('b','b'),('a','b')}
    raw=Checker(R,{'a'},{'a'});repaired=Checker(R,{'a','b'},{'a','b'})
    outcomes=[]
    for A in [at('p'),bang('b',at('p'))]:
        # W premise has one distinguished material leaf.
        p=Proof('g',(at('p'),),at('p'));direct=weaken(p,'b',A);macro=derive_wb(p,A)
        assert repaired.check(direct);reject(raw,direct);assert raw.check(macro)
        assert (macro.g,macro.c)==(direct.g,direct.c)
        assert count_rule(macro,'g')==1 and count_object(macro,p)==1
        outcomes.append({'macro':'Wb','A':repr(A),'nodes':nodes(macro),'material_g':count_rule(macro,'g'),'premise_occurrences':count_object(macro,p)})
        # C premise has a genuine side context q, two resource occurrences, but one proof subtree.
        B=bang('b',A)
        p=pair(ident(at('q')),pair(modal_to_p(B,True),modal_to_p(B,False)))
        assert raw.check(p)
        direct=contract(p,'b',A);macro=derive_cb(p,A)
        assert repaired.check(direct);reject(raw,direct);assert raw.check(macro)
        assert (macro.g,macro.c)==(direct.g,direct.c)
        assert count_rule(macro,'g')==1 and count_object(macro,p)==1
        # Nested !a(!b A) is a real checked cut formula in the macro.
        assert macro.kids[0].c==bang('a',B)
        outcomes.append({'macro':'Cb','A':repr(A),'nodes':nodes(macro),'material_g':count_rule(macro,'g'),'premise_occurrences':count_object(macro,p),'cut_formula':repr(macro.kids[0].c)})
    # Reversed order must not accidentally pass the promotion side-condition check.
    invalid=promote(wrap(ident(at('p')),at('p'),'a'),'b');reject(raw,invalid)
    return outcomes

if __name__=='__main__':
    result={'graph':graph_checks(),'proof_macros':proof_checks()}
    Path(__file__).with_name('sell_test_results.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
