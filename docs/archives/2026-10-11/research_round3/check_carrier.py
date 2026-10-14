"""Independent finite coefficient-sensitive checks of typed P-tree/CK bridge."""
from functools import lru_cache
from collections import Counter
from itertools import product
import json
E=('edge',)
def node(r,*args): return (r,)+args
def mul(A,B):
    out=Counter()
    for (p,r),v in A.items():
        for (s,t),w in B.items(): out[(p+s,r+t)]+=v*w
    return out
@lru_cache(None)
def dt(t):
    if t==E: return Counter({((E,),(E,)):1})
    out=Counter({((t,),(E,)):1})
    children=Counter({((),()):1})
    for child in t[1:]: children=mul(children,dt(child))
    for (p,rs),v in children.items(): out[(p,(node(t[0],*rs),))]+=v
    return out
@lru_cache(None)
def db(F):
    out=Counter({((),()):1})
    for t in F: out=mul(out,dt(t))
    return out
def q(F): return tuple(t for t in F if t!=E)
@lru_cache(None)
def dh(F):
    out=Counter()
    for (p,r),v in db(F).items():out[(q(p),q(r))]+=v
    return out
@lru_cache(None)
def lam(F):
    out=Counter()
    for (p,r),v in db(F).items():out[(q(p),r)]+=v
    return out
def expand(D, left, right):
    L=Counter();R=Counter()
    for (p,r),v in D.items():
        for (a,b),w in left(p).items():L[(a,b,r)]+=v*w
        for (a,b),w in right(r).items():R[(p,a,b)]+=v*w
    return L,R
@lru_cache(None)
def trees(n):
    if n==0:return (E,)
    out=[]
    if n==1:out.append(node('g'))
    out.extend(node('f',a) for a in trees(n-1))
    for i in range(n):out.extend(node('r',a,b) for a in trees(i) for b in trees(n-1-i))
    return tuple(out)
def material(t): return t==E or (t[0]!='f' and all(material(x) for x in t[1:]))
def rho(F):return Counter({(p,r):v for (p,r),v in lam(F).items() if all(map(material,p))})
def epsB(F):return all(t==E for t in F)
def epsH(F):return not F
samples=[()]
for n in range(5):samples.extend((t,) for t in trees(n))
small=sum((list(trees(n)) for n in range(3)),[])
samples.extend(product(small,repeat=2))
counts=Counter()
for F in samples:
    for name,D,l,r in [('B',db(F),db,db),('H',dh(q(F)),dh,dh),('lambda',lam(F),dh,lam),('material',rho(F),dh,rho)]:
        L,R=expand(D,l,r);assert L==R,(name,F,L-R,R-L);counts[name]+=1
    counit=Counter()
    for (p,r),v in lam(F).items():
        if epsH(p): counit[r]+=v
    assert counit==Counter({F:1})
# Half-erasure is not a coalgebra on B.
def naive(F):
    if F==(E,):return Counter({((E,),(E,)):1})
    return lam(F)
g=node('g');fg=node('f',g);fe=node('f',E)
L,R=expand(naive((fg,)),naive,naive)
assert L-R==Counter({((g,),(E,),(fe,)):1})
assert R-L==Counter({((g,),(),(fe,)):1})
result={'checked_forests':len(samples),'identities':dict(counts),'half_erasure_counterexample':True,'max_positive_tree_vertices':4,'ordered_two_component_forests':len(small)**2}
print(json.dumps(result,indent=2))
