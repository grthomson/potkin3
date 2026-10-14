"""Independent finite checks of physical-hole, scope-aware CK transfer laws.

The universal argument is the cut-address bijection, not these tests.
Only Python's standard library is used. A polynomial's variables are named.
"""
from collections import Counter
from dataclasses import dataclass
from itertools import product
from math import comb
import json

def clean(p): return Counter({m:c for m,c in p.items() if c})
def const(n): return Counter({():n}) if n else Counter()
def variable(x): return Counter({((x,1),):1})
def add(p,q):
    r=p.copy()
    for m,c in q.items():r[m]+=c
    return clean(r)
def mul(p,q):
    r=Counter()
    for m,a in p.items():
        for n,b in q.items():
            powers=Counter(dict(m));powers.update(dict(n))
            r[tuple(sorted(powers.items()))]+=a*b
    return clean(r)
def power(p,k):
    r=const(1)
    for _ in range(k):r=mul(r,p)
    return r
def subst(p,values):
    r=const(0)
    for m,c in p.items():
        t=const(c)
        for x,k in m:t=mul(t,power(values.get(x,variable(x)),k))
        r=add(r,t)
    return r
def hasse(p,x,k):
    r=Counter()
    for m,c in p.items():
        d=dict(m);n=d.get(x,0)
        if n<k:continue
        if n==k:d.pop(x,None)
        else:d[x]=n-k
        r[tuple(sorted(d.items()))]+=c*comb(n,k)
    return clean(r)

@dataclass(frozen=True)
class Tree:
    op:str
    kids:tuple=()
    name:str=''
def leaf(x):return Tree('var',(),x)
def hole(x):return Tree('hole',(),x)
def pair(a,b):return Tree('pair',(a,b))
def lam(x,a):return Tree('lam',(a,),x)
def chan(x,a):return Tree('chan',(a,),x)
def signature(t,hole_sigs):
    if t.op=='hole':return hole_sigs[t.name]
    if t.op=='var':return frozenset([t.name])
    s=frozenset().union(*(signature(k,hole_sigs) for k in t.kids))
    if t.op=='chan':s=s|{t.name}
    return s-{t.name} if t.op=='lam' else s
def compile_context(t,hole_sigs):
    if t.op=='hole':return variable(t.name)
    root=variable('z') if 'b' in signature(t,hole_sigs) else const(1)
    children=const(1)
    for k in t.kids:children=mul(children,compile_context(k,hole_sigs))
    return add(root,children)
def fill(t,payloads):
    if t.op=='hole':return payloads[t.name]
    return Tree(t.op,tuple(fill(k,payloads) for k in t.kids),t.name)
def all_trees(n):
    if n==1:return [leaf('g'),leaf('b'),hole('X')]
    ans=[lam('b',t) for t in all_trees(n-1)]
    ans += [chan('b',t) for t in all_trees(n-1)]
    for i in range(1,n-1):
        ans.extend(pair(a,b) for a in all_trees(i) for b in all_trees(n-i-1))
    return ans
def physical_holes(t,counter=None):
    counter=[0] if counter is None else counter
    if t.op=='hole':
        name='X'+str(counter[0]);counter[0]+=1
        return hole(name)
    return Tree(t.op,tuple(physical_holes(k,counter) for k in t.kids),t.name)
def hole_names(t):
    return ([t.name] if t.op=='hole' else [])+sum((hole_names(k) for k in t.kids),[])

payloads=[leaf('g'),leaf('b'),chan('b',leaf('y')),lam('b',leaf('b'))]
checks=0;multiaffine=0
for n in range(1,6):
    for t0 in all_trees(n):
        t=physical_holes(t0);hs=hole_names(t)
        if not hs:continue
        for choices in product(payloads,repeat=len(hs)):
            ps=dict(zip(hs,choices));sigs={h:signature(p,{}) for h,p in ps.items()}
            f=compile_context(t,sigs)
            assert all(dict(m).get(h,0)<=1 for m in f for h in hs)
            multiaffine+=1
            rhs=subst(f,{h:compile_context(p,{}) for h,p in ps.items()})
            assert rhs==compile_context(fill(t,ps),{})
            checks+=1

# Two-layer installation with masking and a binding root. Distinct physical
# holes may have equal providers without identifying their cut choices.
C=pair(hole('X'),lam('b',hole('Y')))
D={'X':pair(hole('L'),hole('R')),'Y':chan('b',hole('S'))}
Ps={'L':chan('b',leaf('v')),'R':chan('b',leaf('v')),'S':leaf('b')}
filled_D={h:fill(t,Ps) for h,t in D.items()}
outer=compile_context(C,{h:signature(t,{}) for h,t in filled_D.items()})
staged=subst(outer,{h:compile_context(t,{}) for h,t in filled_D.items()})
flat=fill(C,D)
flatF=compile_context(flat,{h:signature(t,{}) for h,t in Ps.items()})
assert staged==subst(flatF,{h:compile_context(t,{}) for h,t in Ps.items()})
assert staged==compile_context(fill(flat,Ps),{})

# Integer Hasse chain rule: coefficient of epsilon^n, including copying.
def uni(coeffs):
    return clean(Counter({(('x',i),) if i else ():c for i,c in enumerate(coeffs)}))
small=[uni(c) for c in product(range(2),repeat=4)]
chain_checks=0
for f in small:
    for g in small:
        fg=subst(f,{'x':g})
        dG=add(subst(g,{'x':add(variable('x'),variable('e'))}),
               mul(const(-1),g))
        for n in range(10):
            rhs=const(0)
            for k in range(4):
                # [e^n] dG^k: Hasse derivative then set e=0.
                coeff=subst(hasse(power(dG,k),'e',n),{'e':const(0)})
                rhs=add(rhs,mul(subst(hasse(f,'x',k),{'x':g}),coeff))
            assert hasse(fg,'x',n)==rhs
            chain_checks+=1

report={'status':'finite exact integer checks, not Lean',
        'scope_aware_template_instances':checks,
        'physical_multiaffinity_checks':multiaffine,
        'two_layer_binding_masking_fixture':True,
        'integer_hasse_chain_instances':chain_checks}
print(json.dumps(report,indent=2))
