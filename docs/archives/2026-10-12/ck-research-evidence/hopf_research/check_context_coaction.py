"""Exact finite packet checks for the counit lift and positive macro defect.

These supplement the paper proofs, including arbitrary extraction records
which need not be in the image of the coaction. No external packages.
"""
from dataclasses import dataclass
from collections import Counter
from itertools import product
import json

@dataclass(frozen=True)
class Tree:
    label:str
    kids:tuple=()
    colour:str='A'

def box(c='A'):return Tree('BOX',(),c)
def leaf():return Tree('a')
def b(t):
    assert t.colour=='A'
    return Tree('b',(t,),'B')
def c(t):
    assert t.colour=='B'
    return Tree('c',(t,),'A')
def f(t,u):
    assert t.colour==u.colour=='A'
    return Tree('f',(t,u),'A')
def forest(xs):return tuple(sorted(xs,key=repr))
def delta(t):
    if t.label=='BOX':return Counter({((),t):1})
    out=Counter({((t,),box(t.colour)):1})
    children=[delta(k) for k in t.kids]
    for choices in product(*(list(x.items()) for x in children)):
        hh=[];rr=[];coef=1
        for (h,r),n in choices:hh.extend(h);rr.append(r);coef*=n
        out[(forest(hh),Tree(t.label,tuple(rr),t.colour))]+=coef
    return out
def add(*ps):
    out=Counter()
    for p in ps:
        for x,n in p.items():out[x]+=n
    return Counter({x:n for x,n in out.items() if n})
def scale(p,n):return Counter({x:n*v for x,v in p.items() if n*v})
def counit_record(z):
    out=Counter()
    for (h,t),n in z.items():
        if not h:out[t]+=n
    return Counter({x:n for x,n in out.items() if n})
def K(label,colour,zs):
    out=Counter()
    for choices in product(*(list(z.items()) for z in zs)):
        hh=[];rr=[];coef=1
        for (h,r),n in choices:hh.extend(h);rr.append(r);coef*=n
        t=Tree(label,tuple(rr),colour)
        out[(forest(hh),t)]+=coef
        if not hh:out[((t,),box(colour))]+=coef
    return Counter({x:n for x,n in out.items() if n})
def KG(template,records):
    if template.label.startswith('HOLE'):return records[template.label]
    if template.label=='BOX':return Counter({((),template):1})
    return K(template.label,template.colour,[KG(k,records) for k in template.kids])
def fill(template,values):
    if template.label.startswith('HOLE'):return values[template.label]
    return Tree(template.label,tuple(fill(k,values) for k in template.kids),template.colour)
def addresses(t,prefix=()):
    if t.label=='BOX':return []
    return [prefix]+sum((addresses(k,prefix+(i,)) for i,k in enumerate(t.kids)),[])
def extract(t,chosen,prefix=()):
    if prefix in chosen:return [t],box(t.colour)
    hs=[];rs=[]
    for i,k in enumerate(t.kids):
        h,r=extract(k,chosen,prefix+(i,));hs+=h;rs.append(r)
    return hs,Tree(t.label,tuple(rs),t.colour)
def explicit_delta(t):
    ads=addresses(t);out=Counter()
    for mask in range(1<<len(ads)):
        ss=[p for i,p in enumerate(ads) if (mask>>i)&1]
        if any(p!=q and q[:len(p)]==p for p in ss for q in ss):continue
        hs,r=extract(t,set(ss));out[(forest(hs),r)]+=1
    return out

A=[box(),leaf(),c(b(leaf())),f(leaf(),box())]
B=[box('B'),b(leaf()),b(box())]
checks=0
for t in A+B+[f(x,y) for x in A[:3] for y in A[:3]]:
    assert delta(t)==explicit_delta(t)
    assert counit_record(delta(t))==Counter({t:1})
    if t.label!='BOX':assert delta(t)==K(t.label,t.colour,[delta(k) for k in t.kids])
    checks+=1

# Nested typed templates evaluated on signed, arbitrary records. They are not
# restricted to true cut sums, so a spurious counit/masking factor is detectable.
h=Tree('HOLE0',(), 'A');j=Tree('HOLE1',(),'A')
C=f(h,c(b(j)))
D={'HOLE0':c(b(Tree('HOLE2',(),'A'))),
   'HOLE1':f(Tree('HOLE3',(),'A'),Tree('HOLE4',(),'A'))}
flat=fill(C,D)
zs=[Counter({((),leaf()):1}),
    Counter({((leaf(),),box()):1}),
    Counter({((),box()):2,((leaf(),),leaf()):-3}),
    Counter({((leaf(),leaf()),c(b(leaf()))):1})]
arbitrary_checks=0
for x,y,z in product(zs,repeat=3):
    inp={'HOLE2':x,'HOLE3':y,'HOLE4':z}
    staged=KG(C,{name:KG(t,inp) for name,t in D.items()})
    assert staged==KG(flat,inp)
    arbitrary_checks+=1

# Positive linear compiler: source u is unary A→A, compiled as c(b(-)).
# Record source-origin seams separately to classify every target antichain.
def compile_u(t):
    if t.label=='u':return c(b(compile_u(t.kids[0])))
    return Tree(t.label,tuple(compile_u(k) for k in t.kids),t.colour)
def transport(z):
    out=Counter()
    for (hs,r),n in z.items():out[(forest(compile_u(h) for h in hs),compile_u(r))]+=n
    return out
def seams(t,prefix=()):
    if t.label=='BOX':return set()
    ans={prefix}
    if t.label=='u':return ans|seams(t.kids[0],prefix+(0,0))
    for i,k in enumerate(t.kids):ans |=seams(k,prefix+(i,))
    return ans
source=[Tree('u',(p,)) for p in A]+[Tree('u',(Tree('u',(leaf(),)),)),
        f(Tree('u',(leaf(),)),Tree('u',(leaf(),)))]
defect_checks=0
for t in source:
    target=compile_u(t);ads=addresses(target);ss=seams(t)
    aligned=Counter();extra=Counter()
    for mask in range(1<<len(ads)):
        cut=[p for i,p in enumerate(ads) if mask>>i&1]
        if any(p!=q and q[:len(p)]==p for p in cut for q in cut):continue
        hs,r=extract(target,set(cut));key=(forest(hs),r)
        (aligned if set(cut)<=ss else extra)[key]+=1
    assert aligned==transport(delta(t))
    assert add(aligned,extra)==delta(target)
    assert add(delta(target),scale(transport(delta(t)),-1))==extra
    assert all(n>0 for n in extra.values())
    defect_checks+=1
print(json.dumps({'status':'finite exact checks, not Lean',
    'typed_cut_counit_constructor_cases':checks,
    'arbitrary_signed_record_context_compositions':arbitrary_checks,
    'full_positive_macro_defect_cases':defect_checks,
    'separate_typed_boxes':['A','B']},indent=2))
