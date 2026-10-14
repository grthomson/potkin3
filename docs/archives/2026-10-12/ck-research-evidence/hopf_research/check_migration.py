from dataclasses import dataclass
from collections import Counter
from itertools import product
import json
@dataclass(frozen=True)
class T:
    op:str
    kids:tuple=()
    name:str=''

def var(x):return T('var',(),x)
def app(f,x):return T('app',(f,x))
def lam(x,t):return T('lam',(t,),x)
def par(a,x,y):return T('session',(x,y),a)
def pair(x,y):return T('pair',(x,y))
def fv(t):
    if t.op=='var':return frozenset([t.name])
    f=frozenset().union(*(fv(k) for k in t.kids))
    if t.op=='chan':f=f|{t.name}
    return f-{t.name} if t.op in ('lam','session') else f

def mul(p,q):
    r=Counter()
    for i,a in p.items():
      for j,b in q.items():r[i+j]+=a*b
    return r

def spectrum(t,resource,eligible=lambda t:True):
    p=Counter({0:1})
    for k in t.kids:p=mul(p,spectrum(k,resource,eligible))
    if eligible(t):p[int(resource in fv(t))]+=1
    return p

def cuts(t):
    # tuple of detached whole subtrees, no remainder quotient or deduplication.
    yield (t,)
    for cc in product(*(list(cuts(k)) for k in t.kids)):
        yield sum(cc,())

def nodes(t):return 1+sum(nodes(k) for k in t.kids)

def source():
 return par('a',lam('x',app(var('a'),app(var('z'),var('x')))),
            lam('y',pair(var('y'),app(var('a'),app(var('y'),var('k'))))))
def reduct():
 return par('b',
   par('a1',lam('x1',app(app(var('b'),var('x1')),var('k'))),
             lam('y1',pair(var('y1'),app(var('a1'),app(var('y1'),var('k')))))),
   par('a2',lam('x2',app(var('a2'),app(var('z'),var('x2')))),
             lam('y2',pair(var('y2'),app(var('z'),app(var('b'),var('y2')))))))

def allsmall(n):
 if n==1:return [var('b'),var('g')]
 out=[lam('b',t) for t in allsmall(n-1)]
 for i in range(1,n-1):
  out.extend(app(l,r) for l in allsmall(i) for r in allsmall(n-i-1))
 return out

checks=0
for n in range(1,8):
 for t in allsmall(n):
  explicit=Counter(sum('b' in fv(p) for p in cc) for cc in cuts(t))
  assert explicit==spectrum(t,'b')
  # Max free-b-bearing antichain = number of variable b occurrences.
  def occ_b(t):return int(t.op=='var' and t.name=='b')+sum(occ_b(k) for k in t.kids)
  # This equality holds even with inner b binders: singleton leaves expose them,
  # but resource-ID interpretation must distinguish actual binder identities.
  assert max(explicit)==occ_b(t)
  checks+=1
s,r=source(),reduct()
report={
 'status':'finite checks; not Lean and not native eligibility bridge',
 'exhaustive_small_terms_checked':checks,
 'source':{'nodes':nodes(s),'free_variables':sorted(fv(s)), 'b_spectrum':dict(sorted(spectrum(s,'b').items()))},
 'reduct':{'nodes':nodes(r),'free_variables':sorted(fv(r)), 'b_spectrum':dict(sorted(spectrum(r,'b').items()))},
 'reduct_selected_root_eligibility_variants':{
  'all_positive_nodes':dict(sorted(spectrum(r,'b').items())),
  'applications_only':dict(sorted(spectrum(r,'b',lambda t:t.op=='app').items())),
  'session_roots_only':dict(sorted(spectrum(r,'b',lambda t:t.op=='session').items()))}}
p1=pair(var('x'),lam('h',var('g')))
p2=pair(var('g'),lam('h',var('x')))
def subst_x(t):
    if t.op=='var' and t.name=='x':return app(var('b'),var('y'))
    return T(t.op,tuple(subst_x(k) for k in t.kids),t.name)
assert fv(p1)==fv(p2)==frozenset({'x','g'})
assert spectrum(p1,'b')==spectrum(p2,'b')==Counter({0:7})
assert spectrum(subst_x(p1),'b')==Counter({0:6,1:10})
assert spectrum(subst_x(p2),'b')==Counter({0:4,1:9})
report['typed_context_separator']={
 'source_common_spectrum':dict(spectrum(p1,'b')),
 'adapted_first':dict(spectrum(subst_x(p1),'b')),
 'adapted_second':dict(spectrum(subst_x(p2),'b')),
 'types':'x,g:A; h:H; b:B→A; y:B; both outputs A∧(H→A)'}
def chan(a,t):return T('chan',(t,),a)
def wrapw(t):return app(var('w'),t)
def wrapr(t):return app(var('r'),t)
def typed_source():
 return par('a',wrapw(lam('x',chan('a',app(var('z'),var('x'))))),
   wrapr(lam('y',pair(var('y'),chan('a',app(var('y'),var('k')))))))
def typed_reduct():
 return par('b',
   par('a1',wrapw(lam('x1',app(chan('b',var('x1')),var('k')))),
       wrapr(lam('y1',pair(var('y1'),chan('a1',app(var('y1'),var('k'))))))),
   par('a2',wrapw(lam('x2',chan('a2',app(var('z'),var('x2'))))),
       wrapr(lam('y2',pair(var('y2'),app(var('z'),chan('b',var('y2'))))))))
def Arr(a,b):return ('arrow',a,b)
def Prod(a,b):return ('product',a,b)
A,B,X,K,E='A','B','X','K','E'
Y=Arr(K,B)
ordinary_env={'w':Arr(Arr(X,B),E),'r':Arr(Arr(Y,Prod(Y,A)),E),'z':Arr(X,A),'k':K}
bound_types={'x':X,'x1':X,'x2':X,'y':Y,'y1':Y,'y2':Y}
channel_roles={a:(Arr(A,B),Arr(B,A)) for a in ['a','a1','a2']}
channel_roles['b']=(Arr(X,Y),Arr(Y,X))
def typeof(t,ordinary,channels):
 if t.op=='var':return ordinary[t.name]
 if t.op=='lam':
  return Arr(bound_types[t.name],typeof(t.kids[0],ordinary|{t.name:bound_types[t.name]},channels))
 if t.op=='pair':return Prod(*(typeof(k,ordinary,channels) for k in t.kids))
 if t.op=='app':
  f,x=(typeof(k,ordinary,channels) for k in t.kids)
  assert isinstance(f,tuple) and f[0]=='arrow' and f[1]==x,(t,f,x)
  return f[2]
 if t.op=='chan':
  f=channels[t.name];x=typeof(t.kids[0],ordinary,channels)
  assert f[0]=='arrow' and f[1]==x,(t,f,x)
  return f[2]
 if t.op=='session':
  outputs=[typeof(k,ordinary,channels|{t.name:role}) for k,role in zip(t.kids,channel_roles[t.name])]
  assert len(outputs)==2 and outputs[0]==outputs[1],(t,outputs)
  return outputs[0]
 raise AssertionError(t)
ts,tr=typed_source(),typed_reduct()
assert typeof(ts,ordinary_env,{})==typeof(tr,ordinary_env,{})==E
assert fv(ts)==fv(tr)==frozenset(ordinary_env)
assert spectrum(ts,'b')==Counter({0:436})
assert spectrum(tr,'b')==Counter({0:55681,1:122272,2:67072})
report['typed_canonical_channel_fixture']={
 'encoding':'channel application is one unary node with channel identity in label; no standalone channel term',
 'common_checked_output_type':'E',
 'source_nodes':nodes(ts),'target_nodes':nodes(tr),
 'free_variables':sorted(fv(ts)),
 'source_spectrum':dict(spectrum(ts,'b')),
 'target_spectrum':dict(spectrum(tr,'b')),
 'target_branch_spectra':[dict(spectrum(k,'b')) for k in tr.kids]}
def subst_x_canonical(t):
    if t.op=='var' and t.name=='x':return chan('b',var('y'))
    return T(t.op,tuple(subst_x_canonical(k) for k in t.kids),t.name)
assert spectrum(subst_x_canonical(p1),'b')==Counter({0:6,1:4})
assert spectrum(subst_x_canonical(p2),'b')==Counter({0:4,1:5})
report['canonical_context_separator']={
 'adapter_spectrum':dict(spectrum(chan('b',var('y')),'b')),
 'adapted_first':dict(spectrum(subst_x_canonical(p1),'b')),
 'adapted_second':dict(spectrum(subst_x_canonical(p2),'b'))}
def has_session(t):return t.op=='session' or any(has_session(k) for k in t.kids)
def optimize(t):
    options={0:(0,())}
    for i,k in enumerate(t.kids):
        merged={}
        for cost,(benefit,plan) in options.items():
            for ck,(bk,pk) in optimize(k).items():
                total=cost+ck
                choice=(benefit+bk,plan+tuple((i,)+p for p in pk))
                if total not in merged or choice[0]>merged[total][0]:merged[total]=choice
        options=merged
    if not has_session(t):
        c=int('b' in fv(t));benefit=nodes(t)-2
        if c not in options or benefit>options[c][0]:options[c]=(benefit,((),))
    return options
opts=optimize(tr)
assert {c:b for c,(b,_) in opts.items()}=={0:12,1:19,2:24}
report['budgeted_externalization']={
 'eligibility':'subtree has no session constructor',
 'cost':'one per selected task with free b',
 'benefit':'node count minus two units of task overhead',
 'optimal_exact_cost':{c:{'benefit':b,'selected_addresses':plan} for c,(b,plan) in opts.items()}}
def message(first,xterm,h):
    return pair(xterm,lam(h,var('g'))) if first else pair(var('g'),lam(h,xterm))
def paired_source(first):
    return par('a',wrapw(lam('x',chan('a',message(first,var('x'),'h')))),
                   wrapr(lam('y',chan('a',var('y')))))
def paired_target(first):
    return par('b',
      par('a1',wrapw(lam('x1',chan('b',var('x1')))),
               wrapr(lam('y1',chan('a1',var('y1'))))),
      par('a2',wrapw(lam('x2',chan('a2',message(first,var('x2'),'h2')))),
               wrapr(lam('y2',message(first,chan('b',var('y2')),'h3')))))
A,H,V,E='A','H','V','E';U=Prod(A,Arr(H,A))
ordinary_env={'w':Arr(Arr(A,V),E),'r':Arr(Arr(V,U),E),'g':A}
bound_types={**{x:A for x in ['x','x1','x2']},**{y:V for y in ['y','y1','y2']},**{h:H for h in ['h','h2','h3']}}
channel_roles={a:(Arr(U,V),Arr(V,U)) for a in ['a','a1','a2']}
channel_roles['b']=(Arr(A,V),Arr(V,A))
paired=[]
for first in [True,False]:
    s,t=paired_source(first),paired_target(first)
    assert typeof(s,ordinary_env,{})==typeof(t,ordinary_env,{})==E
    assert fv(s)==fv(t)==frozenset(ordinary_env)
    assert spectrum(s,'b')==Counter({0:172})
    paired.append({'source_nodes':nodes(s),'target_nodes':nodes(t),
                   'source_spectrum':dict(spectrum(s,'b')),
                   'target_spectrum':dict(spectrum(t,'b')),
                   'target_inner_session_spectra':[dict(spectrum(k,'b')) for k in t.kids]})
assert spectrum(paired_target(True),'b')==Counter({0:8209,1:18048,2:9660})
assert spectrum(paired_target(False),'b')==Counter({0:5473,1:15920,2:11408})
report['actual_typed_cross_separator']={
 'status':'both complete source and target terms typecheck at E',
 'cases':paired}
print(json.dumps(report,indent=2))
