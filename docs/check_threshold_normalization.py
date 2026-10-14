from functools import lru_cache
from itertools import product
from math import factorial

# Distinct physical paths are explicitly enumerated by the recursive tree.
def tree(m,a=None):
 a=a or (0,)*len(m)
 if any(x>=b for x,b in zip(a,m)): return ()
 return tuple(tree(m,tuple(x+(j==i) for j,x in enumerate(a))) for i in range(len(m)))
def stats(t):
 if not t:return (0,1)
 ss=[stats(c) for c in t]
 return (1+sum(x for x,y in ss),sum(y for x,y in ss))
def mul(p,q):
 r={}
 for a,x in p.items():
  for b,y in q.items():r[a+b]=r.get(a+b,0)+x*y
 return r
def qtree(t):
 if not t:return {0:1} # opaque interface leaves, ineligible for selection
 p={0:1}
 for c in t:p=mul(p,qtree(c))
 p[1]=p.get(1,0)+1
 return p
def qdag(m):
 @lru_cache(None)
 def f(a):
  if any(x>=b for x,b in zip(a,m)):return {0:1}
  p={0:1}
  for i in range(len(m)):p=mul(p,f(tuple(x+(j==i) for j,x in enumerate(a))))
  p[1]=p.get(1,0)+1
  return p
 return f((0,)*len(m))
def cuts(t):
 if not t:return [frozenset()]
 out=[frozenset([()])]
 for cs in product(*(cuts(c) for c in t)):
  out.append(frozenset((i,)+a for i,C in enumerate(cs) for a in C))
 return out
cases=0
for n in (1,2,3):
 for m in product(range(1,4),repeat=n):
  t=tree(m); N,L=stats(t)
  expected=sum(factorial(sum(a))//__import__('functools').reduce(lambda z,k:z*factorial(k),a,1) for a in product(*(range(k) for k in m)))
  assert N==expected and L==1+(n-1)*N
  assert qtree(t)==qdag(m)
  if N<=13:
   hist={}
   for c in cuts(t):hist[len(c)]=hist.get(len(c),0)+1
   assert hist==qtree(t)
  cases+=1
print('PASS:',cases,'threshold trees; physical recursion/profile DP/count formula agreement; explicit antichains when internal nodes <=13')
for m in ((2,2),(3,3),(2,2,2),(1,3)):
 N,L=stats(tree(m));q=sum(k-1 for k in m)+1;n=len(m)
 full=q if n==1 else (n**q-1)//(n-1)
 print('threshold',m,'q',q,'r_nodes',N,'full_r_nodes',full,'source_copies',L,'opaque-leaf CK spectrum',qdag(m))
def full_proof(m,h,early,a=None):
 a=a or (0,)*len(m); q=sum(x-1 for x in m)+1;k=sum(a)
 eligible=[i for i in range(len(m)) if a[i]>=m[i]]
 if (early and eligible) or k==q:
  i=eligible[0];w=(q-k)*h+k-m[i]
  p=() # positive source proof node, not a Box
  for _ in range(w):p=(p,)
  return p
 return tuple(full_proof(m,h,early,tuple(x+(j==i) for j,x in enumerate(a))) for i in range(len(m)))
def qpositive(t):
 p={0:1}
 for c in t:p=mul(p,qpositive(c))
 p[1]=p.get(1,0)+1
 return p
def nodecount(t):return 1+sum(map(nodecount,t))
for h in (1,20):
 es=full_proof((2,2),h,True);ft=full_proof((2,2),h,False)
 assert nodecount(es)==15+2*h and nodecount(ft)==23
 ec=sum(qpositive(es).values());fc=sum(qpositive(ft).values())
 assert ec==1+(21+10*h)**2 and fc==10202
 print('EW-complete shape fixture H components',h,'early/all-depth nodes',nodecount(es),nodecount(ft),'full positive CK cuts',ec,fc)
