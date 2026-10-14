"""Equality/forced-colour certificate diagrams, with closed-component q weights.

Executable research model; no native POTKIN3/Lean claim. Physical tree cuts
are retained. Semantic summaries are coefficients, not a quotient of trees.
"""
from dataclasses import dataclass
from itertools import product
from collections import Counter
import json

@dataclass(frozen=True)
class Diagram:
    boundary: tuple
    blocks: tuple  # ((sorted boundary vertices), forced colour or None)
    loops: int = 0
    zero: bool = False

class UnionFind:
    def __init__(self, xs): self.parent={x:x for x in xs}
    def find(self,x):
        if self.parent[x]!=x: self.parent[x]=self.find(self.parent[x])
        return self.parent[x]
    def join(self,x,y):
        a,b=self.find(x),self.find(y)
        if a!=b: self.parent[b]=a

def summarize(vertices,edges,forced,boundary,prior_loops=0):
    vertices=set(vertices); boundary=tuple(sorted(boundary))
    assert set(boundary)<=vertices
    uf=UnionFind(vertices)
    for a,b in edges: uf.join(a,b)
    comps={}
    for x in vertices: comps.setdefault(uf.find(x),set()).add(x)
    labels={r:set() for r in comps}
    for x,c in forced: labels[uf.find(x)].add(c)
    if any(len(cs)>1 for cs in labels.values()):
        return Diagram(boundary,(),0,True)
    blocks=[]; loops=prior_loops
    for r,vs in comps.items():
        ports=tuple(sorted(vs.intersection(boundary)))
        color=next(iter(labels[r])) if labels[r] else None
        if ports: blocks.append((ports,color))
        elif color is None: loops+=1
    return Diagram(boundary,tuple(sorted(blocks)),loops)

def glue(diagrams,keep):
    keep=tuple(sorted(keep))
    if any(d.zero for d in diagrams): return Diagram(keep,(),0,True)
    vertices=set();edges=[];forced=[];loops=0
    for d in diagrams:
        vertices.update(d.boundary);loops+=d.loops
        for ports,c in d.blocks:
            edges.extend((ports[0],p) for p in ports[1:])
            if c is not None: forced.append((ports[0],c))
    assert set(keep)<=vertices
    return summarize(vertices,edges,forced,keep,loops)

def evaluate(d,q,assignment=None):
    if d.zero:return 0
    assert q>=1
    if assignment is None:
        if any(c is not None and c not in range(q) for _,c in d.blocks):return 0
        return q**(d.loops+sum(c is None for _,c in d.blocks))
    assert set(assignment)==set(d.boundary)
    for ports,c in d.blocks:
        vals={assignment[p] for p in ports}
        if len(vals)!=1 or not vals.issubset(range(q)):return 0
        if c is not None and next(iter(vals))!=c:return 0
    return q**d.loops

def direct_count(vertices,edges,forced,q,boundary_assignment=None):
    boundary_assignment=boundary_assignment or {}
    free=tuple(sorted(set(vertices)-set(boundary_assignment)))
    total=0
    for vals in product(range(q),repeat=len(free)):
        assignment=dict(boundary_assignment);assignment.update(zip(free,vals))
        if all(assignment[a]==assignment[b] for a,b in edges) and all(assignment[x]==c for x,c in forced):total+=1
    return total

def pair_diagrams(a,b):
    ds=[]
    for same in (False,True):
        if same:
            for c in (None,0,1):ds.append(summarize((a,b),[(a,b)],[] if c is None else [(a,c)],(a,b)))
        else:
            for ca,cb in product((None,0,1),repeat=2):
                forced=[(x,c) for x,c in ((a,ca),(b,cb)) if c is not None]
                ds.append(summarize((a,b),[],forced,(a,b)))
    return ds

def run_checks():
    assoc=0
    for d01,d12,d23 in product(pair_diagrams('x0','x1'),pair_diagrams('x1','x2'),pair_diagrams('x2','x3')):
        left=glue((glue((d01,d12),('x0','x2')),d23),('x0','x3'))
        right=glue((d01,glue((d12,d23),('x1','x3'))),('x0','x3'))
        joint=glue((d01,d12,d23),('x0','x3'))
        assert left==right==joint
        # Independently compare to ordinary finite matrix contraction.
        for q in (2,3):
            for a,d in product(range(q),repeat=2):
                matrix=sum(evaluate(d01,q,{'x0':a,'x1':b})*
                           evaluate(d12,q,{'x1':b,'x2':c})*
                           evaluate(d23,q,{'x2':c,'x3':d})
                           for b,c in product(range(q),repeat=2))
                assert evaluate(joint,q,{'x0':a,'x3':d})==matrix
        assoc+=1
    # The external name stays shared; internal names must be freshened.
    shared=summarize(('x',),[],[],('x',))
    shared_trace=glue((shared,shared),())
    fresh1=summarize(('x1',),[],[],('x1',))
    fresh2=summarize(('x2',),[],[],('x2',))
    fresh_trace=glue((fresh1,fresh2),())
    assert shared_trace.loops==1 and fresh_trace.loops==2
    # Two summaries with equal closed counts can differ in every useful future.
    force_x=summarize(('x','y'),[],[('x',0)],('x','y'))
    force_y=summarize(('x','y'),[],[('y',0)],('x','y'))
    outside=summarize(('x',),[],[('x',1)],('x',))
    assert evaluate(force_x,2)==evaluate(force_y,2)==2
    assert evaluate(glue((force_x,outside),()),2)==0
    assert evaluate(glue((force_y,outside),()),2)==1
    return {'associative_diagram_triples':assoc,'matrix_contraction_cases':assoc*13,
            'shared_trace_polynomial':'q','fresh_trace_polynomial':'q^2',
            'equal_early_counts_different_future':[0,1]}

if __name__=='__main__':print(json.dumps(run_checks(),indent=2))
