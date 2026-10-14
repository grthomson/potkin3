"""Occurrence-marked inverse compiler on actual atomic-identity LJ outputs."""
from check_lq_certificates import Node, bag, occurrences, fixture, wem_fixture, negleft, orleft, weaken
from check_revival_compiler import compile_source, check, contract, negright, orright
from check_revival_nested import compile_general, route_choices, nested_empty_fixture, canonical_adapter
from collections import Counter,defaultdict
from itertools import product
import json,re


def mark_context(ant,ctx,principals=()):
    marks=[None]*len(ant); used=set()
    for f,m in principals:
        j=next(j for j,a in enumerate(ant) if a==f and j not in used)
        used.add(j); marks[j]=m
    pool=defaultdict(list)
    for f,m in ctx: pool[f].append(m)
    for j,f in enumerate(ant):
        if j not in used:
            assert pool[f],(ant,ctx,principals)
            marks[j]=pool[f].pop(0)
    assert all(not xs for xs in pool.values())
    return tuple(marks)


def remove_principal(ant,marks,f):
    i=ant.index(f)
    return marks[i],[(a,m) for j,(a,m) in enumerate(zip(ant,marks)) if j!=i]


def atom_of_wem(f):
    m=re.fullmatch(r'\(~([^|()]+)\|~~\1\)',f)
    assert m,f
    return m.group(1)


def ghostify(t,designated):
    """designated = exact root antecedent indices, not a formula-set test."""
    owner_objects={};leaf_objects={}; owner_colours={}; dummy=0
    antmarks=tuple(('W',('root',i),atom_of_wem(f),None) if i in designated else None
                   for i,f in enumerate(t.ant))
    def go(n,am,sm,path):
        nonlocal dummy
        ctx=list(zip(n.ant,am))
        if n.rule=='ax':
            assert len(n.ant)==1 and n.ant[0]==n.succ and n.succ in ('p','q')
            if am[0] is None and sm is None: out=n
            else:
                if am[0] is not None: assert am[0][3]=='R'
                if sm is not None: assert sm[3]=='L'
                kind='GE' if am[0] is not None and sm is not None else ('GR' if am[0] is not None else 'GL')
                out=Node(kind,(),() if am[0] is not None else n.ant,None if sm is not None else n.succ)
                leaf_objects[id(out)]=(sm[1] if sm is not None else None,
                                       am[0][1] if am[0] is not None else None)
        elif n.rule=='W':
            c,=n.children; f=next((Counter(n.ant)-Counter(c.ant)).elements())
            m,rest=remove_principal(n.ant,am,f)
            child=go(c,mark_context(c.ant,rest),sm,path+(0,))
            if m is not None: out=child;dummy+=1
            else: out=weaken(child,f)
        elif n.rule.startswith('C:'):
            c,=n.children;f=n.rule[2:];m,rest=remove_principal(n.ant,am,f)
            child=go(c,mark_context(c.ant,rest,[(f,m),(f,m)]),sm,path+(0,))
            if m is not None: out=child;dummy+=1
            else: out=contract(child,f)
        elif n.rule=='notL':
            c,=n.children;f='~'+c.succ;m,rest=remove_principal(n.ant,am,f)
            child=go(c,mark_context(c.ant,rest),m,path+(0,))
            if m is not None:out=child;dummy+=1
            else:out=negleft(child)
        elif n.rule.startswith('notR:'):
            c,=n.children;f=n.rule[5:]
            child=go(c,mark_context(c.ant,ctx,[(f,sm)]),None,path+(0,))
            if sm is not None:out=child;dummy+=1
            else:out=negright(child,f)
        elif n.rule.startswith('orL:'):
            _,a,b=n.rule.split(':');f='('+a+'|'+b+')';m,rest=remove_principal(n.ant,am,f)
            if m is not None:
                p=atom_of_wem(f); assert m[0]=='W' and m[2]==p
                childmarks=[('phase',path,p,'L'),('phase',path,p,'R')]
                owner_colours[path]=p
            else:childmarks=[None,None]
            children=[go(c,mark_context(c.ant,rest,[(principal,mark)]),sm,path+(j,))
                      for j,(c,principal,mark) in enumerate(zip(n.children,[a,b],childmarks))]
            if m is not None:
                assert (children[0].ant,children[0].succ)==(children[1].ant,children[1].succ)
                out=Node('owner',tuple(children),children[0].ant,children[0].succ)
                owner_objects[id(out)]=path
            else:out=orleft(*children,a,b)
        elif n.rule.startswith('orR:'):
            assert sm is None
            fields=n.rule.split(':');a,b=fields[1:3];c,=n.children
            child=go(c,mark_context(c.ant,ctx),None,path+(0,))
            out=orright(child,a,b,0 if c.succ==a else 1)
        else:raise ValueError(n.rule)
        expected_ant=tuple(f for f,m in zip(n.ant,am) if m is None)
        expected_succ=n.succ if sm is None else None
        assert (out.ant,out.succ)==(expected_ant,expected_succ),(n.rule,out,expected_ant,expected_succ)
        return out
    result=go(t,antmarks,None,())
    inverse_owners={old:a for a,n in occurrences(result) if (old:=owner_objects.get(id(n))) is not None}
    colours={a:owner_colours[old] for old,a in inverse_owners.items()}
    routes={}
    for a,n in occurrences(result):
        if id(n) in leaf_objects:
            left,right=leaf_objects[id(n)]
            routes[a]=tuple(inverse_owners[x] for x in (left,right) if x is not None)
    # Direct certificate validation, independent of compiler proof output.
    nodes=dict(occurrences(result))
    for a,rs in routes.items():
        n=nodes[a]
        roles=[0] if n.rule=='GL' else [1] if n.rule=='GR' else [0,1]
        for own,role in zip(rs,roles):
            assert len(own)<len(a) and a[:len(own)]==own and a[len(own)]==role
            if role==1:
                assert any(nodes[a[:k]].succ is None for k in range(len(own)+1,len(a)+1))
        if n.rule=='GL':assert colours[rs[0]]==n.ant[0]
        elif n.rule=='GR':assert colours[rs[0]]==n.succ
        else:assert colours[rs[0]]==colours[rs[1]]
    return result,colours,routes,dummy


def main():
    proofs=[]
    for colour in ('p','q'):
        r,_=compile_source(fixture(colour,colour),colour);proofs.append(('coordinated_'+colour,r.proof))
    t=wem_fixture();owners,leaves,routings=route_choices(t)
    for values in product(('p','q'),repeat=len(owners)):
        colours=dict(zip(owners,values))
        for routes in routings:
            if not all(colours[routes[a][0]]==(n.ant[0] if n.rule=='GL' else n.succ) for a,n in leaves):continue
            r,cache,audit=compile_general(t,colours,routes)
            proofs.append(('nested_marked',r.proof))
            proofs.append(('nested_canonical',canonical_adapter(t,(),r,colours,('p','q'))))
    rows=[]
    for label,proof in proofs:
        check(proof)
        designated={i for i,f in enumerate(proof.ant) if re.fullmatch(r'\(~([^|()]+)\|~~\1\)',f)}
        erased,colours,routes,dummy=ghostify(proof,designated)
        revived,_,_=compile_general(erased,colours,routes)
        check(revived.proof)
        rows.append({'case':label,'ordinary_input_nodes':len(list(occurrences(proof))),
                     'ghost_output_nodes':len(list(occurrences(erased))),
                     'output_owners':len(colours),'output_ghost_leaves':len(routes),
                     'suppressed_dummy_nodes':dummy,'certificate_checked':True,
                     'revived_again_to_ordinary_LJ':True})
    # Equal formula text at the root does not identify designated occurrences.
    left=orright(negright(Node('GL',(),('p',),None),'p'),'~p','~~p',0)
    right=orright(negright(negleft(Node('GR',(),(),'p')),'~p'),'~p','~~p',1)
    source=Node('owner',(left,right),(), '(~p|~~p)')
    pr,_=compile_source(source,'p')
    proof=weaken(pr.proof,'(~p|~~p)');check(proof)
    for root_index in (0,1):
        erased,colours,routes,dummy=ghostify(proof,{root_index})
        assert erased.ant==('(~p|~~p)',) and erased.succ=='(~p|~~p)'
        revived,_,_=compile_general(erased,colours,routes);check(revived.proof)
        rows.append({'case':'one_of_two_identical_WEM_occurrences','designated_index':root_index,
                     'ordinary_input_nodes':len(list(occurrences(proof))),
                     'ghost_output_nodes':len(list(occurrences(erased))),
                     'output_owners':len(colours),'output_ghost_leaves':len(routes),
                     'suppressed_dummy_nodes':dummy,'certificate_checked':True,
                     'unmarked_equal_WEM_preserved':True,'revived_again_to_ordinary_LJ':True})
    print(json.dumps(rows,indent=2))


if __name__=='__main__':main()
