"""General marked-token compiler exercised on nested real LQ derivations."""
from check_lq_certificates import Node, bag, occurrences, wem_fixture, validate, negleft, orleft, weaken
from check_revival_compiler import check, contract, negright, orright, cuts, Result
from collections import Counter
from itertools import product
import json


def cut(left,right,a):
    assert left.succ==a and a in right.ant
    ant=list(right.ant);ant.remove(a)
    return Node('cut:'+a,(left,right),bag(left.ant+tuple(ant)),right.succ)


def compile_general(t,colours,routes,cut_cache=None):
    registry={}; audit=Counter()
    def go(n,path):
        if cut_cache is not None and path in cut_cache: return cut_cache[path]
        cs=[go(c,path+(i,)) for i,c in enumerate(n.children)]
        if n.rule in ('GL','GR','GE'):
            route=routes[path]; tok={}
            if n.rule in ('GL','GE'):
                own=route[0]; p=colours[own]; tok[('L',path,own)]='~'+p
                assert n.rule=='GE' or n.ant==(p,)
            if n.rule in ('GR','GE'):
                own=route[-1]; q=colours[own]; tok[('R',path,own)]=q
                assert n.rule=='GE' or n.succ==q
            if n.rule=='GE': assert p==q
            atom=p if n.rule=='GL' else q
            proof=Node('ax',(),(atom,),atom)
            if n.rule in ('GL','GE'): proof=negleft(proof); audit['L']+=1
        elif n.rule=='ax': proof=n; tok={}
        elif n.rule=='owner':
            p=colours[path]
            ownbags=[{k:v for k,v in c.tokens.items() if k[0]!='WEM' and k[2]==path} for c in cs]
            assert all(k[0]=='L' and v=='~'+p for k,v in ownbags[0].items())
            assert all(k[0]=='R' and v=='~~'+p for k,v in ownbags[1].items())
            others=[{k:v for k,v in c.tokens.items() if k not in ownbags[j]} for j,c in enumerate(cs)]
            tok={}
            for d in others:
                assert not set(d)&set(tok); tok.update(d)
            padded=[]
            for j,c in enumerate(cs):
                pr=c.proof; f=('~' if j==0 else '~~')+p
                if not ownbags[j]: pr=weaken(pr,f); audit['Wadd']+=1
                for _ in range(len(ownbags[j])-1): pr=contract(pr,f); audit['Cadd']+=1
                for k in sorted(tok):
                    if k not in others[j]: pr=weaken(pr,tok[k]); audit['Wadd']+=1
                padded.append(pr)
            proof=orleft(*padded,'~'+p,'~~'+p)
            tok[('WEM',path,path)]='(~'+p+'|~~'+p+')'
        else:
            tok={}
            for c in cs:
                assert not set(c.tokens)&set(tok); tok.update(c.tokens)
            padded=[]
            for c in cs:
                pr=c.proof
                for k in sorted(tok):
                    if not n.rule.startswith('cut:') and k not in c.tokens:
                        pr=weaken(pr,tok[k]); audit['Wadd']+=1
                padded.append(pr)
            if n.rule=='W':
                added=list((Counter(n.ant)-Counter(n.children[0].ant)).elements()); assert len(added)==1
                proof=weaken(padded[0],added[0])
            elif n.rule=='notL': proof=negleft(padded[0])
            elif n.rule.startswith('notR:'): proof=negright(padded[0],n.rule[5:])
            elif n.rule.startswith('orL:'):
                _,a,b=n.rule.split(':'); proof=orleft(*padded,a,b)
            elif n.rule.startswith('orR:'):
                fields=n.rule.split(':'); a,b=fields[1:3]
                proof=orright(padded[0],a,b,0 if n.children[0].succ==a else 1)
            elif n.rule.startswith('cut:'): proof=cut(*padded,n.rule[4:])
            else: raise ValueError(n.rule)
        if n.succ is None:
            for k in sorted(tok):
                if k[0]=='R' and tok[k]==colours[k[2]]:
                    assert k[2]!=path # Own conclusion is never own checkpoint.
                    proof=negleft(negright(proof,tok[k])); tok[k]='~~'+tok[k]; audit['R']+=1
        assert Counter(proof.ant)==Counter(n.ant)+Counter(tok.values())
        assert proof.succ==n.succ
        result=Result(proof,tok); registry[path]=result
        return result
    result=go(t,())
    return result,registry,audit


def route_choices(t):
    nodes=dict(occurrences(t)); owners=[a for a,n in nodes.items() if n.rule=='owner']
    leaves=[(a,n) for a,n in nodes.items() if n.rule in ('GL','GR','GE')]
    choices=[]
    for a,n in leaves:
        ls=[];rs=[]
        for o in owners:
            if len(o)<len(a) and a[:len(o)]==o:
                if a[len(o)]==0: ls.append(o)
                elif any(nodes[a[:k]].succ is None for k in range(len(o)+1,len(a)+1)): rs.append(o)
        choices.append([(x,) for x in (ls if n.rule=='GL' else rs)] if n.rule!='GE' else list(product(ls,rs)))
    return owners,leaves,[dict(zip([a for a,n in leaves],r)) for r in product(*choices)]


def nested_empty_fixture():
    # S=p,~p=>; outer A left contains inner B whose right GE routes L:A,R:B.
    s=negleft(Node('ax',(),('p',),'p'))
    empty=weaken(weaken(Node('GE',(),(),None),'p'),'~p')
    inner=Node('owner',(s,empty),s.ant,None)
    right=weaken(negleft(Node('GR',(),(),'p')),'p')
    return Node('owner',(inner,right),s.ant,None)


def canonical_adapter(source,path,result,colours,palette):
    target=Counter('(~'+a+'|~~'+a+')' for a in palette)
    for own,p in colours.items():
        if len(own)<len(path) and path[:len(own)]==own:
            if path[len(own)]==0: target['~'+p]+=1
            else:
                target['~~'+p]+=1
                debt=any(k[0]=='R' and k[2]==own and v==p for k,v in result.tokens.items())
                if debt: target[p]+=1
    current=Counter(result.tokens.values()); pr=result.proof
    for f in sorted(current.keys() | target.keys()):
        assert current[f]==0 or target[f]>0
        while current[f]>target[f]: pr=contract(pr,f); current[f]-=1
        while current[f]<target[f]: pr=weaken(pr,f); current[f]+=1
    assert Counter(pr.ant)==Counter(source.ant)+target and pr.succ==source.succ
    check(pr)
    return pr


def main():
    rows=[]
    for label,t in [('nested_WEM',wem_fixture()),('nested_empty',nested_empty_fixture())]:
        owners,leaves,routings=route_choices(t)
        total=0; witnesses=[]
        for values in product(('p','q'),repeat=len(owners)):
            colours=dict(zip(owners,values))
            for routes in routings:
                ok=True
                for a,n in leaves:
                    vals=[colours[o] for o in routes[a]]
                    if n.rule=='GL': ok &= vals[0]==n.ant[0]
                    elif n.rule=='GR': ok &= vals[0]==n.succ
                    else: ok &= vals[0]==vals[1]
                if not ok: continue
                result,cache,audit=compile_general(t,colours,routes)
                check(result.proof)
                nodes=dict(occurrences(t))
                canonical_checks=0
                for path,compiled in cache.items():
                    canonical_adapter(nodes[path],path,compiled,colours,('p','q'))
                    canonical_checks+=1
                source_size=len(list(occurrences(t))); output_size=len(list(occurrences(result.proof)))
                assert output_size==source_size+audit['L']+2*audit['R']+audit['Wadd']+audit['Cadd']
                cutcount=0
                for cut in cuts(t):
                    rebuilt,_,_=compile_general(t,colours,routes,{a:cache[a] for a in cut})
                    assert rebuilt.proof==result.proof
                    cutcount+=1
                total+=1
                witnesses.append({'colours':values,'source_nodes':source_size,'output_nodes':output_size,
                                  'audit':dict(audit),'checked_source_cuts':cutcount,
                                  'canonical_boundary_adapter_checks':canonical_checks})
        assert total==(5 if label=='nested_WEM' else 1)
        rows.append({'fixture':label,'compatible_colour_routing_witnesses':total,'witnesses':witnesses})
    print(json.dumps(rows,indent=2))


if __name__=='__main__':main()
