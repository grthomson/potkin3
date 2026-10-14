"""Actual LJ proof-output check for the 21-node LQ fixture; no Lean claim."""
from check_lq_certificates import Node, bag, fixture, occurrences, weaken, negleft, orleft
from dataclasses import dataclass
from collections import Counter
from itertools import product
import json


def remove(xs,a):
    ys=list(xs); ys.remove(a); return bag(ys)


def contract(t,a):
    assert t.ant.count(a)>=2
    return Node('C:'+a,(t,),remove(t.ant,a),t.succ)


def negright(t,a):
    assert t.succ is None and a in t.ant
    return Node('notR:'+a,(t,),remove(t.ant,a),'~'+a)


def orright(t,a,b,side):
    assert t.succ==(a if side==0 else b)
    return Node('orR:'+a+':'+b+':'+str(side),(t,),t.ant,'('+a+'|'+b+')')


def check(t):
    for c in t.children: check(c)
    if t.rule=='ax': assert t.ant==(t.succ,)
    elif t.rule=='W':
        c,=t.children
        d=Counter(t.ant)-Counter(c.ant)
        assert sum(d.values())==1 and Counter(t.ant)==Counter(c.ant)+d and t.succ==c.succ
    elif t.rule=='notL': assert t==negleft(t.children[0])
    elif t.rule.startswith('notR:'): assert t==negright(t.children[0],t.rule[5:])
    elif t.rule.startswith('C:'): assert t==contract(t.children[0],t.rule[2:])
    elif t.rule.startswith('orL:'):
        _,a,b=t.rule.split(':'); assert t==orleft(*t.children,a,b)
    elif t.rule.startswith('orR:'):
        _,a,b,side=t.rule.split(':'); assert t==orright(t.children[0],a,b,int(side))
    else: raise ValueError(t.rule)


@dataclass
class Result:
    proof: Node
    tokens: dict


def compile_source(t,colour,cut_cache=None):
    """One owner fixture. Token states inherited at cache seams, never rederived."""
    registry={}
    def go(n,path):
        if cut_cache is not None and path in cut_cache:
            return cut_cache[path]
        cs=[go(c,path+(i,)) for i,c in enumerate(n.children)]
        if n.rule=='GR':
            assert n.succ==colour
            tok={('R',path):colour}
            p=Node('ax',(),(colour,),colour)
        elif n.rule=='GL':
            assert n.ant==(colour,) and n.succ is None
            tok={('L',path):'~'+colour}
            p=negleft(Node('ax',(),(colour,),colour))
        elif n.rule=='ax': p=n; tok={}
        elif n.rule=='owner':
            assert path==()
            # Own tokens all live in right premise, all converted before owner.
            assert all(k[0]=='L' and v=='~'+colour for k,v in cs[0].tokens.items())
            lp=cs[0].proof
            if not cs[0].tokens: lp=weaken(lp,'~'+colour)
            for _ in range(len(cs[0].tokens)-1): lp=contract(lp,'~'+colour)
            rp=cs[1].proof
            assert all(k[0]=='R' and v=='~~'+colour for k,v in cs[1].tokens.items())
            if not cs[1].tokens: rp=weaken(rp,'~~'+colour)
            for _ in range(len(cs[1].tokens)-1): rp=contract(rp,'~~'+colour)
            p=orleft(lp,rp,'~'+colour,'~~'+colour)
            tok={('WEM',path):'(~'+colour+'|~~'+colour+')'}
        else:
            tok={}
            for c in cs:
                for k,v in c.tokens.items():
                    assert k not in tok or tok[k]==v
                    tok[k]=v
            padded=[]
            for c in cs:
                p=c.proof
                for k in sorted(tok):
                    if k not in c.tokens: p=weaken(p,tok[k])
                padded.append(p)
            if n.rule=='W':
                added=list((Counter(n.ant)-Counter(n.children[0].ant)).elements())
                assert len(added)==1
                p=weaken(padded[0],added[0])
            elif n.rule=='notL': p=negleft(padded[0])
            elif n.rule.startswith('orL:'):
                _,a,b=n.rule.split(':'); p=orleft(*padded,a,b)
            elif n.rule.startswith('notR:'): p=negright(padded[0],n.rule[5:])
            elif n.rule.startswith('orR:'):
                _,a,b,side=n.rule.split(':'); p=orright(padded[0],a,b,int(side))
            else: raise ValueError(n.rule)
        if n.succ is None:
            for k in sorted(tok):
                if k[0]=='R' and tok[k]==colour:
                    p=negleft(negright(p,colour)); tok[k]='~~'+colour
        assert Counter(p.ant)==Counter(n.ant)+Counter(tok.values())
        assert p.succ==n.succ
        result=Result(p,tok)
        registry[path]=result
        return result
    result=go(t,())
    return result,registry


def cuts(t,path=()):
    # Every edge-subtree choice, empty included; whole root term included.
    yield (path,)
    if not t.children:
        yield ()
    else:
        lists=[list(cuts(c,path+(i,))) for i,c in enumerate(t.children)]
        for choice in product(*lists): yield tuple(a for piece in choice for a in piece)


def main():
    out=[]
    for colour in ('p','q'):
        t=fixture(colour,colour)
        r,cache=compile_source(t,colour)
        check(r.proof)
        total=0
        for cut in cuts(t):
            rebuilt,_=compile_source(t,colour,{a:cache[a] for a in cut})
            assert rebuilt.proof==r.proof and rebuilt.tokens==r.tokens
            total+=1
        counts=Counter(n.rule.split(':')[0] for _,n in occurrences(r.proof))
        out.append({'colour':colour,'source_nodes':len(list(occurrences(t))),
                    'output_nodes':len(list(occurrences(r.proof))),
                    'output_rule_counts':dict(counts),'checked_full_source_cuts':total,
                    'endsequent':{'antecedent':r.proof.ant,'succedent':r.proof.succ},
                    'all_output_rules_ordinary_LJ':True,'cut_free':True})
    left=orright(negright(Node('GL',(),('p',),None),'p'),'~p','~~p',0)
    right=orright(negright(negleft(Node('GR',(),(),'p')),'~p'),'~p','~~p',1)
    t=Node('owner',(left,right),(), '(~p|~~p)')
    r,cache=compile_source(t,'p'); check(r.proof)
    total=0
    for cut in cuts(t):
        rebuilt,_=compile_source(t,'p',{a:cache[a] for a in cut})
        assert rebuilt.proof==r.proof
        total+=1
    counts=Counter(n.rule.split(':')[0] for _,n in occurrences(r.proof))
    assert len(list(occurrences(t)))==8 and len(list(occurrences(r.proof)))==11
    assert counts['W']==counts['C']==0
    out.append({'fixture':'zero_structural_debt_WEM','source_nodes':8,'output_nodes':11,
                'output_rule_counts':dict(counts),'checked_full_source_cuts':total,
                'endsequent':{'antecedent':r.proof.ant,'succedent':r.proof.succ},
                'all_output_rules_ordinary_LJ':True,'cut_free':True})
    print(json.dumps(out,indent=2))


if __name__=='__main__': main()
