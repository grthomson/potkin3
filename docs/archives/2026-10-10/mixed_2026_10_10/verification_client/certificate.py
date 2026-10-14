"""Portable replacement certificates for the existing material bridge client.

Trusted comparison: the prior finite-mode algorithm. Cut validation uses an
independent powerset/ancestry implementation, not the producer's recursion.
No process, deadlock, authentication, or general mixed-fragment claim.
"""
from pathlib import Path
import sys, json, hashlib
from itertools import combinations
from dataclasses import is_dataclass, asdict

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'continuation_2026_10_10'))
import material_modes as modes
import faa_di_bruno_expansion as fdb
k = modes.k


def jsonable(v):
    if is_dataclass(v):
        return {'tag': type(v).__name__, 'value': jsonable(asdict(v))}
    if isinstance(v, dict): return {str(a): jsonable(b) for a,b in v.items()}
    if isinstance(v, (tuple,list)): return [jsonable(x) for x in v]
    return v


def digest(v):
    return hashlib.sha256(json.dumps(jsonable(v), sort_keys=True,
                         separators=(',', ':')).encode()).hexdigest()


def encode(t):
    return {'kind':t.kind,'uid':t.uid,'type':jsonable(t.typ),
            'meta':jsonable(t.meta),'children':[encode(c) for c in t.children]}


def tuples(v):
    return tuple(tuples(x) for x in v) if isinstance(v,list) else v


def decode(d):
    if set(d) != {'kind','uid','type','meta','children'}: raise ValueError('tree fields')
    if not isinstance(d['uid'],str): raise ValueError('ordinary UID required')
    return k.T(d['kind'], d['uid'], tuples(d['type']),
               tuple(decode(c) for c in d['children']), tuples(d['meta']))


def signature(t): return digest(modes.modes(t))


def row(f,r,roots):
    return {'roots':sorted(roots), 'forest':sorted([encode(p) for p in f],key=lambda p:p['uid']),
            'residual':encode(r),'residual_signature':signature(r)}


def rows(t,engine=k.coaction):
    return sorted([row(f,r,a) for f,r,a in engine(t)],key=lambda a:a['roots'])


def independent_coaction(t):
    """Enumerate vertex subsets and test prefix-incomparability independently."""
    locations = {}
    def collect(u,path):
        locations[u.uid]=(path,u)
        for i,c in enumerate(u.children): collect(c,path+(i,))
    collect(t,())
    def material(u):
        return u.kind=='hole' or (u.kind=='prim' and all(material(c) for c in u.children))
    eligible=[uid for uid,(_,u) in locations.items() if u.kind=='prim' and material(u)]
    out=[]
    for n in range(len(eligible)+1):
        for roots in combinations(eligible,n):
            paths=[locations[a][0] for a in roots]
            if any(a==b[:len(a)] or b==a[:len(b)] for a,b in combinations(paths,2)): continue
            def remove(u):
                if u.uid in roots: return k.T('hole',u.uid,u.typ,(),k.check(u))
                return k.T(u.kind,u.uid,u.typ,tuple(remove(c) for c in u.children),u.meta)
            residual=remove(t)
            k.check(residual)
            out.append((tuple(locations[a][1] for a in roots),residual,roots))
    return out


def install(t, substitutions):
    context=dict(k.check(t))
    if not set(substitutions)<=set(context): raise ValueError('unknown input')
    def uids(u): return {u.uid}.union(*(uids(ch) for ch in u.children))
    used=uids(t)
    contexts=[tuple((x,a) for x,a in context.items() if x not in substitutions)]
    for x,p in substitutions.items():
        if p.typ!=context[x]: raise ValueError('payload type')
        if uids(p)&used: raise ValueError('payload namespace collision')
        used|=uids(p)
        contexts.append(k.check(p))
    def simultaneous(u):
        if u.kind=='var' and u.uid in substitutions: return substitutions[u.uid]
        return k.T(u.kind,u.uid,u.typ,tuple(simultaneous(ch) for ch in u.children),u.meta)
    result=simultaneous(t)
    if k.check(result)!=k.merge(contexts): raise ValueError('capture or interface mismatch')
    return result


def flags(t,engine=k.coaction):
    return sorted([{'first':sorted(a),'second':rows(r,engine)}
                   for _,r,a in engine(t) if a],key=lambda a:a['first'])


def factor_flags(t,engine=k.coaction):
    return sorted([{'first':sorted(a),'factors':[
        {'root':p.uid,'inside':rows(p,engine)} for p in sorted(f,key=lambda z:z.uid)]}
        for f,_,a in engine(t) if a],key=lambda a:a['first'])


def boundary(t):
    holes=[]
    def walk(u):
        if u.kind=='hole': holes.append({'seam':u.uid,'type':jsonable(u.typ),'context':jsonable(u.meta)})
        for ch in u.children: walk(ch)
    walk(t)
    return {'output':jsonable(t.typ),'free':jsonable(k.check(t)),
            'holes':sorted(holes,key=lambda h:h['seam'])}


def module_contract(old,new,engine=k.coaction):
    """Expose all intact composite module factors and their complete remainder ports."""
    target=engine(new); result=[]
    for forest,r,roots in engine(old):
        if len(forest)!=1 or not forest[0].children: continue
        matches=[(f,s) for f,s,a in target if set(a)==set(roots)
                 and tuple(k.key(p) for p in f)==tuple(k.key(p) for p in forest)]
        result.append({'root':roots[0],'factor':encode(forest[0]),
                       'old_boundary':boundary(r),'available_intact':bool(matches),
                       'new_boundary':boundary(matches[0][1]) if matches else None})
    return sorted(result,key=lambda a:a['root'])


def create(old,new,substitutions):
    if k.check(old)!=k.check(new) or old.typ!=new.typ: raise ValueError('interface mismatch')
    a,b=install(old,substitutions),install(new,substitutions)
    return {'schema':'ck-material-replacement/1','old':encode(old),'new':encode(new),
      'substitutions':{x:encode(p) for x,p in substitutions.items()},
      'old_signature':signature(old),'new_signature':signature(new),
      'decision':'ACCEPT' if modes.modes(old)==modes.modes(new) else 'REFUSE',
      'installed_old':rows(a),'installed_new':rows(b),
      'old_flags':flags(a),'new_flags':flags(b),
      'old_factor_flags':factor_flags(a),'new_factor_flags':factor_flags(b),
      'composite_modules':module_contract(a,b)}


def verify(c):
    """Recompute claims; rejecting a replacement is a valid certificate decision."""
    try:
        expected={'schema','old','new','substitutions','old_signature','new_signature',
                  'decision','installed_old','installed_new','old_flags','new_flags','composite_modules',
                  'old_factor_flags','new_factor_flags'}
        if set(c)!=expected or c['schema']!='ck-material-replacement/1': raise ValueError('schema')
        old,new=decode(c['old']),decode(c['new'])
        if k.check(old)!=k.check(new) or old.typ!=new.typ: raise ValueError('interface')
        if c['old_signature']!=signature(old) or c['new_signature']!=signature(new): raise ValueError('signature')
        decision='ACCEPT' if modes.modes(old)==modes.modes(new) else 'REFUSE'
        if c['decision']!=decision: raise ValueError('decision')
        ps={x:decode(p) for x,p in c['substitutions'].items()}
        if not set(ps)<=set(dict(k.check(old))): raise ValueError('unknown input')
        for label,t in [('old',old),('new',new)]:
            installed=install(t,ps)
            if c['installed_'+label]!=rows(installed,independent_coaction): raise ValueError('actual cut profile')
            if c[label+'_flags']!=flags(installed,independent_coaction): raise ValueError('nested cut flags')
            if c[label+'_factor_flags']!=factor_flags(installed,independent_coaction): raise ValueError('inside-factor cut flags')
        contract=module_contract(install(old,ps),install(new,ps),independent_coaction)
        if c['composite_modules']!=contract: raise ValueError('intact composite modules')
        if decision=='ACCEPT' and any(not r['available_intact'] or r['old_boundary']!=r['new_boundary'] for r in contract):
            raise ValueError('accepted module interface not preserved')
        return decision
    except (AssertionError,KeyError,TypeError,IndexError) as e:
        raise ValueError('invalid native certificate') from e


def fixture():
    x=k.var('x','p');g=k.var('g',k.arr('p','q'));h=k.var('h',g.typ)
    d=k.prim('d','d',(),'p')
    region=k.prim('r','r',('p','p'),'p',x,d)
    old=k.app('old_application',g,region)
    new=k.app('new_beta',k.lam('new_lambda',h,k.app('new_body',h,region)),g)
    a=k.prim('a','a',(),'p');b=k.prim('b','b',(),'p')
    payload=k.prim('s','s',('p','p'),'p',a,b)
    return old,new,{'x':payload}


def main():
    c=create(*fixture())
    target=Path(__file__).with_name('accepted_certificate.json')
    target.write_text(json.dumps(c,indent=2)+'\n')
    print(json.dumps({'certificate':target.name,'verified':verify(c)}))


if __name__=='__main__': main()
