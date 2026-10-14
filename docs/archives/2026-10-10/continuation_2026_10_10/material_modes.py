"""Experimental finite material-mode refinement; no general congruence claim."""
from pathlib import Path
from itertools import combinations
from dataclasses import dataclass
import json
import island_seal as island
k=island.k

@dataclass(frozen=True)
class _FormalProbeUID:
    # A separate sum-type namespace, disjoint from ordinary string UIDs.
    # The port label makes independently computed signatures align exactly.
    port: str

@dataclass(frozen=True)
class _FormalProbeSymbol:
    port: str
    atom: str

def _ordinary_namespace(t):
    assert isinstance(t.uid,str), 'input proof UIDs must use the ordinary string namespace'
    for c in t.children:_ordinary_namespace(c)

def nhat(t):return t if k.pure(t) else island.normalize(t)
def modes(t):
    _ordinary_namespace(t)
    atomic=[(x,a) for x,a in k.check(t) if k.atomic(a)]
    rows=[]
    for n in range(len(atomic)+1):
        for chosen in combinations(atomic,n):
            u=t
            for x,a in chosen:
                u=k.substitute(u,x,k.prim(_FormalProbeUID(x),_FormalProbeSymbol(x,a),(),a))
            rows.append((tuple(x for x,a in chosen),k.key(nhat(u))))
    return tuple(rows)

def main():
    x,y=k.var('x','p'),k.var('y','p')
    r=lambda v:k.prim('r','r',('p',),'q',v)
    t=k.app('cuta',k.lam('cutl',x,r(x)),y);u=r(y)
    d=k.prim('d','delta',(),'p')
    assert k.key(nhat(t))==k.key(nhat(u))
    assert k.key(nhat(k.substitute(t,'y',d)))!=k.key(nhat(k.substitute(u,'y',d)))
    assert modes(t)!=modes(u)
    # The formerly colliding ordinary UID is retained without renaming.
    old=k.prim('__formal_y','formal_pure_y',(),'p')
    collision=k.prim('collision_r','r',('p','p'),'q',y,old)
    before=k.key(old)
    collision_rows=modes(collision)
    assert len(collision_rows)==2 and k.key(old)==before
    assert _FormalProbeUID('y')!='__formal_y'
    # An independent computation uses identical formal tags, not fresh random IDs.
    assert collision_rows==modes(collision)
    cases=[]
    for name,a,b,equal in island.cases():
        same=modes(a)==modes(b)
        assert same==equal,(name,same)
        cases.append({'name':name,'same_mode_signature':same})
    result={'status':'FINITE_CHECKS_PASS','purity_tag_not_open_substitution_congruence':True,
      'formal_pure_mode_separates_counterexample':True,
      'ordinary_uid_collision_probe_passes':True,
      'formal_namespace':'tagged UID and rule-symbol classes; ordinary source UIDs validated as strings','carrier_gates':cases,
      'scope':'candidate symbolic base-extension observation only; universal substitution theorem unproved'}
    Path(__file__).with_name('material_modes_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
