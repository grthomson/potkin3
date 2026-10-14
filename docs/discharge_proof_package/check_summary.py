"""Finite debugging model only: no Lean proof or LJ typing claim."""
from dataclasses import dataclass
import random, json
from pathlib import Path

@dataclass(frozen=True)
class T:
    kind: str
    key: int = -1
    pack: int = 0
    role: int = 0
    children: tuple = ()

@dataclass
class S:
    inventory: set
    requirements: dict
    holes: dict
    valid: bool

def direct(tree):
    """Two-pass global address definition, independent of composition."""
    bottoms, tops, holes = {}, {}, {}
    valid = True
    def walk(t, address):
        nonlocal valid
        if t.kind == 'bottom':
            if t.key in bottoms: valid = False
            bottoms[t.key] = (address, t.pack)
        if t.kind == 'top': tops[t.key] = (address, t.pack, t.role)
        if t.kind == 'hole':
            if t.key in holes: valid = False
            holes[t.key] = address
        for i, child in enumerate(t.children): walk(child, address+(i,))
    walk(tree, ())
    # Top key encodes physical top occurrence; owner stored in a separate map.
    req = {}
    for tid, (address, pack, role) in tops.items():
        owner = OWNERS[tid]
        if owner not in bottoms:
            req[tid] = (owner, pack, role)
        else:
            a, p = bottoms[owner]
            valid &= p == pack and address[:len(a)+1] == a+(role,)
    exposure = {}
    for hid, address in holes.items():
        exposure[hid] = {}
        for bid, (a,p) in bottoms.items():
            if len(address)>len(a) and address[:len(a)] == a:
                exposure[hid][bid] = (p, address[len(a)])
    return S(set(bottoms), req, exposure, valid)

def compose(s, fills):
    assert set(fills) <= set(s.holes)
    inventory = set(s.inventory)
    valid = s.valid and all(x.valid for x in fills.values())
    for x in fills.values():
        valid &= not bool(inventory & x.inventory)
        inventory |= x.inventory
    new_ids = inventory - s.inventory
    req = {}
    for tid, r in s.requirements.items():
        if r[0] in new_ids: valid = False
        else: req[tid] = r
    holes = {h: dict(a) for h,a in s.holes.items() if h not in fills}
    for h,x in fills.items():
        for tid,r in x.requirements.items():
            owner,pack,role = r
            if owner in s.inventory:
                valid &= s.holes[h].get(owner) == (pack,role)
            elif owner in inventory:
                valid = False
            else: req[tid] = r
        for k,a in x.holes.items():
            if k in holes: valid = False
            holes[k] = dict(s.holes[h]) | a
    return S(inventory,req,holes,bool(valid))

def plug(t, fills):
    if t.kind == 'hole': return fills.get(t.key,t)
    return T(t.kind,t.key,t.pack,t.role,tuple(plug(c,fills) for c in t.children))

OWNERS = {}
counter = 0
def key():
    global counter
    counter += 1
    return counter
def hole(): return T('hole',key())
def top(owner,p,r,child):
    k = key(); OWNERS[k] = owner
    return T('top',k,p,r,(child,))
def bottom(b,p,l,r): return T('bottom',b,p,0,(l,r))
def unary(t): return T('ordinary',children=(t,))
def leaf(): return T('ordinary')

def random_tree(rng,depth,owner_pool):
    if depth == 0: return hole() if rng.randrange(2) else leaf()
    choice = rng.randrange(5)
    if choice == 0: return hole()
    if choice == 1: return unary(random_tree(rng,depth-1,owner_pool))
    if choice == 2:
        b = key()
        return bottom(b,rng.randrange(2),*(random_tree(rng,depth-1,owner_pool+[b]) for _ in range(2)))
    if choice == 3:
        return top(rng.choice(owner_pool),rng.randrange(2),rng.randrange(2),random_tree(rng,depth-1,owner_pool))
    return T('ordinary',children=tuple(random_tree(rng,depth-1,owner_pool) for _ in range(2)))

def main():
    rng = random.Random(20261013)
    count, invalid, nested = 0,0,0
    for _ in range(1000):
        p = random_tree(rng,3,[-1,-2])
        sp = direct(p)
        fills = {h:random_tree(rng,2,list(sp.inventory)+[-1,-2]) for h in sp.holes}
        # Inject deliberate reverse and sibling references in a fraction of trials.
        if fills and rng.randrange(3)==0:
            h = next(iter(fills)); b = key()
            p = top(b,0,0,p)
            fills[h] = bottom(b,0,fills[h],leaf())
        sp = direct(p)
        expected = direct(plug(p,fills))
        actual = compose(sp,{h:direct(f) for h,f in fills.items()})
        assert actual == expected, (actual,expected)
        count += 1; invalid += not expected.valid
        nextfills = {h:random_tree(rng,1,list(expected.inventory)+[-1,-2]) for h in expected.holes}
        staged = compose(actual,{h:direct(f) for h,f in nextfills.items()})
        final = direct(plug(plug(p,fills),nextfills))
        assert staged == final
        # Only holes belonging to first-stage fillings go inside those fillings.
        upgraded = {h:plug(f,nextfills) for h,f in fills.items()}
        # All original holes were filled; this is the other parenthesization.
        reassoc = compose(sp,{h:direct(f) for h,f in upgraded.items()})
        assert reassoc == final
        nested += 1
    # Unary inference permutation across a bottom; same physical hole IDs.
    b = key(); x,y = hole(),hole()
    before = unary(bottom(b,0,x,y))
    after = bottom(b,0,unary(x),unary(y))
    assert direct(before) == direct(after)
    b2 = key(); x2,y2 = hole(),hole()
    renamed = bottom(b2,0,unary(x2),unary(y2))
    sb = direct(before)
    transported = S({b2},dict(sb.requirements),
                    {x2.key:{b2:(0,0)},y2.key:{b2:(0,1)}},sb.valid)
    assert direct(renamed) == transported
    # Hidden bottom is in a sibling branch and cannot discharge a future top.
    b = key(); h = hole()
    p = T('ordinary',children=(bottom(b,0,leaf(),leaf()),h))
    f = top(b,0,0,leaf())
    assert b in direct(p).inventory and b not in direct(p).holes[h.key]
    assert not compose(direct(p),{h.key:direct(f)}).valid
    assert not direct(plug(p,{h.key:f})).valid
    # Sibling owner and reverse owner negative cases.
    h1,h2 = hole(),hole(); b = key()
    p = T('ordinary',children=(h1,h2))
    fs = {h1.key:top(b,0,0,leaf()),h2.key:bottom(b,0,leaf(),leaf())}
    assert not compose(direct(p),{h:direct(f) for h,f in fs.items()}).valid
    assert compose(direct(p),{h:direct(f) for h,f in fs.items()}) == direct(plug(p,fs))
    out = {'status':'PASS','seed':20261013,'direct_vs_composed_trials':count,
           'nested_associativity_trials':nested,'invalid_cases_in_random_trials':invalid,
           'unary_permutation':True,'global_bottom_and_hole_reindexing':True,
           'hidden_owner_rejection':True,'sibling_owner_rejection':True,
           'scope':'Finite untyped debugging checks; no universal theorem or LJ typing claim.'}
    Path(__file__).with_name('summary_checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__ == '__main__': main()
