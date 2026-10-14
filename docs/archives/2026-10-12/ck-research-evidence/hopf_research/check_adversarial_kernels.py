"""Independent finite falsification attempt for all-region certificate kernels.
Not a Lean proof and not a full LQ certificate model.
"""
from itertools import product
from collections import defaultdict
import json

# Each atom gives its *declared* live variables and a local Boolean relation.
ATOMS = [
    ((), lambda a: True, 'unit'),
    (('x',), lambda a: a['x'] == 0, 'x=0'),
    (('x',), lambda a: a['x'] == 1, 'x=1'),
    (('y',), lambda a: a['y'] == 0, 'y=0'),
    (('y',), lambda a: a['y'] == 1, 'y=1'),
    (('x','y'), lambda a: a['x'] == a['y'], 'x=y'),
    (('x','y'), lambda a: a['x'] != a['y'], 'x!=y'),
    (('x',), lambda a: True, 'free x'),
]

def assignments(names):
    return (dict(zip(names, values)) for values in product(range(2), repeat=len(names)))

def bits(mask):
    return {i for i in range(3) if mask & (1 << i)}

def boundary(atoms, mask):
    before, after = set(), set()
    for i, atom in enumerate(atoms):
        (before if i in bits(mask) else after).update(atom[0])
    return tuple(sorted(before & after))

def kernel(atoms, low, high):
    ins, outs = boundary(atoms, low), boundary(atoms, high)
    region = bits(high) - bits(low)
    names = set(ins + outs)
    for i in region:
        names.update(atoms[i][0])
    result = defaultdict(int)
    for a in assignments(sorted(names)):
        if all(atoms[i][1](a) for i in region):
            result[tuple(a[x] for x in ins), tuple(a[x] for x in outs)] += 1
    return dict(result)

def compose(first, second):
    result = defaultdict(int)
    for (a,b), f in first.items():
        for (c,d), g in second.items():
            if b == c:
                result[a,d] += f*g
    return dict(result)

pairs = [(i,j) for i in range(8) for j in range(8) if i & j == i]
triples = [(i,j,k) for i,j in pairs for k in range(8) if j & k == j]
count = 0
for idxs in product(range(len(ATOMS)), repeat=3):
    atoms = [ATOMS[i] for i in idxs]
    kernels = {(i,j): kernel(atoms,i,j) for i,j in pairs}
    for i,j,k in triples:
        assert kernels[i,k] == compose(kernels[i,j], kernels[j,k]), (idxs,i,j,k)
        count += 1
    # Independent whole-network enumeration must agree with empty/full kernel.
    all_names = sorted(set().union(*(set(atom[0]) for atom in atoms)))
    direct = sum(all(atom[1](a) for atom in atoms) for a in assignments(all_names))
    assert kernels[0,7].get(((),()),0) == direct

# Explicit tests of the disputed cases.
a = [ATOMS[1], ATOMS[0], ATOMS[2]]
assert boundary(a,1) == ('x',) and boundary(a,3) == ('x',)
assert kernel(a,1,3) == {((0,),(0,)):1, ((1,),(1,)):1}
assert kernel(a,0,7) == {}
# Independent feasibility is true in both end regions, but gluing is false.
assert any(ATOMS[1][1](v) for v in assignments(['x']))
assert any(ATOMS[2][1](v) for v in assignments(['x']))
# Copy semantics: common external x versus fresh x,y.
shared_count = sum(1 for _ in assignments(['x']))
fresh_count = sum(1 for _ in assignments(['x','y']))
assert (shared_count,fresh_count)==(2,4)
print(json.dumps({'networks':len(ATOMS)**3, 'nested_region_checks':count,
 'whole_network_comparisons':len(ATOMS)**3,
 'nonconsecutive_port_identity':True, 'incompatible_siblings_detected':True,
 'shared_copy_count':shared_count,'fresh_copy_count':fresh_count}, indent=2))
