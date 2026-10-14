"""Finite checks of canonical normalization plans, not a Lean proof checker."""
from functools import lru_cache
from itertools import product
import json

def mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): out[i+j] += a*b
    return tuple(out)

def unary(p, w):
    out = list(p) + [0] * max(0, 2-len(p))
    out[1] += w
    return tuple(out)

def solve(m, h, mode='optimal', donor_sizes=None):
    q = 1 + sum(x-1 for x in m)
    donor_sizes = donor_sizes or (1,)*len(m)
    @lru_cache(None)
    def f(a):
        k = sum(a)
        eligible = [i for i in range(len(m)) if a[i] >= m[i]]
        choices = []
        if mode != 'uniform' or k == q:
            for i in eligible:
                w = (q-k)*h + k-m[i]
                choices.append((donor_sizes[i]+w, unary((1,donor_sizes[i]), w), ('donor', i, w)))
        if k < q and not (mode == 'early' and eligible):
            children = [f(tuple(x+(j==i) for j,x in enumerate(a))) for i in range(len(m))]
            p = (1,)
            for _, cp, _ in children: p = mul(p, cp)
            choices.append((1+sum(x[0] for x in children), unary(p,1), ('rule', tuple(c[2] for c in children))))
        # Lexicographic objective: minimum nodes, then minimum total CK cuts.
        return min(choices, key=lambda c:(c[0],sum(c[1])))
    return f((0,)*len(m))

def enumerate_scores(m,h):
    q=1+sum(x-1 for x in m)
    @lru_cache(None)
    def f(a):
        k=sum(a); out=set()
        for i in range(len(m)):
            if a[i]>=m[i]:
                w=(q-k)*h+k-m[i]
                out.add((1+w,2+w))
        if k<q:
            children=[f(tuple(x+(j==i) for j,x in enumerate(a))) for i in range(len(m))]
            for cs in product(*children):
                size=1+sum(s for s,c in cs); count=1
                for s,c in cs: count*=c
                out.add((size,1+count))
        return out
    return f((0,)*len(m))

def verify_boundary(plan,m,h,a=None):
    """Component-multiset check with fresh C labels, H labels, empty G."""
    a=a or (0,)*len(m); q=1+sum(x-1 for x in m)
    boundary=tuple(a)+(q-sum(a),)*h
    if plan[0]=='donor':
        _,i,w=plan
        source=tuple(m[i] if j==i else 0 for j in range(len(m)))+(0,)*h
        assert all(x<=y for x,y in zip(source,boundary))
        assert sum(boundary)-sum(source)==w
    else:
        common=tuple(a)+(q-sum(a)-1,)*h
        for i,child in enumerate(plan[1]):
            aa=tuple(x+(j==i) for j,x in enumerate(a))
            child_boundary=verify_boundary(child,m,h,aa)
            expected=list(common); expected[i]+=1
            assert child_boundary==tuple(expected)
    return boundary

if __name__=='__main__':
    checked=0
    for n in (1,2,3):
        for m in product((1,2),repeat=n):
            for h in (1,2,4,20):
                opt=solve(m,h)
                assert (opt[0],sum(opt[1]))==min(enumerate_scores(m,h))
                verify_boundary(opt[2],m,h)
                assert opt[0]<=min(solve(m,h,'early')[0],solve(m,h,'uniform')[0])
                checked+=1
    early=solve((1,2),4,'early'); full=solve((1,2),4,'uniform')
    assert early[:2]==(10,(1,10,22,10))
    assert full[:2]==(10,(1,10,26,26,8))
    assert solve((1,2),4)[:2]==early[:2]
    real_early=solve((1,2),4,'early',(1,2))
    real_full=solve((1,2),4,'uniform',(1,2))
    assert real_early[:2]==(11,(1,11,29,20))
    assert real_full[:2]==(11,(1,11,33,40,16))
    com_early=solve((2,2),2,'early',(2,2))
    com_full=solve((2,2),2,'uniform',(2,2))
    assert com_early[0]+4==29 and com_full[0]+4==35
    assert sum(com_early[1])+4==7401 and sum(com_full[1])+4==84105
    verify_boundary(com_early[2],(2,2),2)
    verify_boundary(com_full[2],(2,2),2)
    # Four common terminal EC nodes; same final boundary H, all components fresh.
    result={'finite_instances_checked':checked,
            'equal_size_fixture':{'before_final_EC_nodes':10,'after_final_EC_nodes':14,
                'early_spectrum':unary(early[1],4),'uniform_spectrum':unary(full[1],4),
                'early_cut_count':sum(early[1])+4,'uniform_cut_count':sum(full[1])+4},
            'identity_plus_EW_donors':{'after_final_EC_nodes':15,
                'early_spectrum':unary(real_early[1],4),'uniform_spectrum':unary(real_full[1],4),
                'early_cut_count':sum(real_early[1])+4,'uniform_cut_count':sum(real_full[1])+4,
                'qualification':'Concrete identity/EW donors; four-component external rule remains an assumed schema.'},
            'HLJ_com_fixture':{'early_nodes':29,'uniform_nodes':35,
                'early_spectrum':unary(com_early[1],4),'uniform_spectrum':unary(com_full[1],4),
                'early_cut_count':7401,'uniform_cut_count':84105,
                'qualification':'Paper-level communication-rule instantiation, not a native Lean admission check.'},
            'status':'Executable finite checks only; universal proofs are in the report.'}
    print(json.dumps(result,indent=2))
