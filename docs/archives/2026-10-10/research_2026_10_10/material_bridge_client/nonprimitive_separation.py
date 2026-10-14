"""Concrete primitive-leaf/support shadow versus nonprimitive CK operation.

This does not execute BeS semantics. The erased observation records only the
complete typed hole interface of its proof-irrelevant support operation; the
paper supplies its support interpretation. All native cuts remain explicit.
"""
from collections import Counter
from check_bridge import (T, arr, var, prim, lam, app, check, key, normal,
                          cut, coaction)


def nodes(t):
    yield t
    for c in t.children:
        yield from nodes(c)


def material_inventory(t):
    return Counter((n.uid,n.meta[:2],n.typ) for n in nodes(t) if n.kind=='prim')


def hole_interface(t):
    return tuple(sorted((n.uid,n.typ,n.meta) for n in nodes(t) if n.kind=='hole'))


def leaf_shadow(t):
    result=Counter()
    for forest,residual,_ in coaction(t):
        if all(p.kind=='prim' and not p.children for p in forest):
            result[(tuple(sorted(p.uid for p in forest)),hole_interface(residual),
                    check(residual),residual.typ)]+=1
    return result


def leaf_histories(t):
    # Every nonempty successive batch of original nullary leaf occurrences.
    found={()}
    for forest,residual,_ in coaction(t):
        if forest and all(p.kind=='prim' and not p.children for p in forest):
            first=tuple(sorted(p.uid for p in forest))
            for suffix in leaf_histories(residual):
                found.add((first,)+suffix)
    return found


def fixture():
    p,q='p','q'
    a,b,c=[prim(x,x,(),p) for x in ('a','b','c')]
    left=prim('r','r',(p,p),p,prim('s','s',(p,p),p,a,b),c)
    right=prim('r','r',(p,p),p,a,prim('s','s',(p,p),p,b,c))
    def wrap(t):
        f=var('f',arr(p,q))
        return lam('wrapper',f,app('application',f,t))
    return wrap(left),wrap(right)


def run():
    left,right=fixture()
    assert check(left)==check(right)==()
    assert left.typ==right.typ
    assert key(normal(left))==key(left) and key(normal(right))==key(right)
    assert material_inventory(left)==material_inventory(right)
    assert leaf_shadow(left)==leaf_shadow(right)
    histories=leaf_histories(left)
    assert histories==leaf_histories(right)
    lr,lf=cut(left,{'s'})
    rr,rf=cut(right,{'s'})
    composite=lf[0]
    assert {n.uid for n in nodes(composite)}=={'s','a','b'}
    assert {n.uid for n in nodes(rf[0])}=={'s','b','c'}
    assert not any(any(key(p)==key(composite) for p in forest)
                   for forest,_,_ in coaction(right))
    # Coassociative nested flag: outer s then inner leaves versus leaves then s.
    s_open,detached_leaves=cut(composite,{'a','b'})
    inner_first,first_leaves=cut(left,{'a','b'})
    final_residual,second_factor=cut(inner_first,{'s'})
    assert tuple(map(key,detached_leaves))==tuple(map(key,first_leaves))
    assert key(s_open)==key(second_factor[0])
    assert key(lr)==key(final_residual)
    assert s_open.kind=='prim' and len(s_open.children)==2
    assert all(x.kind=='hole' for x in s_open.children)
    return {'same_material_occurrence_inventory':True,
            'same_complete_judgment_and_both_native_normal':True,
            'same_primitive_leaf_interface_shadow':True,
            'equal_iterated_leaf_histories':len(histories),
            'left_nonprimitive_module_support':['s','a','b'],
            'right_same_rule_module_support':['s','b','c'],
            'actual_nested_cut_flag_with_nonprimitive_intermediate_checked':True}


if __name__=='__main__':
    print(run())
