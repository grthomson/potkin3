"""Finite native certificate for the nonprimitive lifting obstruction.

Does not execute a BeS semantic engine; nonzeroness of its support adapter is
proved in hopf_consequence.md. Syntax and every primitive residual are checked.
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research_2026_10_10'/'material_bridge_client'))
from check_bridge import cut,coaction,key,check,pure
from nonprimitive_separation import fixture,nodes
from collections import Counter


def primitive_terms(t):
    return [(tuple(sorted(p.uid for p in forest)),residual)
            for forest,residual,_ in coaction(t)
            if all(p.kind=='prim' and not p.children for p in forest)]


def run():
    source,target=fixture()
    leaves=('a','b','c')
    old,new={},{}
    for mask in range(8):
        chosen={leaves[i] for i in range(3) if mask>>i&1}
        old[mask]=cut(source,chosen)[0]
        new[mask]=cut(target,chosen)[0]
        assert check(old[mask])==check(new[mask])
        assert old[mask].typ==new[mask].typ
    comparison={key(old[m]):new[m] for m in old}
    terms=0
    for mask in old:
        mapped=Counter((forest,key(comparison[key(residual)]))
                       for forest,residual in primitive_terms(old[mask]))
        expected=Counter((forest,key(residual)) for forest,residual in primitive_terms(new[mask]))
        assert mapped==expected
        terms+=sum(mapped.values())
    remainder,forest=cut(source,{'s'})
    p=forest[0]
    assert pure(p)
    def coefficient(t):
        return [r for fs,r,_ in coaction(t) if len(fs)==1 and key(fs[0])==key(p)]
    assert len(coefficient(source))==1
    assert key(coefficient(source)[0])==key(remainder)
    assert not coefficient(target)
    intermediate,detached=cut(p,{'a','b'})
    assert [x.uid for x in detached]==['a','b']
    assert intermediate.kind=='prim' and intermediate.uid=='s'
    assert all(c.kind=='hole' for c in intermediate.children)
    assert check(remainder)==check(source)
    return {'primitive_comodule_state_squares':8,'primitive_coaction_terms':terms,
            'nonprimitive_source_coefficient_multiplicity':1,
            'nonprimitive_target_coefficient_multiplicity':0,
            'positive_binary_intermediate_checked':True,
            'typed_nonzero_residual_syntax_checked':True,
            'semantic_nonzeroness':'paper proof, not executed semantics'}


if __name__=='__main__':
    print(run())
