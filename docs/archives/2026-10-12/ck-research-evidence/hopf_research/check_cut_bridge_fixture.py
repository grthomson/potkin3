"""One explicit identity-Cut bridge fixture, NOT a generic Cut eliminator."""
from check_lq_certificates import Node, occurrences, negleft
from check_revival_compiler import negright,orright,check
from check_revival_nested import cut,compile_general
from check_ghostification import ghostify
import json


def check_with_cut(t):
    if t.rule.startswith('cut:'):
        for c in t.children:check_with_cut(c)
        assert t==cut(*t.children,t.rule[4:])
    else:
        for c in t.children:check_with_cut(c)
        # A node's local ordinary rule can be checked after replacing each
        # Cut subtree by its known type-equivalent identity-cut reduct.
        check(reduce_identity_cut(t))


def reduce_identity_cut(t):
    children=tuple(reduce_identity_cut(c) for c in t.children)
    if t.rule.startswith('cut:'):
        left,right=children;a=t.rule[4:]
        assert left.rule=='ax' and left.ant==(a,) and left.succ==a
        assert (right.ant,right.succ)==(t.ant,t.succ)
        return right
    return Node(t.rule,children,t.ant,t.succ)


def main():
    left=orright(negright(Node('GL',(),('p',),None),'p'),'~p','~~p',0)
    contradiction=negleft(Node('ax',(),('p',),'p'))
    right=cut(Node('GR',(),(),'p'),contradiction,'p')
    right=orright(negright(right,'~p'),'~p','~~p',1)
    source=Node('owner',(left,right),(), '(~p|~~p)')
    leaves=[(a,n) for a,n in occurrences(source) if n.rule in ('GL','GR')]
    routes={a:((),) for a,n in leaves}
    compiled,_,audit=compile_general(source,{():'p'},routes)
    check_with_cut(compiled.proof)
    normalized=reduce_identity_cut(compiled.proof);check(normalized)
    assert not any(n.rule.startswith('cut:') for _,n in occurrences(normalized))
    erased,colours,newroutes,dummy=ghostify(normalized,{0})
    final,_,_=compile_general(erased,colours,newroutes);check(final.proof)
    assert erased.ant==() and erased.succ=='(~p|~~p)'
    print(json.dumps({'source_nodes':len(list(occurrences(source))),
                      'compiled_nodes':len(list(occurrences(compiled.proof))),
                      'normalized_nodes':len(list(occurrences(normalized))),
                      'grounded_output_nodes':len(list(occurrences(erased))),
                      'audit':dict(audit),'source_cut_is_right_leaf_first_empty_checkpoint':True,
                      'outer_owner_spans_Cut_premise':'Cut first premise ghost is not independently grounded',
                      'normalization':'one explicitly checked identity-Cut reduction, no general normalizer',
                      'new_certificate_checked':True,'endsequent':' => (~p|~~p)'},indent=2))


if __name__=='__main__':main()
