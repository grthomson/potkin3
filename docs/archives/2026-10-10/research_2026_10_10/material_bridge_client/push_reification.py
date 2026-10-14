"""Exact source-cut/reification check using the combined N_push normalizer."""
from collections import Counter
from pathlib import Path
import json
import source_reification as src
import check_bridge as k
import impure_plus_passenger as push


def verify(name, root, decode):
    target=src.naturalise(root,decode)
    assert k.check(target)==src.source_check(root)
    expected=Counter()
    for roots in src.antichains(root):
        residual,forest=src.source_cut(root,set(roots))
        left=tuple(sorted((k.key(src.naturalise(p,decode)) for p in forest),key=repr))
        right=k.key(push.normal(src.naturalise(residual,decode)))
        expected[(left,right)]+=1
    final=push.normal(target)
    assert expected==push.profile(final,False)
    assert all(not push.steps(r) for _,r,_ in k.coaction(final))
    forms,states,labels=push.all_forms(target)
    assert len(forms)==1
    return {'name':name,'status':'PASS','source_antichain_terms':sum(expected.values()),
            'rewrite_states':states,'rewrite_edge_labels':dict(labels)}


def main():
    rows=[]
    for name,kwargs in [('binary_old_rule',{}),('repeated_boundary',{'repeated':True}),
                        ('nested_nonprimitive',{'nested':True}),('old_hypothetical_discharge',{'hypothetical':True})]:
        rows.append(verify(name,*src.fixture(**kwargs)))
    report={'status':'PASS','normalizer':'N_push','source_cut_naturalisation_normalization_square':rows,
            'scope':'four exact native fixtures; paper theorem carries general claim'}
    Path(__file__).with_name('push_reification_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
