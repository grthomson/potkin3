"""Literal conjunction-right/ghost-leaf fixture for the checkpoint transform."""
from itertools import product
from collections import Counter
import json
from pathlib import Path

assignments=list(product(range(2),repeat=2))
# Two distinct ghost leaves =>p under a nonempty-succedent conjunction-right.
# Both imported RIGHT owners have colour p; no internal checkpoint exists.
G=Counter(sum(1<<i for i in set(a)) for a in assignments)
# Independent top-down acceptance: each selected external owner must be seen.
F={s:sum(all(s & (1<<owner) for owner in a) for a in assignments)
   for s in range(4)}
inverse={d:sum((-1)**((d^s).bit_count())*F[s]
               for s in range(4) if s & ~d == 0)
         for d in range(4)}
assert [G[d] for d in range(4)]==[0,1,1,2]
assert [F[d] for d in range(4)]==[0,1,1,4]
assert inverse=={d:G[d] for d in range(4)}
leafG={0:0,1:1,2:1,3:0}
unionG={d:sum(leafG[a]*leafG[b] for a in range(4) for b in range(4)
              if a|b==d) for d in range(4)}
leafF={s:sum(leafG[d] for d in range(4) if d & ~s==0) for s in range(4)}
assert unionG==dict(inverse)
assert all(F[s]==leafF[s]**2 for s in range(4))
result={'physical_certificates':len(assignments),
        'exact_debt_counts':[G[d] for d in range(4)],
        'seen_acceptance_counts':[F[d] for d in range(4)],
        'mobius_recovered_counts':[inverse[d] for d in range(4)],
        'union_convolution_becomes_pointwise_product':True,
        'formal_boolean_domain_includes_unrealizable_ancestor_flags':True,
        'status':'bounded check of universal paper identity, not Lean'}
Path(__file__).with_name('checkpoint_mobius_results.json').write_text(
    json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
