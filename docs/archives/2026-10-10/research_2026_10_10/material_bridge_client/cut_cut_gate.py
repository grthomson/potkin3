"""Negative Cut-Cut gate for N_push; exact finite witness, not full nets."""
import json
from pathlib import Path
import check_bridge as k
import impure_plus_passenger as push


def cut(uid,x,m,p):return k.app(uid+'_app',k.lam(uid+'_lam',x,m),p)

def main():
    x,y,z=[k.var(a,'p') for a in ('x','y','z')]
    m=k.lam('logical_z',z,k.prim('r','r',('p','p'),'q',x,z))
    p=k.prim('s','s',('p',),'p',y)
    q=k.prim('delta','delta',(),'p')
    left=cut('cy',y,cut('cx',x,m,p),q)
    right=cut('cx',x,m,cut('cy',y,p,q))
    assert k.check(left)==k.check(right)==()
    assert left.typ==right.typ==k.arr('p','q')
    nl,nr=push.normal(left),push.normal(right)
    assert k.key(nl)!=k.key(nr)
    assert not push.steps(nl) and not push.steps(nr)
    expected_left=cut('cy',y,k.lam('logical_z',z,
        k.prim('r','r',('p','p'),'q',k.prim('s','s',('p',),'p',y),z)),q)
    expected_right=k.lam('logical_z',z,k.prim('r','r',('p','p'),'q',
        k.prim('s','s',('p',),'p',cut('cy',y,y,q)),z))
    assert k.key(nl)==k.key(expected_left)
    assert k.key(nr)==k.key(expected_right)
    a,b=push.validate(left),push.validate(right)
    result={'status':'CONFIRMED_COUNTEREXAMPLE','judgment':'empty |- p -> q',
      'source':'C_y(C_x(lambda z.r(x,z),s(y)),delta)',
      'target':'C_x(lambda z.r(x,z),C_y(s(y),delta))',
      'source_normal':'(lambda y.lambda z.r(s(y),z))delta',
      'target_normal':'lambda z.r(s((lambda y.y)delta),z)',
      'normal_classes_distinct':True,'normal_sizes':[push.size(nl),push.size(nr)],
      'source_validation':{'rewrite_states':a[0],'residual_states':a[1],'cut_terms':a[2]},
      'target_validation':{'rewrite_states':b[0],'residual_states':b[1],'cut_terms':b[2]},
      'scope':'failure of representative invariance under this additional Cut-Cut reassociation; bounded primitive-passenger theorem remains intact'}
    Path(__file__).with_name('cut_cut_gate_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
