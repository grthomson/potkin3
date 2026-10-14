"""Finite exact CK forest / fully-normalized residual profiles.
Independent target construction; does not alter earlier guarded normalizers.
"""
from pathlib import Path
import sys,json
from collections import Counter
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research_2026_10_10/material_bridge_client'))
import check_bridge as k

def nf(t):
    k.check(t)
    while (ss:=k.one_steps(t,atomic_beta=True)):t=ss[0]
    return t

def phi(t):
    return Counter((tuple(sorted((k.key(p) for p in forest),key=repr)),k.key(nf(r)))
                   for forest,r,_ in k.coaction(t))

def cut(uid,x,m,p):return k.app(uid+'a',k.lam(uid+'l',x,m),p)

def cases():
    x,y,z=[k.var(a,'p') for a in ('x','y','z')]
    d=k.prim('d','delta',(),'p')
    f=k.var('f',k.arr('p','q'))
    eta=cut('c',x,k.app('fapp',f,x),d)
    pushed=k.app('fapp',f,cut('c',x,x,d))
    yield 'eta_app_push',eta,pushed,True
    m=k.lam('zlam',z,k.prim('r','r',('p','p'),'q',x,z))
    p=k.prim('s','s',('p',),'p',y)
    yield 'dependent_cut_cut',cut('cy',y,cut('cx',x,m,p),d),cut('cx',x,m,cut('cy',y,p,d)),True
    active=k.app('apply',f,x)
    yield 'general_material_passenger',cut('c',x,k.prim('r','r',('q',),'s',active),d),k.prim('r','r',('q',),'s',cut('c',x,active,d)),True
    yield 'lambda_passenger',cut('c',x,m,d),k.lam('zlam',z,cut('c',x,m.children[0],d)),True
    yield 'unsafe_material_fusion',k.prim('r','r',('p',),'q',cut('c',x,x,d)),k.prim('r','r',('p',),'q',d),False

def main():
    rows=[]
    for name,a,b,equal in cases():
        assert k.check(a)==k.check(b) and a.typ==b.typ
        pa,pb=phi(a),phi(b)
        assert (pa==pb)==equal
        assert k.key(nf(a))==k.key(nf(b))
        rows.append({'name':name,'same_ordinary_normal_form':True,'same_CK_cofree_profile':pa==pb,
          'left_profile_terms':sum(pa.values()),'right_profile_terms':sum(pb.values()),
          'new_right_terms':sum((pb-pa).values()),'lost_right_terms':sum((pa-pb).values())})
    result={'status':'PASS','definition':'Phi=(id_H tensor unrestricted_beta_eta_nf) rho',
      'cases':rows,'scope':'finite actual-antichain profile evidence; cofree comodule proof separate'}
    Path(__file__).with_name('cofree_profile_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
