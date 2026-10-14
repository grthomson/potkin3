"""Run directly; finite executable client integration, no theorem mechanization."""
from pathlib import Path
from copy import deepcopy
import json
import certificate as c
k=c.k


def must_reject(cert):
    try: c.verify(cert)
    except ValueError: return
    raise AssertionError('tampering accepted')


def canonical(t):
    return sorted([(tuple(sorted((k.key(p) for p in f),key=repr)),
                    c.signature(r)) for f,r,_ in c.independent_coaction(t)],key=repr)


def main():
    old,new,ps=c.fixture()
    cert=c.create(old,new,ps)
    # JSON roundtrip is the portable interface, not an in-memory object test.
    cert=json.loads(json.dumps(cert))
    assert c.verify(cert)=='ACCEPT'
    a,b=c.install(old,ps),c.install(new,ps)
    assert canonical(a)==canonical(b)
    # Match every supported cut and every subsequent cut by exact root IDs.
    paired=0
    for fa,ra,roots in c.independent_coaction(a):
        matches=[(fb,rb) for fb,rb,s in c.independent_coaction(b) if set(s)==set(roots)]
        assert len(matches)==1
        fb,rb=matches[0]
        assert sorted((k.key(z) for z in fa),key=repr)==sorted((k.key(z) for z in fb),key=repr)
        assert c.modes.modes(ra)==c.modes.modes(rb)
        assert canonical(ra)==canonical(rb)
        paired+=len(c.independent_coaction(ra))
    # Refusal supplies an actual admitted closed filler, not merely a formal mode.
    x=k.var('x','p');z=k.var('z','p')
    direct=k.prim('refusal_r','r',('p',),'p',x)
    rz=k.prim('refusal_r','r',('p',),'p',z)
    bad=k.app('bad_app',k.lam('bad_lam',z,rz),x)
    refused=c.create(direct,bad,ps)
    assert c.verify(refused)=='REFUSE'
    assert k.key(c.modes.nhat(c.install(direct,ps)))!=k.key(c.modes.nhat(c.install(bad,ps)))
    assert k.key(c.modes.island.nf(direct))==k.key(c.modes.island.nf(bad))
    assert all(r['available_intact'] and r['old_boundary']==r['new_boundary'] for r in cert['composite_modules'])
    lost=next(r for r in refused['composite_modules'] if r['root']=='refusal_r')
    assert not lost['available_intact']
    # Actual nonprimitive inner coefficient and strict two-stage CK flag.
    payload=ps['x']
    forest,residual,_=next(row for row in c.independent_coaction(a) if set(row[2])=={'s'})
    assert forest==(payload,)
    first_f,first_r,_=next(row for row in c.independent_coaction(a) if set(row[2])=={'a'})
    second_f,second_r,_=next(row for row in c.independent_coaction(first_r) if set(row[2])=={'s'})
    inner_f,inner_r,_=next(row for row in c.independent_coaction(payload) if set(row[2])=={'a'})
    assert tuple(k.key(t) for t in first_f)==tuple(k.key(t) for t in inner_f)
    assert tuple(k.key(t) for t in second_f)==(k.key(inner_r),)
    assert k.key(second_r)==k.key(residual)
    assert second_f[0].kind=='prim' and second_f[0].children[0].kind=='hole'
    def refill(t,seam,p):
        if t.kind=='hole' and t.uid==seam:
            assert t.typ==p.typ and k.check(p)==t.meta
            return p
        return k.T(t.kind,t.uid,t.typ,tuple(refill(ch,seam,p) for ch in t.children),t.meta)
    staged=refill(refill(second_r,'s',inner_r),'a',inner_f[0])
    together=refill(second_r,'s',payload)
    assert k.key(staged)==k.key(together)==k.key(a)
    k.check(staged)
    # Exact composite evaluation: this calls prior Faa di Bruno client code.
    probe=k.prim('probe','probe',(),'p')
    template=k.prim('r','r',('p','p'),'p',probe,k.prim('d','d',(),'p'))
    expanded=c.fdb.expand(template,{'probe':payload})
    reconstructed,n=c.fdb.reconstructed_profile(template,{'probe':payload})
    independent_profile=c.fdb.Counter(c.fdb.canonical(f,r) for f,r,_ in c.independent_coaction(expanded))
    assert reconstructed==independent_profile
    # Template has a single probe cut; payload has extra proper/internal cuts.
    assert len(c.independent_coaction(payload))==5
    assert len(c.independent_coaction(probe))==2
    mutations=[]
    tamper=deepcopy(cert);tamper['old_signature']='0'*64;mutations.append(tamper)
    tamper=deepcopy(cert);tamper['decision']='REFUSE';mutations.append(tamper)
    tamper=deepcopy(cert);tamper['installed_old']=[r for r in tamper['installed_old'] if r['roots']!=['s']];mutations.append(tamper)
    tamper=deepcopy(cert);tamper['old_flags'][0]['second'].pop();mutations.append(tamper)
    tamper=deepcopy(cert)
    nonprimitive=next(r for r in tamper['installed_old'] if r['roots']==['s'])
    nonprimitive['forest'][0]['children'].reverse();mutations.append(tamper)
    tamper=deepcopy(cert);tamper['substitutions']['x']['type']='wrong';mutations.append(tamper)
    tamper=deepcopy(cert);tamper['installed_new'][0]['residual_signature']='forged';mutations.append(tamper)
    tamper=deepcopy(cert);tamper['composite_modules'][0]['old_boundary']['holes'][0]['seam']='wrong';mutations.append(tamper)
    tamper=deepcopy(cert);tamper['old_factor_flags'][-1]['factors'][0]['inside'].pop();mutations.append(tamper)
    for t in mutations: must_reject(t)
    # Host/payload namespace must be separated before simultaneous installation.
    collision=k.prim('s','s',('p','p'),'p',k.var('g','p'),k.prim('b','b',(),'p'))
    try: c.install(old,{'x':collision})
    except ValueError: pass
    else: raise AssertionError('capturing/colliding payload accepted')
    base=Path(__file__).parent
    (base/'accepted_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    (base/'refused_certificate.json').write_text(json.dumps(refused,indent=2)+'\n')
    result={'status':'PASS','accepted_replacement':True,'refused_normal_equivalent_replacement':True,
      'explicit_refusal_filler':'s(a,b)','paired_nested_terms':paired,
      'accepted_intact_composites':[r['root'] for r in cert['composite_modules']],
      'refused_lost_composite':'r(s(a,b))',
      'installed_cut_terms':len(cert['installed_old']),'composite_expansion_terms':n,
      'nonprimitive_coefficient':'s(a,b)','strict_nested_flag':'a then s(hole_a,b)',
      'staged_refill_equals_composed_refill':True,
      'inside_detached_factor_flags_checked':True,'namespace_collision_rejected':True,
      'tampering_rejected':len(mutations),'verification_cut_engine':'independent subset/ancestry enumeration',
      'scope':'implicational occurrence-linear bridge client; finite validation, not process/deadlock semantics'}
    (base/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
