"""Independent challenge: mode-equal terms, actual matched cuts, later hole refill."""
from pathlib import Path
from collections import Counter
from itertools import product
import json
import material_modes as mm
import material_modes_validation as mv
k=mm.k;g=mm.island.gen

def fill(t,uid,p):
    if t.kind=='hole' and t.uid==uid:
        assert not t.meta and p.typ==t.typ
        return p
    return k.T(t.kind,t.uid,t.typ,tuple(fill(c,uid,p) for c in t.children),t.meta)

def holes(t):
    return ([(t.uid,t.typ)] if t.kind=='hole' else [])+sum((holes(c) for c in t.children),[])

def probes(a,b,counts):
    if mm.modes(a)!=mm.modes(b):return
    ca={tuple(sorted(roots)):(f,r) for f,r,roots in k.coaction(a)}
    cb={tuple(sorted(roots)):(f,r) for f,r,roots in k.coaction(b)}
    assert ca.keys()==cb.keys(),'mode equality lost occurrence-matched cuts'
    counts['equal_pairs']+=1
    for roots in ca:
        if not roots:continue
        fa,ra=ca[roots];fb,rb=cb[roots]
        assert sorted(map(k.key,fa),key=repr)==sorted(map(k.key,fb),key=repr)
        assert holes(ra)==holes(rb) or sorted(holes(ra))==sorted(holes(rb))
        counts['nonempty_matched_batches']+=1
        def internal(u,inside=False):
            hit=u.uid in roots and inside
            return hit or any(internal(c,inside or (u.kind=='prim' and k.pure(u))) for c in u.children)
        counts['batches_inside_nonprimitive_islands']+=internal(a)
        assert mm.modes(ra)==mm.modes(rb),'residual mode mismatch before refill'
        hs=sorted(holes(ra))
        # Every complete pure/impure decision for the inherited/new holes.
        for bits in product((False,True),repeat=len(hs)):
            aa,bb=ra,rb
            for (h,typ),impure in zip(hs,bits):
                d=k.prim('refill_d_'+h,'refill_delta_'+typ,(),typ)
                p=d
                if impure:
                    x=k.var('refill_x_'+h,typ)
                    p=k.app('refill_a_'+h,k.lam('refill_l_'+h,x,x),d)
                aa,bb=fill(aa,h,p),fill(bb,h,p)
            assert k.check(aa)==k.check(bb)
            assert mm.modes(aa)==mm.modes(bb),('HOLE_REFILL_COUNTEREXAMPLE',a,b,roots,bits,aa,bb)
            counts['closed_joint_mode_refills']+=1
            if counts['closed_joint_mode_refills']<=400:
                def exact_profile(v):
                    return Counter((tuple(sorted((k.key(p) for p in f),key=repr)),k.key(mm.nhat(r)))
                                   for f,r,_ in k.coaction(v))
                assert exact_profile(aa)==exact_profile(bb),'refilled coaction mismatch'
                counts['post_refill_exact_coaction_checks']+=1
        # Open impure fillers test fresh free ports and later mode switches.
        for h,typ in hs:
            for p in mv.fillers(typ,'open_'+h):
                aa,bb=fill(ra,h,p),fill(rb,h,p)
                assert mm.modes(aa)==mm.modes(bb),('OPEN_REFILL_COUNTEREXAMPLE',a,b,roots,p)
                counts['single_open_or_composite_refills']+=1

def main():
    counts=Counter()
    contexts=((),((0,'p'),),((0,g.A),),((0,g.A),(1,'p')))
    for ctx in contexts:
        for typ in g.TYPES:
            for sz in range(1,9):
                for ast in g.generate(typ,ctx,sz):
                    t=g.instantiate(ast,f'h{counts["terms"]}',ctx);counts['terms']+=1
                    for u in k.one_steps(t,atomic_beta=True):probes(t,u,counts)
                    nt=mm.nhat(t)
                    if k.key(nt)!=k.key(t) and mm.modes(nt)==mm.modes(t):
                        counts['nontrivial_canonical_image_pairs']+=1
                        probes(t,nt,counts)
    result={'status':'NO_BOUNDED_COUNTEREXAMPLE','totals':dict(counts),
      'scope':'all actual antichain batches of generated mode-equal beta/eta and canonical-image pairs; joint closed pure/identity-detour fills preserve complete slot judgment; open/composite single fills additionally stress changing ambient contexts'}
    Path(__file__).with_name('hole_refill_challenge_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
