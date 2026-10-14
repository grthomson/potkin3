"""Generated pair/substitution probes for material modes (finite evidence)."""
from pathlib import Path
from collections import Counter
import json
import material_modes as mm
k=mm.k;g=mm.island.gen

def fillers(a,prefix):
    out=[k.var(prefix+'ref',a)]
    if k.atomic(a):
        d=k.prim(prefix+'d','delta_'+a,(),a)
        out += [d,k.prim(prefix+'bin','bin_'+a,(a,a),a,d,k.prim(prefix+'e','delta_'+a,(),a))]
        x=k.var(prefix+'x',a)
        out += [k.app(prefix+'ia',k.lam(prefix+'il',x,x),d),
                k.app(prefix+'fa',k.var(prefix+'f',k.arr(a,a)),d)]
    else:
        x=k.var(prefix+'x',a[0]);f=k.var(prefix+'f',a)
        out.append(k.lam(prefix+'l',x,k.app(prefix+'a',f,x)))
        for sz in range(1,6):
            asts=g.generate(a,(),sz)
            if asts:
                out.append(g.instantiate(asts[0],prefix+'closed',()));break
    return out

def two_flags(t):
    result=Counter()
    for f1,r1,_ in k.coaction(t):
        for f2,r2,_ in k.coaction(r1):
            result[(tuple(sorted((k.key(p) for p in f1),key=repr)),
                    tuple(sorted((k.key(p) for p in f2),key=repr)),
                    k.key(mm.island.normalize(r2)))]+=1
    return result

def test_pair(a,b,totals):
    assert k.check(a)==k.check(b) and a.typ==b.typ
    if mm.modes(a)!=mm.modes(b):totals['mode_unequal_pairs_rejected']+=1;return
    totals['mode_equal_pairs']+=1
    for x,typ in k.check(a):
        for i,p in enumerate(fillers(typ,f'fill_{x}_')):
            sa,sb=k.substitute(a,x,p),k.substitute(b,x,p)
            assert mm.modes(sa)==mm.modes(sb),('SUBSTITUTION_COUNTEREXAMPLE',a,b,p)
            totals['substitution_probes']+=1
            assert mm.island.profile(sa,True)==mm.island.profile(sb,True)
            totals['direct_coaction_checks']+=1
            if totals['substitution_probes']<=180:
                fa,fb=two_flags(sa),two_flags(sb)
                assert fa==fb,'nested material flag mismatch'
                totals['two_stage_flag_checks']+=1
                totals['two_stage_flag_terms']+=sum(fa.values())
                totals['nonempty_two_stage_flag_terms']+=sum(v for (f1,f2,r),v in fa.items() if f1 and f2)
            totals['open_filler_probes']+=bool(k.check(p))
            totals['compound_input_probes']+=not k.atomic(typ)
    # Logical application context works for all conclusion types.
    f=k.var('envelope_f',k.arr(a.typ,'p'))
    assert mm.modes(k.app('envelope_a',f,a))==mm.modes(k.app('envelope_a',f,b))
    totals['logical_context_probes']+=1
    if k.atomic(a.typ):
        def wrap(u):return k.prim('envelope_r','envelope',(u.typ,),'p',u)
        assert mm.modes(wrap(a))==mm.modes(wrap(b))
        totals['material_context_probes']+=1
        atomics=[(x,t) for x,t in k.check(a) if k.atomic(t)]
        if atomics:
            bound=atomics[0]
            def discharge(u):return k.T('prim','envelope_hyp','p',(u,),('hyp',(u.typ,),((bound,),)))
            assert mm.modes(discharge(a))==mm.modes(discharge(b))
            totals['hypothetical_discharge_probes']+=1
    for x,t in k.check(a):
        v=k.var(x,t)
        assert mm.modes(k.lam('envelope_lam',v,a))==mm.modes(k.lam('envelope_lam',v,b))
        totals['binder_context_probes']+=1

def main():
    totals=Counter()
    contexts=(((0,'p'),),((0,g.A),),((0,'p'),(1,'p')),((0,g.A),(1,'p')))
    for ctx in contexts:
        for typ in g.TYPES:
            for sz in range(1,9):
                for ast in g.generate(typ,ctx,sz):
                    t=g.instantiate(ast,f'm{totals["generated_terms"]}',ctx)
                    totals['generated_terms']+=1
                    for u in k.one_steps(t,atomic_beta=True):test_pair(t,u,totals)
    result={'status':'BOUNDED_CHECKS_PASS','totals':dict(totals),
            'scope':'mode-equal one-step beta/eta pairs; generated finite substitutions and contexts; no universal theorem claimed'}
    Path(__file__).with_name('material_modes_validation_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
