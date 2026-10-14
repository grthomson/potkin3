"""Exact-state residual tests and independent bounded literal-cut enumeration."""
import json
from itertools import product
from typed_checker import *

RULES=(Rule('a',(),'P'),Rule('b',(),'P'),Rule('u',('P',),'P'),
       Rule('f',('P','P'),'P'),Rule('z',(),'Q'),Rule('embed',('P',),'Q'))

def mask_rule(r,qs):
    if r=='a': return 1
    if r=='b': return 2
    if r=='z': return 0
    ans=0
    for q in qs: ans|=q
    return ans

# Exactly two providers of identical, pure a/b support. Full correlation is
# necessary: independent projections admit a,b, which violates the target.
def corr_step(u,letter):
    s,q=letter
    if s!='P' or q not in (1,2): return 'dead'
    if u=='start': return 'a1' if q==1 else 'b1'
    if (u,q) in (('a1',1),('b1',2)): return 'yes'
    return 'dead'


def correlation_model():
    return Model(RULES,mask_rule,('start','a1','b1','yes','dead'),
                 'start',{'yes'},corr_step,lambda s,q:q!=3)


def height_rule(r,qs):
    if r=='u': return min(2,1+qs[0])
    return max(qs,default=0)


def ancestry_model():
    return Model(RULES,height_rule,(0,1),0,{0},
                 lambda u,sq:int(bool(u or sq[1]!=0)),lambda s,q:q<=1)


def direct_relation(model,skeleton):
    """Literal finite representative filling, separately from recursion."""
    out=set()
    hs=holes(skeleton)
    for qs in product(*(model.reachable[s] for s in hs)):
        ps=tuple(model.witness[s][q] for s,q in zip(hs,qs))
        q=model.observe(fill(model,skeleton,ps))
        for initial in model.word_states:
            final=initial
            for p in ps: final=model.word_step(final,model.letter(p))
            out.add((initial,q,final))
    return frozenset(out)


def check_model(model,bound):
    trees=trees_up_to(model,bound)
    seen_skeletons=set()
    cuts_count=0
    for t in trees:
        direct_states=set()
        direct_query=False
        for material,ctx in direct_cuts(model,t):
            cuts_count+=1
            assert fill(model,ctx,material)==t
            assert holes(ctx)==tuple(model.sort(p) for p in material)
            if ctx not in seen_skeletons:
                seen_skeletons.add(ctx)
                assert direct_relation(model,ctx)==model.relation(ctx)
                ce=model.counterexample(ctx)
                assert (ce is None)==model.residual_accepts(ctx)
                if ce:
                    providers,assembly=ce
                    assert model.provider_accepts(providers)
                    assert not model.good(model.sort(assembly),model.observe(assembly))
            action=model.compose_actions(tuple(model.letter_action(model.letter(p)) for p in material))
            direct_states.add((action,model.relation(ctx)))
            direct_query|=model.provider_accepts(material) and model.residual_accepts(ctx)
        assert frozenset(direct_states)==model.cut_summary(t)
        assert direct_query==model.query(t)
    context_states,context_rounds=saturate_context_states(model)
    for sort,states in context_states.items():
        for rel,ctx in states.items():
            assert rel==direct_relation(model,ctx)
            assert (model.counterexample(ctx) is None)==model.relation_accepts(sort,rel)
    return dict(trees=len(trees),literal_cuts=cuts_count,
                all_context_state_counts={s:len(v) for s,v in context_states.items()},
                context_saturation_rounds=context_rounds,
                distinct_skeletons=len(seen_skeletons),
                reachable_states={s:len(qs) for s,qs in model.reachable.items()},
                saturation_rounds=model.saturation_rounds)


def main():
    corr=correlation_model()
    h=Hole('P')
    ctx=Tree('f',(h,h))
    assert corr.residual_accepts(ctx)
    assert corr.provider_accepts((Tree('a'),Tree('a')))
    assert corr.provider_accepts((Tree('b'),Tree('b')))
    assert not corr.provider_accepts((Tree('a'),Tree('b')))
    assert not corr.good('P',corr.observe(fill(corr,ctx,(Tree('a'),Tree('b')))))
    # A different observer on the SAME proof objects tests ancestry.
    anc=ancestry_model()
    flat=Tree('f',(Tree('u',(Tree('a'),)),Tree('u',(Tree('a'),))))
    nested=Tree('u',(Tree('f',(Tree('u',(Tree('a'),)),Tree('a'))),))
    def bag(t):
        from collections import Counter
        return Counter([t.rule])+sum((bag(c) for c in t.children),Counter())
    assert bag(flat)==bag(nested)
    assert anc.good('P',anc.observe(flat)) and not anc.good('P',anc.observe(nested))
    flat_open=Tree('f',(Tree('u',(h,)),Tree('u',(h,))))
    nested_open=Tree('u',(Tree('f',(Tree('u',(h,)),h)),))
    assert anc.residual_accepts(flat_open)
    assert not anc.residual_accepts(nested_open)
    assert anc.counterexample(nested_open) is not None
    # Typed top extraction remains a hole, whereas the empty extraction is
    # a closed tree. They differ in hole count and residual semantics.
    a=Tree('a')
    cuts=list(direct_cuts(corr,a))
    assert cuts==[((a,),h),((),a)]
    assert corr.relation(h)!=corr.relation(a)
    try: fill(corr,h,(Tree('z'),))
    except ValueError: pass
    else: raise AssertionError('sort error not rejected')
    # Vacuity is intentional and must remain distinct from nonempty contracts.
    assert corr.residual_accepts(h) and corr.counterexample(h) is None
    assert not any(u==corr.word_initial and v in corr.word_final for u,q,v in corr.relation(h))
    results={'correlated_provider':check_model(corr,6),
             'ancestry':check_model(anc,6),
             'special_checks':['correlation versus independent projections',
                 'same multiset different ancestry', 'typed root versus empty endpoints',
                 'sort rejection','vacuous residual explicit'],
             'scope':'Exact finite state saturation; exhaustive literal cuts and representative fillings for all sorted closed trees of size <= 6; not Lean mechanization.'}
    with open('research_round3/typed_checker_results.json','w') as f:
        json.dump(results,f,indent=2)
    print(json.dumps(results,indent=2))

if __name__=='__main__': main()
