"""D4 generic residual instantiated by positive-exponential demand observer.
Fixed finite scope/type registry, but unbounded recursively nested providers.
"""
from typed_checker import *
from test_typed_checker import direct_relation
import check_natural_demand as N
import json

BUDGET=2
CAP=BUDGET+1
RULES=(Rule('aC',(),'C'),Rule('gC',('C',),'C'),Rule('mergeC',('C','C'),'C'),
       Rule('bang',('C',),'B'),Rule('let',('B','O'),'C'),
       Rule('aO',(),'O'),Rule('x',(),'O'),Rule('gO',('O',),'O'),
       Rule('mergeO',('O','O'),'O'))

def obs(r,qs):
    if r in ('aC','aO'): return 0,0
    if r=='x': return 0,1
    if r in ('gC','gO'): return min(CAP,qs[0][0]+1),qs[0][1]
    if r in ('mergeC','mergeO'):
        return tuple(min(CAP,a+b) for a,b in zip(*qs))
    if r=='bang': return qs[0]
    if r=='let':
        (cp,_),(cq,dq)=qs
        return min(CAP,cq+dq*cp),0
    raise ValueError(r)

def word_step(u,letter):
    s,(c,d)=letter
    if u=='start' and s=='B': return ('provider',c)
    if isinstance(u,tuple) and s=='O':
        return 'yes' if c+d*u[1]<=BUDGET else 'no'
    return 'no'


def model():
    return Model(RULES,obs,('start','yes','no')+tuple(('provider',c) for c in range(CAP+1)),
                 'start',{'yes'},word_step,lambda s,q:q[0]<=BUDGET)


def native(t):
    r=t.rule
    cs=tuple(native(c) for c in t.children)
    if r in ('aC','aO'): return N.A()
    if r=='x': return N.V('x')
    if r in ('gC','gO'): return N.G(cs[0])
    if r in ('mergeC','mergeO'): return N.M(*cs)
    if r=='bang': return N.B(cs[0])
    if r=='let': return N.L('x',*cs)
    raise ValueError(r)


def main():
    m=model()
    trees=trees_up_to(m,7)
    native_checks=0
    cuts=0
    for t in trees:
        s=m.sort(t)
        n=native(t)
        env={'x':N.P} if s=='O' else {}
        assert N.typ(n,env)==(N.Bang(N.P) if s=='B' else N.P)
        c,d=N.demand(n,CAP)
        assert m.observe(t)==(c,d['x'])
        if s!='O':
            assert m.observe(t)[0]==min(CAP,N.gcount(N.normal(n,{})))
        else:
            for cost in range(4):
                v=N.closed(N.P,cost)
                assert min(CAP,c+d['x']*cost)==min(CAP,N.gcount(N.normal(n,{'x':v})))
        native_checks+=1
        direct=set()
        for material,ctx in direct_cuts(m,t):
            cuts+=1
            assert fill(m,ctx,material)==t
            action=m.compose_actions(tuple(m.letter_action(m.letter(p)) for p in material))
            direct.add((action,m.relation(ctx)))
        assert direct==set(m.cut_summary(t))
    ctx=Tree('let',(Hole('B'),Hole('O')))
    assert m.relation(ctx)==direct_relation(m,ctx)
    assert m.residual_accepts(ctx)
    assert any(u=='start' and v=='yes' for u,q,v in m.relation(ctx))
    unsafe=Tree('gC',(ctx,))
    assert not m.residual_accepts(unsafe)
    providers,assembled=m.counterexample(unsafe)
    assert m.provider_accepts(providers)
    actual_cost=N.gcount(N.normal(native(assembled),{}))
    assert actual_cost>BUDGET
    # Non-rectangular contract: both pairs accepted, crossed pair forbidden.
    expensive=Tree('bang',(Tree('gC',(Tree('gC',(Tree('aC'),)),)),))
    cheap=Tree('bang',(Tree('aC'),))
    erase=Tree('aO')
    duplicate=Tree('mergeO',(Tree('x'),Tree('x')))
    assert m.provider_accepts((expensive,erase))
    assert m.provider_accepts((cheap,duplicate))
    assert not m.provider_accepts((expensive,duplicate))
    # A single context branch may duplicate the whole opaque provider.
    ampl=Tree('gC',(Tree('aC'),))
    for _ in range(7): ampl=Tree('let',(Tree('bang',(ampl,)),duplicate))
    assert N.gcount(N.normal(native(ampl),{}))==128
    assert m.observe(ampl)==(CAP,0)
    result={'budget':BUDGET,'reachable_joint_states':{s:len(qs) for s,qs in m.reachable.items()},
            'provider_saturation_rounds':m.saturation_rounds,'typed_terms_native_checked':native_checks,
            'literal_ck_cuts_checked':cuts,'max_tree_size':7,
            'universal_let_contract_nonvacuous':True,'outer_g_counterexample_actual_cost':actual_cost,
            'correlation_cross_product_counterexample':True,'seven_level_normal_form_g_nodes':128,
            'scope':'Finite types and scope; unbounded terms. Natural observer checked against independent substitution normalizer. Tests are not a general cut-elimination theorem or time-cost model.'}
    with open('research_round3/typed_natural_results.json','w') as f: json.dump(result,f,indent=2)
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
