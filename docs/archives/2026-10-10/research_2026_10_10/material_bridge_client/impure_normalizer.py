"""Separate candidate: beta with an impure positive argument, plus eta.

Does not mutate check_bridge.normal or its compound-domain policy.
"""
from collections import Counter
from pathlib import Path
import json
import check_bridge as k
import enumerated_validation as gen
from sequent_gate import passenger
import source_reification as source


def impure(t):
    return t.kind not in ('prim', 'hole') or any(impure(c) for c in t.children)


def one_steps(t):
    if t.kind == 'hole':
        assert not t.meta, 'N_imp requires actual-origin holes with empty free context'
    result = []
    if t.kind == 'app' and t.children[0].kind == 'lam':
        f, p = t.children
        if impure(p): result.append(k.substitute(f.children[0], f.meta[0], p))
    if t.kind == 'lam' and t.children[0].kind == 'app':
        f, p = t.children[0].children
        if p.kind == 'var' and p.uid == t.meta[0] and p.uid not in dict(k.check(f)):
            result.append(f)
    for i,c in enumerate(t.children):
        for reduced in one_steps(c):
            cs = list(t.children);cs[i] = reduced
            result.append(k.T(t.kind,t.uid,t.typ,tuple(cs),t.meta))
    for u in result:
        assert k.check(t) == k.check(u) and t.typ == u.typ
        assert impure(t) == impure(u), 'impurity guard not invariant'
    return result


def normal(t):
    while (steps := one_steps(t)): t = steps[0]
    return t


def normal_forms(t):
    pending, seen, outputs = [t],set(),set()
    while pending:
        u=pending.pop()
        if u in seen:continue
        seen.add(u)
        steps=one_steps(u)
        if steps:pending.extend(steps)
        else:outputs.add(k.key(u))
    return outputs,len(seen)


def profile(t, normalize_right):
    return Counter((tuple(sorted((k.key(p) for p in forest),key=repr)),
                    k.key(normal(r) if normalize_right else r))
                   for forest,r,roots in k.coaction(t))


def validate(t):
    k.check(t)
    forms,states=normal_forms(t)
    assert len(forms)==1
    pending,seen,terms=[t],set(),0
    while pending:
        u=pending.pop()
        if u in seen:continue
        seen.add(u)
        nu=normal(u)
        assert all(not one_steps(r) for _,r,_ in k.coaction(nu))
        assert profile(u,True)==profile(nu,False)
        for forest,r,roots in k.coaction(u):
            assert impure(r)==impure(u), 'material opening lost an impure blocker'
            terms+=1
            if roots:pending.append(r)
    return states,len(seen),terms


def reification_checks():
    rows=[]
    for name,kwargs in [('binary_old_rule',{}),('repeated_atomic_boundary',{'repeated':True}),
                        ('nested_nonprimitive_material',{'nested':True}),
                        ('old_hypothetical_atomic_discharge',{'hypothetical':True})]:
        m,decode=source.fixture(**kwargs)
        assert source.source_check(m)==()
        target=source.naturalise(m,decode)
        final=normal(target)
        assert k.check(final)==() and final.typ==m.atom
        exact=Counter()
        for roots in source.antichains(m):
            r,forest=source.source_cut(m,set(roots))
            assert source.source_check(r)==()
            left=tuple(sorted((k.key(source.naturalise(p,decode)) for p in forest),key=repr))
            right=k.key(normal(source.naturalise(r,decode)))
            exact[(left,right)]+=1
        assert exact==profile(final,False)
        assert all(not one_steps(r) for _,r,_ in k.coaction(final))
        states,residuals,terms=validate(target)
        rows.append({'name':name,'status':'PASS','source_antichain_terms':sum(exact.values()),
                     'normal_output_kind':final.kind,'rewrite_states':states,
                     'material_residual_states':residuals,'residual_cut_terms':terms})
    return rows


def reference_passenger_probes():
    rows=[]
    for argument in ('pure','ref','logical'):
        for slot in (0,1):
            x=k.var('probe_x','p')
            if argument=='pure':p=k.prim('probe_delta','delta_p',(),'p')
            elif argument=='ref':p=k.var('probe_y','p')
            else:
                p=k.app('probe_logical',k.var('probe_f',k.arr('p','p')),
                        k.prim('probe_delta','delta_p',(),'p'))
            side=k.prim('probe_side','delta_q',(),'q')
            children=(x,side) if slot==0 else (side,x)
            body=k.prim('probe_r','r',tuple(c.typ for c in children),'s',*children)
            left=k.app('probe_cut',k.lam('probe_lam',x,body),p)
            identity=k.lam('probe_lam',x,x)
            targetchildren=list(children);targetchildren[slot]=k.app('probe_cut',identity,p)
            right=k.T('prim',body.uid,body.typ,tuple(targetchildren),body.meta)
            for envelope in ('bare','material_parent'):
                l,r=left,right
                if envelope=='material_parent':
                    l=k.prim('probe_parent','h',('s',),'u',l)
                    r=k.prim('probe_parent','h',('s',),'u',r)
                nl,nr=normal(l),normal(r)
                if argument=='pure':
                    # The κ cell persists with normalized parameters; strict
                    # equality is neither expected nor claimed in this case.
                    assert k.key(nl)==k.key(l) and k.key(nr)==k.key(r)
                    assert k.key(nl)!=k.key(nr)
                else:assert k.key(nl)==k.key(nr)
                validate(l);validate(r)
                rows.append({'argument':argument,'slot':slot,'envelope':envelope,
                             'normalized_relation':'same_explicit_passenger_cell' if argument=='pure' else 'equal'})
    return rows


def main():
    contexts=((),((0,gen.A),),((0,k.arr(gen.A,gen.A)),),
              ((0,gen.A),(1,gen.P)),((0,k.arr(gen.A,gen.A)),(1,gen.A)))
    totals=Counter()
    for context in contexts:
        for typ in gen.TYPES:
            for size in range(1,11):
                for ast in gen.generate(typ,context,size):
                    prefix=f'i{totals["terms"]}'
                    t=gen.instantiate(ast,prefix,context)
                    assert k.check(t)==tuple(sorted((f'{prefix}_free_{v}',a) for v,a in context))
                    assert t.typ==typ
                    states,residuals,terms=validate(t)
                    totals['terms']+=1;totals['rewrite_states']+=states
                    totals['residual_states']+=residuals;totals['cut_terms']+=terms
                    totals['strict_improvements_over_type_guard']+=k.key(normal(t))!=k.key(k.normal(t))
    # Exact mixed passenger/eta peak which broke N_c now joins.
    x,y=k.var('peak_x','p'),k.var('peak_y','p')
    b=k.prim('peak_b','delta_q',(),'q')
    body=k.prim('peak_r','r',('p','q'),'s',x,b)
    inner=k.app('peak_app',k.lam('peak_lam',x,body),y)
    left=k.lam('peak_outer',y,inner)
    right=k.lam('peak_outer',y,passenger(inner))
    assert k.key(normal(left))==k.key(normal(right))
    validate(left);validate(right)
    # Pure material and zero-positive hole arguments are deliberately blocked.
    z=k.var('block_z','p')
    identity=k.lam('block_lam',z,z)
    pure=k.prim('block_delta','delta',(),'p')
    hole=k.T('hole','block_hole','p')
    assert not one_steps(k.app('blocked_pure',identity,pure))
    assert not one_steps(k.app('blocked_hole',identity,hole))
    hidden=k.T('hole','hidden_atomic_input','p',(),(('hidden_x','p'),))
    try:
        one_steps(hidden)
        raise AssertionError('artificial atomic-input hole accepted')
    except AssertionError as e:
        assert e.args[0]=='N_imp requires actual-origin holes with empty free context'
    # General Cut/r permutation with a nontrivial active premise still fails.
    gx=k.var('general_x','p');gf=k.var('general_f',k.arr('p','q'))
    gd=k.prim('general_delta','delta_p',(),'p')
    active=k.app('general_f_apply',gf,gx)
    gr=k.prim('general_r','r',('q',),'s',active)
    general_left=k.app('general_cut',k.lam('general_lam',gx,gr),gd)
    general_right=k.prim('general_r','r',('q',),'s',
        k.app('general_cut',k.lam('general_lam',gx,active),gd))
    assert k.check(general_left)==k.check(general_right)
    def size(t):return 1+sum(size(c) for c in t.children)
    gl,gt=normal(general_left),normal(general_right)
    assert size(general_left)==size(general_right)==7
    assert size(gl)==7 and size(gt)==4
    assert not one_steps(gl) and not one_steps(gt)
    validate(general_left);validate(general_right)
    result={'status':'PASS','policy':'beta iff argument has a positive nonmaterial vertex; all implication eta',
            'bounded_generator':{'maximum_nodes':10,'per_state_cap':gen.CAP},
            'totals':dict(totals),'passenger_eta_peak_joins':True,
            'pure_material_and_zero_positive_hole_beta_blocked':True,
            'artificial_atomic_input_hole_rejected':True,
            'general_passenger_non_descent':{'source_sizes':[7,7],'normal_image_sizes':[7,4],
                'invariant':'contextual general Cut/r permutation preserves node count'},
            'direct_shadow_reification':reification_checks(),
            'reference_passenger_probes':reference_passenger_probes(),
            'scope':'finite exact typed/material-coaction evidence; general confluence remains a paper theorem'}
    Path(__file__).with_name('impure_normalizer_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
