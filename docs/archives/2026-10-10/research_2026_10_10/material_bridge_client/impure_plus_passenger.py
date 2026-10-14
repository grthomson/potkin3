"""Exploratory combined normalizer; finite tests, no theorem claimed here."""
from collections import Counter
from pathlib import Path
import json
import check_bridge as k
import enumerated_validation as gen
import impure_normalizer as imp
import source_reification as source


def size(t):return int(t.kind!='hole')+sum(size(c) for c in t.children)
def materials(t):return int(t.kind=='prim')+sum(materials(c) for c in t.children)
def measure(t):
    def weight(u):
        own=materials(u.children[0].children[0]) if u.kind=='app' and u.children[0].kind=='lam' else 0
        return own+sum(weight(c) for c in u.children)
    return size(t),weight(t)


def root_steps(t):
    result=[]
    if t.kind=='app' and t.children[0].kind=='lam':
        fn,p=t.children;x,a=fn.meta;body=fn.children[0]
        if imp.impure(p):result.append(('beta',k.substitute(body,x,p)))
        if k.atomic(a) and body.kind=='prim':
            active=[i for i,c in enumerate(body.children) if x in dict(k.check(c))]
            if len(active)==1:
                i=active[0]
                # x is genuinely free at the material conclusion, not one of
                # that primitive's discharged atomic assumptions.
                assert x in dict(k.check(body))
                child=body.children[i]
                discharged=body.meta[2] if len(body.meta)>2 else tuple(() for _ in body.children)
                bound_tokens={u for entries in discharged for u,_ in entries}
                assert not (bound_tokens & set(dict(k.check(p)))), 'passenger would capture primitive discharge token'
                moved_lam=k.T('lam',fn.uid,k.arr(a,child.typ),(child,),fn.meta)
                moved_app=k.T('app',t.uid,child.typ,(moved_lam,p))
                cs=list(body.children);cs[i]=moved_app
                result.append(('passenger',k.T('prim',body.uid,body.typ,tuple(cs),body.meta)))
    if t.kind=='lam' and t.children[0].kind=='app':
        f,p=t.children[0].children
        if p.kind=='var' and p.uid==t.meta[0] and p.uid not in dict(k.check(f)):
            result.append(('eta',f))
    return result


def steps(t):
    if t.kind=='hole':assert not t.meta,'actual-origin empty-context holes required'
    result=root_steps(t)
    for i,c in enumerate(t.children):
        for label,u in steps(c):
            cs=list(t.children);cs[i]=u
            result.append((label,k.T(t.kind,t.uid,t.typ,tuple(cs),t.meta)))
    for label,u in result:
        assert k.check(u)==k.check(t) and u.typ==t.typ
        assert measure(u)<measure(t),(label,measure(t),measure(u))
        assert imp.impure(u)==imp.impure(t)
    return result


def normal(t):
    while (s:=steps(t)):t=s[0][1]
    return t


def all_forms(t):
    pending,seen,outputs=[t],set(),set()
    labels=Counter()
    while pending:
        u=pending.pop()
        if u in seen:continue
        seen.add(u);s=steps(u)
        if not s:outputs.add(k.key(u))
        for label,v in s:labels[label]+=1;pending.append(v)
    return outputs,len(seen),labels


def profile(t,normalize_right):
    return Counter((tuple(sorted((k.key(p) for p in f),key=repr)),
                    k.key(normal(r) if normalize_right else r)) for f,r,_ in k.coaction(t))


def validate(t):
    forms,count,labels=all_forms(t)
    assert len(forms)==1,('NONCONFLUENT_FINITE_WITNESS',t,forms)
    pending,seen,terms=[t],set(),0
    while pending:
        u=pending.pop()
        if u in seen:continue
        seen.add(u);nu=normal(u)
        assert all(not steps(r) for _,r,_ in k.coaction(nu))
        assert profile(u,True)==profile(nu,False)
        for _,r,roots in k.coaction(u):
            terms+=1
            if roots:pending.append(r)
    return count,len(seen),terms,labels


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
        assert all(not steps(r) for _,r,_ in k.coaction(final))
        states,residuals,terms,_=validate(target)
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
                assert k.key(nl)==k.key(nr)
                validate(l);validate(r)
                rows.append({'argument':argument,'slot':slot,'envelope':envelope,
                             'normalized_relation':'equal'})
    return rows


def main():
    totals=Counter();edge_labels=Counter()
    contexts=((),((0,gen.A),),((0,k.arr(gen.A,gen.A)),),
              ((0,gen.A),(1,gen.P)),((0,k.arr(gen.A,gen.A)),(1,gen.A)))
    for context in contexts:
        for typ in gen.TYPES:
            for sz in range(1,11):
                for ast in gen.generate(typ,context,sz):
                    t=gen.instantiate(ast,f'c{totals["terms"]}',context)
                    a,b,c,labels=validate(t)
                    totals['terms']+=1;totals['rewrite_states']+=a
                    totals['residual_states']+=b;totals['cut_terms']+=c
                    totals['changed_from_Nimp']+=k.key(normal(t))!=k.key(imp.normal(t))
                    edge_labels.update(labels)
    # The exact generalized passenger/eta counterexample now has a common NF.
    x=k.var('gate_x','p');f=k.var('gate_f',k.arr('p','q'))
    d=k.prim('gate_d','delta',(),'p')
    active=k.app('gate_active',f,x)
    body=k.prim('gate_r','r',('q',),'s',active)
    left=k.app('gate_cut',k.lam('gate_lam',x,body),d)
    right=k.prim('gate_r','r',('q',),'s',k.app('gate_cut',k.lam('gate_lam',x,active),d))
    assert k.key(normal(left))==k.key(normal(right))
    validate(left);validate(right)
    # A genuine old hypothetical-discharge witness is also checked.
    m,decode=source.fixture(hypothetical=True)
    target=source.naturalise(m,decode)
    hyp=validate(target)
    result={'status':'FINITE_CHECKS_PASS','policy':'N_imp plus atomic Cut passenger inward through a selected material root',
            'totals':dict(totals),'rewrite_edge_labels':dict(edge_labels),
            'general_passenger_eta_peak_joins':True,
            'direct_shadow_reification':reification_checks(),
            'reference_passenger_probes':reference_passenger_probes(),
            'discharge_capture_side_condition':'primitive bound tokens disjoint from argument free context',
            'hypothetical_fixture':{'rewrite_states':hyp[0],'residual_states':hyp[1],'cut_terms':hyp[2]},
            'termination_measure_checked':'lex(positive size,total material vertices inside explicit beta bodies)',
            'scope':'exploratory bounded evidence; no general confluence or all-permutation quotient theorem claimed'}
    Path(__file__).with_name('impure_plus_passenger_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
