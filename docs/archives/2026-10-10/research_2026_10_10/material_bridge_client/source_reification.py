"""Finite direct shadow-naturalisation check; not semantic completeness evidence.

Source typing is generic atomic App with explicitly routed discharged atoms.
Executed old rules include ordinary positive arity and an actual hypothetical
atomic-discharge instance with a checked linear premise witness.
"""
from dataclasses import dataclass
from collections import Counter
from itertools import product
from pathlib import Path
import json
import check_bridge as nd


@dataclass(frozen=True)
class Rule:
    tag: str
    kind: str
    inputs: tuple
    output: str
    # One tuple of intrinsic discharged atomic types per premise.
    discharged: tuple


@dataclass(frozen=True)
class S:
    uid: str
    atom: str
    kind: str
    children: tuple = ()
    rule: object = None
    # Concrete occurrence IDs routed to the corresponding discharged entries.
    binders: tuple = ()
    interface: tuple = ()


def source_check(t):
    def walk(u, seen):
        assert u.uid not in seen, ('duplicate source occurrence', u.uid)
        seen.add(u.uid)
        assert isinstance(u.atom, str)
        if u.kind == 'ref': return ((u.uid, u.atom),)
        if u.kind == 'hole':
            assert not u.children
            return u.interface
        r = u.rule
        assert r.output == u.atom
        assert len(r.inputs) == len(u.children) == len(r.discharged) == len(u.binders)
        result = []
        for c, a, ds, bs in zip(u.children, r.inputs, r.discharged, u.binders):
            assert c.atom == a and len(ds) == len(bs)
            context = dict(walk(c, seen))
            for x, expected in zip(bs, ds):
                assert context.pop(x) == expected
            result.append(tuple(context.items()))
        return nd.merge(result)
    return walk(t, set())


def apply(uid, r, *children, binders=None):
    bs = tuple(() for _ in children) if binders is None else binders
    return S(uid, r.output, 'rule', tuple(children), r, bs)


def pure(t):
    return t.kind == 'hole' or (t.kind == 'rule' and t.rule.kind == 'old' and all(map(pure, t.children)))


def antichains(t):
    result = [sum(parts, ()) for parts in product(*(antichains(c) for c in t.children))]
    if t.kind == 'rule' and t.rule.kind == 'old' and pure(t): result.append((t.uid,))
    return result


def source_cut(t, roots):
    if t.uid in roots:
        return S(t.uid, t.atom, 'hole', interface=source_check(t)), (t,)
    children, forest = [], ()
    for c in t.children:
        residual, part = source_cut(c, roots)
        children.append(residual)
        forest += part
    return S(t.uid, t.atom, t.kind, tuple(children), t.rule, t.binders, t.interface), forest


def naturalise(t, decode):
    typ = decode.get(t.atom, t.atom)
    if t.kind == 'ref': return nd.var(t.uid, typ)
    if t.kind == 'hole':
        context = tuple((x, decode.get(a, a)) for x, a in t.interface)
        assert nd.atomic(typ) and all(nd.atomic(a) for _, a in context), 'nonmaterial-origin source hole'
        return nd.T('hole', t.uid, typ, (), context)
    args = tuple(naturalise(c, decode) for c in t.children)
    if t.rule.kind == 'old':
        assert all(a not in decode for a in t.rule.inputs + (t.atom,)), 'old/shadow vocabulary collision'
        if any(t.rule.discharged):
            discharges = tuple(tuple(zip(bs, ds)) for bs, ds in zip(t.binders, t.rule.discharged))
            return nd.T('prim', t.uid, t.atom, args, (t.rule.tag, t.rule.inputs, discharges))
        return nd.prim(t.uid, t.rule.tag, t.rule.inputs, t.atom, *args)
    if t.rule.kind == 'SI':
        assert len(args) == 1 and len(t.binders[0]) == 1
        x = nd.var(t.binders[0][0], decode.get(t.rule.discharged[0][0], t.rule.discharged[0][0]))
        out = nd.lam(t.uid, x, args[0])
    elif t.rule.kind == 'SE':
        assert len(args) == 2
        out = nd.app(t.uid, args[0], args[1])
    else: raise AssertionError(t.rule.kind)
    assert out.typ == typ
    return out


def fixture(repeated=False, nested=False, hypothetical=False):
    # The enlarged subformula-closed Xi contains F and F-o-w, in addition to
    # final w. Its shadows are tagged, disjoint from all old primitive atoms.
    F, G = '@F', '@G'
    decode = {F: nd.arr('s', 'w'), G: nd.arr(nd.arr('s', 'w'), 'w')}
    q = 'p' if repeated else 'q'
    a = apply('a', Rule('delta_p', 'old', (), 'p', ()))
    b = apply('b', Rule('delta_q', 'old', (), q, ()))
    t = apply('r', Rule('r', 'old', ('p', q), 's', ((), ())), a, b)
    if nested:
        t = apply('g', Rule('g', 'old', ('s',), 's', ((),)), t)
    if hypothetical:
        # Real witness of p |- q; r discharges precisely its p occurrence.
        a_h = apply('a_h', Rule('delta_v', 'old', (), 'v', ()))
        pure_inner = apply('g_h', Rule('g', 'old', ('v',), 'u', ((),)), a_h)
        hyp = S('hyp_p', 'p', 'ref')
        premise = apply('k_h', Rule('k', 'old', ('p', 'u'), 'q', ((), ())), hyp, pure_inner)
        t = apply('r_h', Rule('r_discharge', 'old', ('q',), 's', (('p',),)),
                  premise, binders=(('hyp_p',),))
    f, x = S('f', F, 'ref'), S('x', 's', 'ref')
    use_f = apply('apply_f', Rule('E_F', 'SE', (F, 's'), 'w', ((), ())), f, t)
    left = apply('abstract_f', Rule('I_G', 'SI', ('w',), G, ((F,),)), use_f, binders=(('f',),))
    hx = apply('h', Rule('h', 'old', ('s',), 'w', ((),)), x)
    right = apply('abstract_x', Rule('I_F', 'SI', ('w',), F, (('s',),)), hx, binders=(('x',),))
    root = apply('outer_apply', Rule('E_G', 'SE', (G, F), 'w', ((), ())), left, right)
    return root, decode


def run_one(name, root, decode, expected_gain=1):
    assert source_check(root) == ()
    target = naturalise(root, decode)
    assert nd.check(target) == () and target.typ == root.atom
    source_profile = Counter()
    roots_checked = 0
    for selected in antichains(root):
        residual, forest = source_cut(root, set(selected))
        assert source_check(residual) == source_check(root)
        # Material forests must contain no shadow atom in any complete seam.
        for p in forest:
            assert p.atom not in decode and all(a not in decode for _, a in source_check(p))
        left = tuple(sorted((nd.key(naturalise(p, decode)) for p in forest), key=repr))
        right = nd.key(nd.normal(naturalise(residual, decode)))
        source_profile[(left, right)] += 1
        roots_checked += 1
    final = nd.normal(target)
    assert source_profile == nd.profile(final, normalize_residuals=False)
    # Naturalisation alone also matches literal cut roots and ordered forest
    # tuples; normalization uses the declared commutative observer.
    for selected in antichains(root):
        sr, sf = source_cut(root, set(selected))
        tr, tf = nd.cut(target, set(selected))
        assert tuple(nd.key(naturalise(p, decode)) for p in sf) == tuple(nd.key(p) for p in tf)
        assert nd.key(naturalise(sr, decode)) == nd.key(tr)
    excluded = nd.one_steps(final, atomic_beta=True)
    assert len(excluded) == 1
    gain = nd.profile(excluded[0], normalize_residuals=False)
    assert len(gain) == len(source_profile) + expected_gain
    return {'name': name, 'status': 'PASS', 'source_atomic_type': root.atom,
            'native_antichain_terms': roots_checked, 'normal_output_kind': final.kind,
            'excluded_atomic_step_new_terms': len(gain)-len(source_profile)}


def main():
    rows = [run_one(name, *fixture(rep, nest)) for name, rep, nest in
            [('binary_old_rule', False, False), ('repeated_atomic_boundary', True, False),
             ('nested_nonprimitive_material', False, True)]]
    hyp_root, hyp_decode = fixture(hypothetical=True)
    rows.append(run_one('old_hypothetical_atomic_discharge', hyp_root, hyp_decode, expected_gain=0))
    # Deliberate bad source-profile tags are rejected, not silently decoded
    # into a compound material primitive.
    caught = False
    try:
        bad = apply('bad', Rule('bad_old', 'old', (), '@F', ()))
        naturalise(bad, {'@F': nd.arr('p','q')})
    except AssertionError: caught = True
    assert caught
    bad_hole_rejected = False
    try:
        hole = S('bad_hole', 'p', 'hole', interface=(('hidden', '@A'),))
        envelope = apply('bad_envelope', Rule('r_env', 'old', ('p',), 'q', ((),)), hole)
        assert source_check(envelope) == (('hidden', '@A'),)
        naturalise(envelope, {'@A': nd.arr('p', 'q')})
    except AssertionError: bad_hole_rejected = True
    assert bad_hole_rejected
    report = {'fixtures': rows, 'old_shadow_collision_rejected': caught,
              'hidden_compound_input_hole_rejected': bad_hole_rejected,
              'scope': 'Finite source App/target NIMLL checks including one genuine old hypothetical atomic discharge; no support completeness or all-rules proof.'}
    Path(__file__).with_name('source_reification_results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__': main()
