"""Finite native-tree check, not GGP semantics or a proof assistant.

Occurrence-linear implication syntax, positive-arity atomic primitives,
complete-judgment vacancies, and actual admissible rooted-tree antichains.
"""
from dataclasses import dataclass
from collections import Counter
from itertools import product
import json
from pathlib import Path


def arr(a, b): return (a, b)
def atomic(a): return isinstance(a, str)


@dataclass(frozen=True)
class T:
    kind: str
    uid: str
    typ: object
    children: tuple = ()
    meta: tuple = ()


def var(uid, typ): return T('var', uid, typ)
def prim(uid, name, inputs, output, *args):
    return T('prim', uid, output, tuple(args), (name, tuple(inputs)))
def lam(uid, x, body): return T('lam', uid, arr(x.typ, body.typ), (body,), (x.uid, x.typ))
def app(uid, fn, arg): return T('app', uid, fn.typ[1], (fn, arg))


def merge(contexts):
    result = {}
    for c in contexts:
        for x, typ in c:
            assert x not in result, ('nonlinear occurrence', x)
            result[x] = typ
    return tuple(sorted(result.items()))


def check(t, _seen=None):
    if _seen is None: _seen = set()
    assert t.uid not in _seen, ('duplicate proof occurrence', t.uid)
    _seen.add(t.uid)
    if t.kind == 'var': return ((t.uid, t.typ),)
    if t.kind == 'hole':
        assert atomic(t.typ) and all(atomic(a) for _, a in t.meta), 'non-atomic vacancy interface'
        return t.meta
    contexts = [check(c, _seen) for c in t.children]
    if t.kind == 'prim':
        assert len(t.meta) in (2, 3)
        name, inputs = t.meta[:2]
        assert atomic(t.typ) and all(map(atomic, inputs)), name
        assert tuple(c.typ for c in t.children) == inputs
        if len(t.meta) == 3:
            discharged = t.meta[2]
            assert len(discharged) == len(contexts)
            remaining = []
            for context, binders in zip(contexts, discharged):
                available = dict(context)
                for x, a in binders:
                    assert atomic(a), 'compound material discharge'
                    assert available.pop(x) == a
                remaining.append(tuple(sorted(available.items())))
            contexts = remaining
        return merge(contexts)
    if t.kind == 'app':
        f, a = t.children
        assert not atomic(f.typ) and f.typ == arr(a.typ, t.typ)
        return merge(contexts)
    if t.kind == 'lam':
        x, a = t.meta
        context = dict(contexts[0])
        assert context.pop(x) == a
        assert t.typ == arr(a, t.children[0].typ)
        return tuple(sorted(context.items()))
    raise AssertionError(t.kind)


def substitute(t, x, p):
    if t.kind == 'var' and t.uid == x:
        assert t.typ == p.typ
        return p
    if t.kind == 'hole':
        assert x not in dict(t.meta), 'cannot conceal substitution in a vacancy'
        return t
    if t.kind == 'prim' and len(t.meta) == 3:
        assert all(x != y for bs in t.meta[2] for y, _ in bs), 'cannot substitute a discharged atom'
    assert not (t.kind == 'lam' and t.meta[0] == x), 'globally fresh binders required'
    return T(t.kind, t.uid, t.typ, tuple(substitute(c, x, p) for c in t.children), t.meta)


def one_steps(t, atomic_beta=False):
    result = []
    if t.kind == 'app' and t.children[0].kind == 'lam':
        f, p = t.children
        x, a = f.meta
        if atomic_beta or not atomic(a):
            result.append(substitute(f.children[0], x, p))
    if t.kind == 'lam':
        x, a = t.meta
        body = t.children[0]
        if body.kind == 'app':
            f, p = body.children
            if p.kind == 'var' and p.uid == x and x not in dict(check(f)):
                result.append(f)
    for i, c in enumerate(t.children):
        for reduced in one_steps(c, atomic_beta):
            children = list(t.children)
            children[i] = reduced
            result.append(T(t.kind, t.uid, t.typ, tuple(children), t.meta))
    for r in result:
        assert check(r) == check(t) and r.typ == t.typ
    return result


def normal(t):
    while (steps := one_steps(t)):
        t = steps[0]
    return t


def key(t, bound=None):
    # Logical rule occurrence names are presentation metadata; material and
    # variable/hole occurrence names preserve exact physical seams.
    bound = {} if bound is None else bound
    uid = t.uid if t.kind in ('prim', 'var', 'hole') else ''
    meta = t.meta
    child_bound = bound
    if t.kind == 'lam':
        child_bound = dict(bound)
        child_bound[t.meta[0]] = ('bound', len(bound))
        meta = ('binder', t.meta[1])
    elif t.kind == 'var':
        uid = bound.get(t.uid, ('free', t.uid))
    elif t.kind == 'hole':
        meta = tuple(sorted(((bound.get(x, ('free', x)), a) for x, a in t.meta), key=repr))
    return (t.kind, uid, t.typ, meta, tuple(key(c, child_bound) for c in t.children))


def pure(t):
    return t.kind == 'hole' or (t.kind == 'prim' and all(pure(c) for c in t.children))


def antichains(t):
    # Child products give mutually incomparable selected roots; selecting this
    # root excludes every descendant. A vacancy is never a positive cut root.
    result = [tuple(x for part in choices for x in part)
              for choices in product(*(antichains(c) for c in t.children))]
    if t.kind == 'prim' and pure(t): result.append((t.uid,))
    return result


def cut(t, selected):
    if t.uid in selected:
        interface = check(t)
        assert atomic(t.typ) and all(atomic(a) for _, a in interface)
        return T('hole', t.uid, t.typ, (), interface), (t,)
    children, forest = [], ()
    for c in t.children:
        r, p = cut(c, selected)
        children.append(r)
        forest += p
    return T(t.kind, t.uid, t.typ, tuple(children), t.meta), forest


def coaction(t):
    check(t)
    terms = []
    for roots in antichains(t):
        residual, forest = cut(t, set(roots))
        assert check(residual) == check(t)
        terms.append((forest, residual, roots))
    return terms


def profile(t, normalize_residuals=True):
    # Native tuples remain ordered in coaction(). The theorem comparison uses
    # the project's explicitly commutative forest observer: substitution need
    # not preserve traversal order of independent material factors.
    return Counter((tuple(sorted((key(p) for p in forest), key=repr)),
                    key(normal(residual) if normalize_residuals else residual))
                   for forest, residual, roots in coaction(t))


def all_normal_forms(t):
    pending, seen, outputs = [t], set(), set()
    while pending:
        u = pending.pop()
        if u in seen: continue
        seen.add(u)
        steps = one_steps(u)
        if not steps: outputs.add(key(u))
        pending.extend(steps)
    return outputs, len(seen)


def check_case(name, t):
    check(t)
    n = normal(t)
    assert all(not one_steps(r) for _, r, _ in coaction(n)), (name, 'normality not hereditary')
    assert profile(t) == profile(n, normalize_residuals=False), name
    states = [t]
    seen = set()
    cut_count = 0
    while states:
        u = states.pop()
        if u in seen: continue
        seen.add(u)
        nu = normal(u)
        assert all(not one_steps(r) for _, r, _ in coaction(nu)), (name, 'residual normality')
        assert profile(u) == profile(nu, normalize_residuals=False), (name, 'residual')
        for forest, residual, roots in coaction(u):
            cut_count += 1
            if roots: states.append(residual)
    forms, reduction_states = all_normal_forms(t)
    assert len(forms) == 1
    return dict(name=name, material_terms=len(coaction(t)), residual_states=len(seen),
                residual_cut_terms=cut_count, rewrite_states=reduction_states)


def main():
    p, q = 'p', 'q'
    d1 = prim('delta_p_1', 'delta_p', (), p)
    d2 = prim('delta_p_2', 'delta_p', (), p)
    x = var('x', p)
    provider = lam('lambda_x', x, prim('r', 'r', (p, p), q, x, d2))
    f = var('f', arr(p, q))
    source = app('outer', lam('lambda_f', f, app('body', f, d1)), provider)
    eta_x = var('eta_x', p)
    eta = lam('eta_wrapper', eta_x, app('eta_apply', provider, eta_x))

    rows = [check_case('compound_beta_binary_material', source),
            check_case('eta_binary_material', eta)]
    source_eta = app('outer_eta', source.children[0], eta)
    rows.append(check_case('nested_beta_eta_overlap', source_eta))
    a = arr(p, q)
    g = var('g', arr(a, a))
    h = var('h', a)
    eta_function = lam('eta_function', h, app('g_h', g, h))
    rows.append(check_case('beta_function_eta_critical_pair',
                          app('critical_apply', eta_function, provider)))
    j = var('j', a)
    rows.append(check_case('eta_body_beta_critical_pair',
                          lam('critical_lambda', j, app('critical_body', eta_function, j))))
    alpha_type = arr(p, p)
    alpha_x = var('alpha_x', alpha_type)
    alpha_y = var('alpha_y', alpha_type)
    alpha_inner = lam('alpha_inner', alpha_y, app('alpha_y_apply', alpha_y, d1))
    rows.append(check_case('eta_beta_persistent_alpha_overlap',
                          lam('alpha_outer', alpha_x, app('alpha_apply', alpha_inner, alpha_x))))

    # Repeated atom p has distinct complete holes and detached occurrences.
    both = next((forest, residual) for forest, residual, roots in coaction(source)
                if set(roots) == {'delta_p_1', 'delta_p_2'})
    assert [z.uid for z in both[0]] == ['delta_p_1', 'delta_p_2']

    blocked = normal(source)
    assert blocked.kind == 'app' and blocked.children[0].kind == 'lam'
    assert atomic(blocked.children[0].meta[1])
    unrestricted = one_steps(blocked, atomic_beta=True)[0]
    assert unrestricted.kind == 'prim' and unrestricted.uid == 'r'
    assert len(coaction(blocked)) == 4 and len(coaction(unrestricted)) == 5
    assert profile(blocked) != profile(unrestricted)
    extra = [roots for _, _, roots in coaction(unrestricted) if roots == ('r',)]
    assert len(extra) == 1

    # Genuine nested pure material tree, repeated type, and opening flags.
    nested = prim('s', 's', (q, p), p, unrestricted,
                  prim('delta_p_3', 'delta_p', (), p))
    z = var('z', p)
    nested_provider = lam('nested_lambda', z,
        prim('outer_r', 'outer_r', (p, p), q, nested, z))
    ez = var('ez', p)
    rows.append(check_case('eta_nested_material_flags',
        lam('nested_eta', ez, app('nested_eta_app', nested_provider, ez))))

    # Eta freshness must see complete antecedents of holes.
    hx = T('hole', 'typed_hole', p, (), (('hidden_x', p),))
    hidden_x = var('hidden_x', p)
    hz = var('hidden_z', p)
    hidden_function = lam('hidden_function', hz,
                         prim('hidden_r', 'r', (p, p), q, hx, hz))
    bad = lam('bad', hidden_x, app('bad_app', hidden_function, hidden_x))
    try:
        check(bad)
        raise AssertionError('duplicate resource unexpectedly accepted')
    except AssertionError as error:
        assert error.args[0] == ('nonlinear occurrence', 'hidden_x')
    forbidden = T('hole', 'forbidden', p, (), (('compound_input', arr(p, q)),))
    try:
        check(forbidden)
        raise AssertionError('arbitrary compound-context hole accepted')
    except AssertionError as error:
        assert error.args[0] == 'non-atomic vacancy interface'
    duplicate = prim('duplicate_root', 'r', (p, p), q, d1, d1)
    try:
        check(duplicate)
        raise AssertionError('duplicate positive occurrence accepted')
    except AssertionError as error:
        assert error.args[0] == ('duplicate proof occurrence', 'delta_p_1')

    report = {'status': 'PASS', 'scope': 'finite native syntax/material-cut evidence',
              'observer': 'commutative material forest; native ordered tuples retained',
              'vacancy_domain': 'atomic complete interfaces; cuts originate in checked native trees',
              'cases': rows, 'blocked_atomic_beta': {'old_terms': 4, 'new_terms': 5,
                 'new_root': 'r', 'two_equal_atomic_boundaries_distinct': True},
              'not_claimed': ['full base-extension semantics implementation',
                 'proof-assistant mechanization', 'full beta normalization descent']}
    destination = Path(__file__).with_name('results.json')
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__': main()
