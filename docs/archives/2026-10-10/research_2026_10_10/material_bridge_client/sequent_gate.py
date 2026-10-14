"""Concrete Cut/material-rule permutation versus alpha-only N_c classes.

The graph is explicitly a generalized atomic-rule incidence graph, not an
asserted member of the pre-existing pure MLL proof-net carrier.
"""
from dataclasses import dataclass
from pathlib import Path
import json
import check_bridge as n


@dataclass(frozen=True)
class Seq:
    rule: str
    uid: str
    output: str
    typ: str
    children: tuple = ()
    hypothesis: str = ''


def context(t):
    if t.rule == 'ax': return ((t.hypothesis, t.typ),)
    if t.rule == 'delta': return ()
    if t.rule == 'r':
        assert tuple(c.typ for c in t.children) == ('p', 'q') and t.typ == 's'
        return n.merge(context(c) for c in t.children)
    if t.rule == 'cut':
        p, q = t.children
        assumptions = dict(context(q))
        assert assumptions.pop(t.hypothesis) == p.typ
        assert t.output == q.output and t.typ == q.typ
        return n.merge((context(p), tuple(sorted(assumptions.items()))))
    raise AssertionError(t.rule)


def fixed_incidence(t):
    """Retains Ax, old primitive and Cut link identities and exact endpoints."""
    links = []
    for c in t.children: links.extend(fixed_incidence(c))
    if t.rule == 'ax':
        links.append(('ax', t.uid, t.hypothesis, t.output, t.typ))
    elif t.rule == 'delta':
        links.append(('delta', t.uid, t.output, t.typ))
    elif t.rule == 'r':
        links.append(('r', t.uid, tuple(c.output for c in t.children), t.output, t.typ))
    else:
        links.append(('cut', t.uid, t.children[0].output, t.hypothesis, t.children[0].typ))
    return tuple(sorted(links, key=repr))


def elaborate(t):
    if t.rule == 'ax': return n.var(t.hypothesis, t.typ)
    if t.rule == 'delta': return n.prim(t.uid, 'delta_'+t.typ, (), t.typ)
    if t.rule == 'r': return n.prim(t.uid, 'r', ('p', 'q'), 's', *(elaborate(c) for c in t.children))
    p, q = t.children
    var = n.var(t.hypothesis, p.typ)
    return n.app(t.uid+'_app', n.lam(t.uid+'_lam', var, elaborate(q)), elaborate(p))


def passenger(t):
    """The exact one-layer instance used here, not an arbitrary normalizer."""
    assert t.kind == 'app' and t.children[0].kind == 'lam'
    abstraction, payload = t.children
    body = abstraction.children[0]
    x, typ = abstraction.meta
    assert body.kind == 'prim' and body.children[0].kind == 'var'
    assert body.children[0].uid == x
    identity = n.T('lam', abstraction.uid, n.arr(typ, typ), (body.children[0],), abstraction.meta)
    cut_argument = n.T('app', t.uid, typ, (identity, payload))
    return n.T('prim', body.uid, body.typ, (cut_argument, body.children[1]), body.meta)


def main():
    dp = Seq('delta', 'dp', 'dp_out', 'p')
    dq = Seq('delta', 'dq', 'dq_out', 'q')
    ax = Seq('ax', 'ax_x', 'ax_out', 'p', hypothesis='x')
    r = Seq('r', 'r', 'r_out', 's', (ax, dq))
    first = Seq('cut', 'C', 'r_out', 's', (dp, r), 'x')
    ax_cut = Seq('cut', 'C', 'ax_out', 'p', (dp, ax), 'x')
    second = Seq('r', 'r', 'r_out', 's', (ax_cut, dq))
    assert context(first) == context(second) == ()
    assert first.output == second.output and first.typ == second.typ
    assert fixed_incidence(first) == fixed_incidence(second)
    a, b = elaborate(first), elaborate(second)
    assert n.check(a) == n.check(b) == () and a.typ == b.typ == 's'
    assert not n.one_steps(a) and not n.one_steps(b)
    assert n.key(a) != n.key(b)
    assert n.key(passenger(a)) == n.key(b)
    right = {tuple(sorted(roots)): (forest, residual) for forest,residual,roots in n.coaction(b)}
    checks = 0
    for forest, residual, roots in n.coaction(a):
        tf, tr = right[tuple(sorted(roots))]
        assert tuple(sorted((n.key(x) for x in forest),key=repr)) == tuple(sorted((n.key(x) for x in tf),key=repr))
        assert n.key(passenger(residual)) == n.key(tr)
        checks += 1
    assert checks == 4
    # A genuine mixed permutation/eta peak: the material-balanced passenger
    # equation preserves size, but N_c images have different sizes.
    x, y = n.var('peak_x', 'p'), n.var('peak_y', 'p')
    side = n.prim('peak_b', 'delta_q', (), 'q')
    body = n.prim('peak_r', 'r', ('p', 'q'), 's', x, side)
    inner = n.app('peak_app', n.lam('peak_lam', x, body), y)
    peak_s = n.lam('peak_outer', y, inner)
    peak_t = n.lam('peak_outer', y, passenger(inner))
    assert n.check(peak_s) == n.check(peak_t) == ()
    ns, nt = n.normal(peak_s), n.normal(peak_t)
    def size(t): return 1 + sum(size(c) for c in t.children)
    assert size(peak_s) == size(peak_t) == 7
    assert size(ns) == 4 and size(nt) == 7
    assert not n.one_steps(ns) and not n.one_steps(nt)
    assert n.key(ns) != n.key(nt)
    # Every contextual κ step and its reverse preserves this size, as does
    # alpha. The distinct counts certify non-equivalence in that quotient.
    result = {'status': 'CONCRETE_COMPARISON_NON_DESCENT_CONFIRMED',
              'source_rule': 'nonprincipal Cut through binary atomic material r',
              'source_complete_judgment': 'empty |- s',
              'same_fixed_generalized_incidence': True,
              'same_normalized_alpha_only_ND_class': False,
              'both_Nc_normal': True,
              'material_cut_terms_matched_modulo_explicit_passenger_cell': checks,
              'mixed_eta_passenger_peak': {'source_sizes': [size(peak_s),size(peak_t)],
                  'Nc_image_sizes': [size(ns),size(nt)],
                  'Nc_does_not_descend_to_passenger_quotient': True,
                  'separating_invariant': 'all contextual passenger/alpha equations preserve positive node count'},
              'scope': 'generalized primitive-rule incidence; not identification with pure MLL fixed-net carrier; not impossibility of other comparison maps'}
    Path(__file__).with_name('sequent_gate_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__': main()
