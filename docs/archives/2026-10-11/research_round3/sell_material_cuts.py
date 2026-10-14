"""Actual SELL repair macros versus typed positive material cuts.

Reuses round2's independently checked logical rules. Adds typed holes and
literal address antichain extraction, not an asserted native Hopf formalization.
The material profile includes tensor introduction, so coefficients are not
restricted to primitive leaves.
"""
from pathlib import Path
import sys
from dataclasses import replace
from itertools import product
from collections import Counter
import json

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'research_round2'))
from check_sell import (Proof, Checker, at, bang, tensor, ctx, ident, wrap,
                        pair, weaken, contract, derive_wb, derive_cb, nodes)

MATERIAL = frozenset({'g', 'tR'})

def hole(p):
    return Proof('hole', p.g, p.c)

def pure(p):
    return p.rule == 'hole' or (p.rule in MATERIAL and all(pure(k) for k in p.kids))

def positive(p):
    return p.rule != 'hole'

def compile_repair(p):
    q = replace(p, kids=tuple(compile_repair(k) for k in p.kids))
    if p.rule in {'W', 'C'} and p.g[p.pos][1] == 'b':
        a = p.g[p.pos][2]
        return derive_wb(q.kids[0], a) if p.rule == 'W' else derive_cb(q.kids[0], a)
    return q

def all_material_cuts(p, root=True):
    """Return (ordered factors, exact residual, addresses), no cuts at holes."""
    if p.rule == 'hole':
        return [((), p, ())]
    out = []
    for choices in product(*(all_material_cuts(k) for k in p.kids)):
        factors = tuple(v for fs, _, _ in choices for v in fs)
        remainder = replace(p, kids=tuple(r for _, r, _ in choices))
        addresses = tuple((i,) + a for i, (_, _, aa) in enumerate(choices) for a in aa)
        out.append((factors, remainder, addresses))
    if root and pure(p):
        out.append(((p,), hole(p), ((),)))
    return out

def material_record(p, root=True):
    return Counter((f, r) for f, r, _ in all_material_cuts(p, root))

def refill(r, factors):
    it = iter(factors)
    def visit(t):
        if t.rule == 'hole':
            p = next(it)
            assert (p.g, p.c) == (t.g, t.c)
            return p
        return replace(t, kids=tuple(visit(k) for k in t.kids))
    result = visit(r)
    try:
        next(it)
    except StopIteration:
        return result
    raise AssertionError('unused provider')

def open_local_check(p, checker):
    """Check rigid rules with holes treated as exact judgment axioms.

    Override recursive entry, keeping all existing local rule checks.
    """
    original = checker.check
    def check(q):
        if q.rule == 'hole':
            assert q.g == ctx(q.g) and not q.kids
            return True
        return original(q)
    checker.check = check
    try:
        return check(p)
    finally:
        checker.check = original

def full_cut_count(p):
    if p.rule == 'hole':
        return 1
    n = 1
    for k in p.kids:
        n *= full_cut_count(k)
    return n + 1

def cases():
    g = Proof('g', (at('p'),), at('p'))
    # Nonprimitive wholly selected binary and nested binary material regions.
    providers = [g, pair(g, g), pair(pair(g, g), g), pair(g, pair(g, g))]
    for i, p in enumerate(providers):
        yield f'Wb_material_shape_{i}', weaken(p, 'b', at('q'))
        yield f'nested_Wb_material_shape_{i}', weaken(weaken(p, 'b', at('q')), 'b', at('r'))
        # Two !b q hypotheses are generated legally by Wa-derived rules,
        # while the positive p material forest remains an actual proof region.
        prem = weaken(weaken(p, 'a', at('q')), 'a', at('q'))
        # Ordinary Ca is retained, while the inner Wb repair is expanded.
        yield f'Ca_over_Wb_shape_{i}', contract(weaken(prem, 'b', at('r')), 'a', at('q'))
        # Cb with two b-derelicted identity branches and independent material.
        bq = bang('b', at('q'))
        d = wrap(ident(at('q')), at('q'), 'b')
        premise = pair(p, pair(d, d))
        yield f'Cb_material_shape_{i}', contract(premise, 'b', at('q'))

def main():
    order = {('a','a'), ('a','b'), ('b','b')}
    raw = Checker(order, {'a'}, {'a'})
    repaired = Checker(order, {'a','b'}, {'a','b'})
    rows = []
    residual_checks = 0
    for name, source in cases():
        assert repaired.check(source)
        target = compile_repair(source)
        assert raw.check(target)
        assert (source.g, source.c) == (target.g, target.c)
        src = all_material_cuts(source)
        tgt = all_material_cuts(target)
        expected = Counter((f, compile_repair(r)) for f, r, _ in src)
        actual = Counter((f, r) for f, r, _ in tgt)
        assert expected == actual, name
        # Exact local typing and literal source/target reconstruction.
        for proof, cuts, checker in ((source, src, repaired), (target, tgt, raw)):
            for fs, r, _ in cuts:
                assert open_local_check(r, checker)
                assert refill(r, fs) == proof
                residual_checks += 1
        assert any(any(f.rule == 'tR' for f in fs) for fs, _, _ in src) == ('shape_0' not in name)
        rows.append({'case':name, 'source_nodes':nodes(source), 'target_nodes':nodes(target),
                     'material_cut_witnesses':len(src), 'full_source_pointed_cuts':full_cut_count(source),
                     'full_target_pointed_cuts':full_cut_count(target)})
    assert all(r['full_target_pointed_cuts'] > r['full_source_pointed_cuts'] for r in rows)
    result = {'logical_cases':len(rows), 'typed_residual_and_refill_checks':residual_checks,
              'material_profile':sorted(MATERIAL), 'coefficient_sensitive_material_record_equality':True,
              'full_cut_equality_rejected_in_every_case':True, 'cases':rows,
              'scope':'Python checked literal typed cut bijections; not Lean or a general linear coaction theorem'}
    Path(__file__).with_name('sell_material_results.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
