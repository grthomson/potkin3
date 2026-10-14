"""Bounded type-directed linear-term generation, independently of fixtures.

State-local caps bound search; no exhaustiveness beyond retained states claimed.
"""
from functools import lru_cache
from itertools import combinations, product
from collections import Counter
from pathlib import Path
import json
import check_bridge as k

P, Q = 'p', 'q'
A, B = k.arr(P, P), k.arr(P, Q)
TYPES = (P, Q, A, B, k.arr(A, P), k.arr(A, A), k.arr(B, Q))
CAP = 45


def parts(context):
    masks = sorted(range(1 << len(context)), key=lambda m: (abs(2 * m.bit_count() - len(context)), m))
    for mask in masks:
        yield (tuple(x for i, x in enumerate(context) if mask & (1 << i)),
               tuple(x for i, x in enumerate(context) if not mask & (1 << i)))


@lru_cache(None)
def generate(typ, context, size):
    out = []
    def add(x):
        if x not in out: out.append(x)
        return len(out) >= CAP
    if size == 1:
        if len(context) == 1 and context[0][1] == typ:
            add(('v', typ, context[0][0], ()))
        if not context and typ in (P, Q): add(('c', typ, 'c_' + typ, ()))
        return tuple(out)
    if not k.atomic(typ):
        a, b = typ
        fresh = max((v for v, _ in context), default=-1) + 1
        for body in generate(b, tuple(sorted(context + ((fresh, a),))), size - 1):
            if add(('l', typ, fresh, (body,))): return tuple(out)
    if size >= 3:
        for a in TYPES:
            fn_type = k.arr(a, typ)
            if fn_type not in TYPES: continue
            for left, right in parts(context):
                for n in sorted(range(1, size - 1), key=lambda n: (abs(2*n-(size-1)), n)):
                    for f, x in product(generate(fn_type, left, n), generate(a, right, size-1-n)):
                        if add(('a', typ, '', (f, x))): return tuple(out)
    if typ in (P, Q):
        # Positive-arity constructors are enumerated with actual linear resource
        # partitions, rather than inserted only as leaves of a beta template.
        if typ == P:
            for child in generate(P, context, size-1):
                if add(('h', P, 'h', (child,))): return tuple(out)
        for left, right in parts(context):
            for n in sorted(range(1, size-1), key=lambda n: (abs(2*n-(size-1)), n)):
                for x, y in product(generate(P, left, n), generate(P, right, size-1-n)):
                    if add(('r', typ, 'r_' + typ, (x, y))): return tuple(out)
    return tuple(out)


def instantiate(ast, prefix, context):
    serial = 0
    def next_id(stem):
        nonlocal serial
        serial += 1
        return f'{prefix}_{stem}_{serial}'
    def walk(a, env):
        kind, typ, payload, children = a
        if kind == 'v': return k.var(env[payload], typ)
        uid = next_id(kind)
        if kind == 'l':
            fresh = next_id('bound')
            new_env = dict(env)
            new_env[payload] = fresh
            return k.lam(uid, k.var(fresh, typ[0]), walk(children[0], new_env))
        cs = tuple(walk(c, env) for c in children)
        if kind == 'a': return k.app(uid, *cs)
        if kind == 'c': return k.prim(uid, payload, (), typ)
        return k.prim(uid, payload, tuple(c.typ for c in cs), typ, *cs)
    return walk(ast, {v: f'{prefix}_free_{v}' for v, _ in context})


def features(t):
    counts = Counter()
    redex_positions = []
    def walk(u, depth, position):
        counts['nodes'] += 1
        counts['depth'] = max(counts['depth'], depth)
        counts['material'] += u.kind == 'prim'
        if u.kind == 'app' and u.children[0].kind == 'lam':
            counts['atomic_beta' if k.atomic(u.children[0].meta[1]) else 'compound_beta'] += 1
            if not k.atomic(u.children[0].meta[1]): redex_positions.append(position)
        if u.kind == 'lam' and u.children[0].kind == 'app':
            f, x = u.children[0].children
            if x.kind == 'var' and x.uid == u.meta[0] and x.uid not in dict(k.check(f)):
                counts['eta'] += 1
                redex_positions.append(position)
        for i, c in enumerate(u.children): walk(c, depth + 1, position + (i,))
    walk(t, 0, ())
    for u, v in combinations(redex_positions, 2):
        counts['nested_pairs' if u == v[:len(u)] or v == u[:len(v)] else 'disjoint_pairs'] += 1
    return counts


def main():
    contexts = ((), ((0, A),), ((0, k.arr(A, A)),), ((0, A), (1, P)),
                ((0, k.arr(A, A)), (1, A)))
    candidates = []
    for context in contexts:
        for typ in TYPES:
            for size in range(1, 11):
                for ast in generate(typ, context, size):
                    prefix = f't{len(candidates)}'
                    t = instantiate(ast, prefix, context)
                    expected_context = tuple(sorted((f'{prefix}_free_{v}', a) for v, a in context))
                    assert k.check(t) == expected_context and t.typ == typ
                    candidates.append((t, features(t), bool(context)))
    # Deterministic strata prevent the first easy type from dominating selection.
    groups = {}
    for entry in candidates:
        t, f, opened = entry
        sig = (opened, f['compound_beta'], f['atomic_beta'], f['eta'],
               min(f['material'], 3), min(f['depth'], 5), bool(f['nested_pairs']), bool(f['disjoint_pairs']))
        groups.setdefault(sig, []).append(entry)
    selected = []
    for sig in sorted(groups):
        selected.extend(groups[sig][:3])
    totals = Counter()
    for number, (t, f, opened) in enumerate(selected):
        row = k.check_case(f'generated_{number}', t)
        totals['checked_terms'] += 1
        totals['free_context_terms'] += opened
        totals['terms_with_compound_beta'] += f['compound_beta'] > 0
        totals['terms_with_eta'] += f['eta'] > 0
        totals['terms_with_multiple_redexes'] += f['compound_beta'] + f['eta'] > 1
        totals['terms_with_nested_redexes'] += f['nested_pairs'] > 0
        totals['terms_with_disjoint_redexes'] += f['disjoint_pairs'] > 0
        totals['terms_with_positive_arity_material'] += any_arity(t)
        totals['residual_states'] += row['residual_states']
        totals['residual_cut_terms'] += row['residual_cut_terms']
        totals['rewrite_states'] += row['rewrite_states']
    negative_checks = []
    d = k.prim('d', 'd', (), P)
    bad = {
        'compound_material_input': k.prim('bad1', 'bad', (A,), P, k.var('f', A)),
        'wrong_material_premise_type': k.prim('bad2', 'bad', (Q,), P, d),
        'compound_material_output': k.prim('bad3', 'bad', (), A),
        'duplicate_closed_occurrence': k.prim('bad4', 'r', (P, P), Q, d, d),
        'compound_input_hidden_in_hole': k.T('hole', 'bad5', P, (), (('x', A),)),
        'compound_hole_output': k.T('hole', 'bad6', A),
    }
    for name, term in bad.items():
        try: k.check(term)
        except (AssertionError, KeyError): negative_checks.append(name)
        else: raise AssertionError(('invalid term accepted', name))
    result = {'status': 'PASS', 'generator': 'type-directed linear resource partition enumeration',
              'maximum_nodes': 10, 'per_state_cap': CAP, 'candidate_terms': len(candidates),
              'feature_strata': len(groups), 'totals': dict(totals),
              'negative_checks': negative_checks,
              'scope': 'bounded retained enumeration; no exhaustive general theorem claim'}
    Path(__file__).with_name('enumerated_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


def any_arity(t):
    return ((t.kind == 'prim' and bool(t.children)) or any(any_arity(c) for c in t.children))


if __name__ == '__main__': main()
