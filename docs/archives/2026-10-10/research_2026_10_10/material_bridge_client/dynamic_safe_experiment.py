"""Exact host-relative material-transparent beta/eta steps: nonconfluence.

Separate experiment; does not change the proved type-guard normalizer.
"""
from collections import deque
from pathlib import Path
import json
import check_bridge as k


def root_reduce(t):
    if t.kind == 'app' and t.children[0].kind == 'lam':
        fn, arg = t.children
        return k.substitute(fn.children[0], fn.meta[0], arg)
    if t.kind == 'lam' and t.children[0].kind == 'app':
        fn, arg = t.children[0].children
        if arg.kind == 'var' and arg.uid == t.meta[0] and arg.uid not in dict(k.check(fn)):
            return fn
    return None


def at_path(t, path):
    if not path: return root_reduce(t)
    child = at_path(t.children[path[0]], path[1:])
    assert child is not None
    children = list(t.children)
    children[path[0]] = child
    return k.T(t.kind, t.uid, t.typ, tuple(children), t.meta)


def redex_paths(t, prefix=()):
    if root_reduce(t) is not None: yield prefix
    for i, c in enumerate(t.children): yield from redex_paths(c, prefix + (i,))


def indexed_profile(t):
    out = {}
    for forest, residual, roots in k.coaction(t):
        batch = tuple(sorted(roots))
        assert batch not in out
        out[batch] = (tuple(sorted((k.key(p) for p in forest), key=repr)), residual)
    return out


def safe_step(t, path):
    u = at_path(t, path)
    assert k.check(t) == k.check(u) and t.typ == u.typ
    left, right = indexed_profile(t), indexed_profile(u)
    if set(left) != set(right): return False, u
    for batch, (coeff, residual) in left.items():
        coeff_after, residual_after = right[batch]
        if coeff != coeff_after: return False, u
        # This uses the actual corresponding redex inside each typed residual,
        # not cut counts or an unrelated normal-form equivalence.
        if k.key(at_path(residual, path)) != k.key(residual_after): return False, u
    return True, u


def initial(n):
    args = []
    for i in range(n):
        atom = f'p{i}'
        x = k.var(f'x{i}', atom)
        d = k.prim(f'd{i}', f'delta{i}', (), atom)
        args.append(k.app(f'identity_app{i}', k.lam(f'identity_lam{i}', x, x), d))
    return k.prim('outer_material', 'r', tuple(a.typ for a in args), 'q', *args)


def explore(n):
    source = initial(n)
    pending, seen, normals, edges = [source], set(), [], 0
    rejected = 0
    while pending:
        t = pending.pop()
        if t in seen: continue
        seen.add(t)
        assert len(k.coaction(t)) == 2**n
        steps = []
        for path in redex_paths(t):
            safe, u = safe_step(t, path)
            if safe: steps.append(u)
            else: rejected += 1
        edges += len(steps)
        if not steps: normals.append(t)
        pending.extend(steps)
    assert len(seen) == 2**n - 1 and len(normals) == n
    assert len({k.key(t) for t in normals}) == n
    for t in normals:
        assert sum(c.kind == 'app' for c in t.children) == 1
        paths = list(redex_paths(t))
        assert len(paths) == 1
        safe, full = safe_step(t, paths[0])
        assert not safe
        assert len(k.coaction(full)) == len(k.coaction(t)) + 1
        assert ('outer_material',) in {roots for _, _, roots in k.coaction(full)}
    return {'arity': n, 'safe_states': len(seen), 'safe_edges': edges,
            'distinct_terminal_normal_forms': len(normals),
            'material_terms_every_safe_state': 2**n,
            'material_terms_after_forbidden_last_step': 2**n + 1,
            'terminal_remaining_guard_slots': sorted(next(i for i,c in enumerate(t.children)
                                                        if c.kind == 'app') for t in normals),
            'rejected_last_steps': rejected}


def fixed_binary_initial(blocks):
    p = 'p'
    gtype = p
    for _ in range(blocks): gtype = k.arr(p, gtype)
    g = k.var('consumer_g', gtype)
    result = g
    for j in range(blocks):
        args = []
        for i in range(2):
            x = k.var(f'b{j}_x{i}', p)
            d = k.prim(f'b{j}_d{i}', 'delta', (), p)
            args.append(k.app(f'b{j}_app{i}', k.lam(f'b{j}_lam{i}', x, x), d))
        block = k.prim(f'b{j}_r', 'r', (p, p), p, *args)
        result = k.app(f'consumer_app{j}', result, block)
    return k.lam('consumer_lam', g, result)


def explore_fixed_binary(blocks):
    source = fixed_binary_initial(blocks)
    pending, seen, normals, edges = [source], set(), [], 0
    while pending:
        t = pending.pop()
        if t in seen: continue
        seen.add(t)
        assert len(k.coaction(t)) == 4**blocks
        steps = []
        for path in redex_paths(t):
            safe, u = safe_step(t, path)
            if safe: steps.append(u)
        edges += len(steps)
        if not steps: normals.append(t)
        pending.extend(steps)
    assert len(seen) == 3**blocks
    assert len(normals) == len({k.key(t) for t in normals}) == 2**blocks
    for t in normals:
        for path in redex_paths(t):
            safe, u = safe_step(t, path)
            assert not safe
            assert len(k.coaction(u)) - len(k.coaction(t)) == 4**(blocks-1)
    assert edges == 2*blocks*3**(blocks-1)
    return {'binary_blocks': blocks, 'safe_states': len(seen), 'safe_edges': edges,
            'distinct_terminal_normal_forms': len(normals),
            'material_terms_every_safe_state': 4**blocks,
            'new_terms_after_one_forbidden_last_step': 4**(blocks-1)}


def main():
    rows = [explore(n) for n in range(2, 6)]
    result = {'status': 'COUNTEREXAMPLE_CONFIRMED',
              'claim_refuted': 'host-relative exact material-transparent beta/eta has unique normal forms',
              'step_test': 'same actual cut root batches, identical marked material factors, and exact corresponding residual beta/eta step',
              'families': rows,
              'fixed_binary_signature_families': [explore_fixed_binary(n) for n in range(1, 4)],
              'baseline_compound_guard_normalizer': 'unchanged; counterexample has only atomic-domain beta redexes'}
    Path(__file__).with_name('dynamic_safe_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
