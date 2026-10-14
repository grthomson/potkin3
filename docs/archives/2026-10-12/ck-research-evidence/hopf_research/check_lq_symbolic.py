"""Symbolic partition-diagram DP versus raw certificate enumeration."""
from collections import Counter
from itertools import product
from random import Random
import json
from check_lq_certificates import Node, fixture, occurrences, abstract_tree, raw_count, wem_fixture, inventory_fixture


def discrete(ports):
    return tuple(((p,), '') for p in sorted(ports))


def normalize(blocks):
    return tuple(sorted((tuple(sorted(block)), force) for block, force in blocks if block))


def join(s, t):
    ports = {p for block, force in s for p in block}
    assert ports == {p for block, force in t for p in block}
    par = {p: p for p in ports}
    def find(x):
        while par[x] != x:
            x = par[x]
        return x
    for block, force in s + t:
        for p in block[1:]:
            par[find(p)] = find(block[0])
    groups = {}
    for p in ports:
        groups.setdefault(find(p), set()).add(p)
    labels = {}
    for block, force in s + t:
        if force:
            root = find(block[0])
            if root in labels and labels[root] != force:
                return None
            labels[root] = force
    return normalize((ps, labels.get(root, '')) for root, ps in groups.items())


def forced(ports, owner, atom):
    return normalize(({p}, atom if p == owner else '') for p in ports)


def linked(ports, i, j):
    return normalize([({i, j}, '')] + [({p}, '') for p in ports if p not in (i, j)])


def forget(s, owner):
    exponent = 0
    blocks = []
    for block, colour in s:
        if owner not in block:
            blocks.append((block, colour))
        elif len(block) == 1:
            exponent += int(not colour)
        else:
            blocks.append((tuple(p for p in block if p != owner), colour))
    return normalize(blocks), exponent


def poly_add_into(target, source, shift=0):
    for k, v in source.items():
        target[k + shift] += v


def poly_mul(p, q):
    out = Counter()
    for i, a in p.items():
        for j, b in q.items():
            out[i + j] += a * b
    return out


def table_mul(x, y):
    out = {}
    for s, ps in x.items():
        for t, pt in y.items():
            u = join(s, t)
            if u is not None:
                poly_add_into(out.setdefault(u, Counter()), poly_mul(ps, pt))
    return out


def symbolic(t, env=(), address=()):
    # Environments: physical owner address, role, already seen empty succedent.
    env = tuple((i, role, seen or t.succ is None) for i, role, seen in env)
    ports = [i for i, role, seen in env]
    if t.rule == 'owner':
        children = [symbolic(c, env + ((address, role, False),), address + (role,))
                    for role, c in enumerate(t.children)]
        combined = table_mul(*children)
        out = {}
        for s, polynomial in combined.items():
            newstate, shift = forget(s, address)
            poly_add_into(out.setdefault(newstate, Counter()), polynomial, shift)
        return out
    choices = []
    if t.rule == 'GL':
        choices = [forced(ports, i, t.ant[0]) for i, role, seen in env if role == 0]
    elif t.rule == 'GR':
        choices = [forced(ports, i, t.succ) for i, role, seen in env if role == 1 and seen]
    elif t.rule == 'GE':
        choices = [linked(ports, i, j) for i, ri, _ in env for j, rj, seen in env
                   if ri == 0 and rj == 1 and seen]
    else:
        out = {discrete(ports): Counter({0: 1})}
        for k, c in enumerate(t.children):
            out = table_mul(out, symbolic(c, env, address + (k,)))
        return out
    out = {}
    for state in choices:
        out.setdefault(state, Counter())[0] += 1
    return out


def closed_polynomial(t):
    table = symbolic(t)
    assert set(table).issubset({()})
    return dict(sorted(table.get((), {}).items()))


def main():
    result = {'fixture_polynomials': {}, 'random_symbolic_checks': 0}
    for a, b in product(['p', 'q'], repeat=2):
        t = fixture(a, b)
        poly = closed_polynomial(t)
        _, raw = raw_count(t, ['p', 'q'])
        assert poly == raw
        result['fixture_polynomials'][a + b] = poly
    rng = Random(121020261)
    maxowners = 0
    for _ in range(1500):
        t = abstract_tree(rng, 5)
        owners = sum(n.rule == 'owner' for _, n in occurrences(t))
        if owners > 7:
            continue
        maxowners = max(maxowners, owners)
        _, raw = raw_count(t, ['p', 'q'])
        poly = closed_polynomial(t)
        assert poly == raw, (t, poly, raw)
        result['random_symbolic_checks'] += 1
    # Two closed free owner components distinguish Boolean summary from count.
    n = Node('normal', (), (), None)
    free = Node('owner', (n, n), (), None)
    assert closed_polynomial(free) == {1: 1}
    twofree = Node('normal', (free, free), (), None)
    assert closed_polynomial(twofree) == {2: 1}
    result['closed_free_components'] = [closed_polynomial(free), closed_polynomial(twofree)]
    result['max_owners_checked'] = maxowners
    result['weak_excluded_middle'] = closed_polynomial(wem_fixture())
    assert result['weak_excluded_middle'] == {0: 3, 1: 1}
    assert closed_polynomial(inventory_fixture(True)) == {0: 1}
    assert closed_polynomial(inventory_fixture(False)) == {}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
