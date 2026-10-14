"""Finite checks of paper theorems; deliberately independent raw and DP counts.

Native-like fixture rules are checked for actual sequents. Random abstract trees
only test certificate combinatorics and are not claimed to be derivations.
"""
from dataclasses import dataclass
from itertools import product
from collections import Counter
from random import Random
import json


@dataclass(frozen=True)
class Node:
    rule: str
    children: tuple = ()
    ant: tuple = ()
    succ: str | None = None


def bag(xs):
    return tuple(sorted(xs))


def weaken(t, a):
    return Node('W', (t,), bag(t.ant + (a,)), t.succ)


def negleft(t):
    assert t.succ is not None
    return Node('notL', (t,), bag(t.ant + ('~' + t.succ,)), None)


def negright(t, a):
    assert t.succ is None and a in t.ant
    ant = list(t.ant); ant.remove(a)
    return Node('notR:' + a, (t,), bag(ant), '~' + a)


def orright(t, a, b):
    assert t.succ in (a, b)
    return Node('orR:' + a + ':' + b, (t,), t.ant, '(' + a + '|' + b + ')')


def orleft(t, u, a, b):
    ca, cb = Counter(t.ant), Counter(u.ant)
    ca.subtract([a]); cb.subtract([b])
    assert ca == cb and all(x >= 0 for x in ca.values()) and t.succ == u.succ
    ctx = list(ca.elements())
    return Node('orL:' + a + ':' + b, (t, u), bag(ctx + ['(' + a + '|' + b + ')']), t.succ)


def module(a):
    t = negleft(Node('GR', (), (), a))
    for f in ['p', '~p', 'q', '~q']:
        if f != '~' + a:
            t = weaken(t, f)
    return t


def ordinary_s():
    return weaken(weaken(negleft(Node('ax', (), ('p',), 'p')), 'q'), '~q')


def fixture(a, b):
    lhs = orleft(ordinary_s(), ordinary_s(), 'p', 'p')
    rhs = orleft(module(a), module(b), 'p', 'p')
    assert (lhs.ant, lhs.succ) == (rhs.ant, rhs.succ)
    return Node('owner', (lhs, rhs), lhs.ant, lhs.succ)


def inventory_fixture(valid):
    t, u = (fixture('p', 'p'), fixture('q', 'q')) if valid else (fixture('p', 'q'), fixture('p', 'q'))
    return orleft(t, u, '(p|p)', '(p|p)')


def wem_fixture():
    left = orright(negright(Node('GL', (), ('p',), None), 'p'), '~p', '~~p')
    right = orright(negright(negleft(Node('GR', (), (), 'p')), '~p'), '~p', '~~p')
    inner = Node('owner', (left, right), (), left.succ)
    return Node('owner', (inner, inner), (), left.succ)


def validate(t):
    for c in t.children:
        validate(c)
    if t.rule == 'ax':
        assert t.ant == (t.succ,)
    elif t.rule == 'GR':
        assert not t.ant and t.succ in ('p', 'q')
    elif t.rule == 'GL':
        assert len(t.ant) == 1 and t.ant[0] in ('p', 'q') and t.succ is None
    elif t.rule == 'W':
        c, = t.children
        diff = Counter(t.ant) - Counter(c.ant)
        assert sum(diff.values()) == 1 and Counter(t.ant) == Counter(c.ant) + diff
        assert t.succ == c.succ
    elif t.rule == 'notL':
        c, = t.children
        assert c.succ is not None and t.succ is None
        assert t.ant == bag(c.ant + ('~' + c.succ,))
    elif t.rule.startswith('orL:'):
        _, a, b = t.rule.split(':')
        assert t == orleft(*t.children, a, b)
    elif t.rule.startswith('notR:'):
        assert t == negright(t.children[0], t.rule.removeprefix('notR:'))
    elif t.rule.startswith('orR:'):
        _, a, b = t.rule.split(':')
        assert t == orright(t.children[0], a, b)
    elif t.rule == 'owner':
        assert len(t.children) == 2
        assert all((c.ant, c.succ) == (t.ant, t.succ) for c in t.children)
    else:
        raise ValueError(t.rule)


def occurrences(t, path=()):
    yield path, t
    for i, c in enumerate(t.children):
        yield from occurrences(c, path + (i,))


def raw_count(t, palette):
    """Enumerate raw leaf-owner choices, then independently graph components."""
    nodes = dict(occurrences(t))
    owners = [a for a, n in nodes.items() if n.rule == 'owner']
    leaves = [(a, n) for a, n in nodes.items() if n.rule in ('GL', 'GR', 'GE')]
    choice_sets = []
    for a, n in leaves:
        left, right = [], []
        for o in owners:
            if len(o) < len(a) and a[:len(o)] == o:
                if a[len(o)] == 0:
                    left.append(o)
                else:
                    # Leaf included, owner conclusion excluded.
                    pathnodes = [a[:k] for k in range(len(o) + 1, len(a) + 1)]
                    if any(nodes[z].succ is None for z in pathnodes):
                        right.append(o)
        if n.rule == 'GL':
            choice_sets.append([(i,) for i in left])
        elif n.rule == 'GR':
            choice_sets.append([(j,) for j in right])
        else:
            choice_sets.append(list(product(left, right)))
    total = 0
    polynomial = Counter()
    for choices in product(*choice_sets):
        parent = {o: o for o in owners}
        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        for (_, n), choice in zip(leaves, choices):
            if n.rule == 'GE':
                parent[find(choice[0])] = find(choice[1])
        forced = {}
        valid = True
        for (_, n), choice in zip(leaves, choices):
            if n.rule != 'GE':
                atom = n.succ if n.rule == 'GR' else n.ant[0]
                root = find(choice[0])
                if root in forced and forced[root] != atom:
                    valid = False
                forced[root] = atom
        if valid and all(a in palette for a in forced.values()):
            k = len({find(o) for o in owners} - set(forced))
            total += len(palette) ** k
            polynomial[k] += 1
    return total, dict(sorted(polynomial.items()))


def dp_count(t, palette, env=()):
    """Scope recursion: no owner-choice enumeration, no connectivity graph."""
    env = tuple((colour, role, seen or t.succ is None) for colour, role, seen in env)
    if t.rule == 'owner':
        return sum(dp_count(t.children[0], palette, env + ((a, 0, False),)) *
                   dp_count(t.children[1], palette, env + ((a, 1, False),))
                   for a in palette)
    if t.rule == 'GL':
        return sum(c == t.ant[0] and role == 0 for c, role, seen in env)
    if t.rule == 'GR':
        return sum(c == t.succ and role == 1 and seen for c, role, seen in env)
    if t.rule == 'GE':
        return sum(c == d for c, r, _ in env for d, s, seen in env if r == 0 and s == 1 and seen)
    ans = 1
    for c in t.children:
        ans *= dp_count(c, palette, env)
    return ans


def abstract_tree(rng, depth):
    if depth == 0 or rng.random() < .35:
        kind = rng.choice(['normal', 'GL', 'GR', 'GE'])
        atom = rng.choice(['p', 'q'])
        return Node(kind, (), (atom,) if kind == 'GL' else (),
                    atom if kind == 'GR' else None)
    kind = rng.choice(['owner', 'normal', 'unary'])
    arity = 1 if kind == 'unary' else 2
    return Node(kind, tuple(abstract_tree(rng, depth - 1) for _ in range(arity)), (),
                'p' if rng.random() < .6 else None)


def main():
    result = {'fixture': [], 'abstract_random_checks': 0}
    for a, b in product(['p', 'q'], repeat=2):
        t = fixture(a, b)
        validate(t)
        raw, poly = raw_count(t, ['p', 'q'])
        dp = dp_count(t, ['p', 'q'])
        assert raw == dp == int(a == b)
        assert len(list(occurrences(t))) == 21
        result['fixture'].append({'modules': a + b, 'nodes': 21, 'count': raw,
                                  'polynomial': poly, 'ordinary_rules_checked': True})
    good, bad = inventory_fixture(True), inventory_fixture(False)
    validate(good); validate(bad)
    def inventory(t):
        return Counter((n.rule, n.ant, n.succ,
                        tuple((c.ant, c.succ) for c in n.children)) for _, n in occurrences(t))
    assert inventory(good) == inventory(bad)
    assert len(list(occurrences(good))) == len(list(occurrences(bad))) == 43
    assert raw_count(good, ['p', 'q'])[0] == dp_count(good, ['p', 'q']) == 1
    assert raw_count(bad, ['p', 'q'])[0] == dp_count(bad, ['p', 'q']) == 0
    result['inventory_separator'] = {'nodes_each': 43, 'exact_local_inventory_equal': True,
                                     'good_count': 1, 'bad_count': 0}
    wem = wem_fixture()
    validate(wem)
    count, poly = raw_count(wem, ['p', 'q'])
    assert poly == {0: 3, 1: 1} and count == dp_count(wem, ['p', 'q']) == 5
    result['weak_excluded_middle'] = {'root': wem.succ, 'polynomial': poly,
                                      'raw_certificates': sum(poly.values()), 'q_2_count': count,
                                      'nodes': len(list(occurrences(wem)))}
    rng = Random(12102026)
    for _ in range(1000):
        t = abstract_tree(rng, 4)
        if sum(n.rule == 'owner' for _, n in occurrences(t)) > 7:
            continue
        for palette in (['p', 'q'], ['p', 'q', 'r']):
            raw, _ = raw_count(t, palette)
            dp = dp_count(t, palette)
            assert raw == dp, (t, raw, dp)
            result['abstract_random_checks'] += 1
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
