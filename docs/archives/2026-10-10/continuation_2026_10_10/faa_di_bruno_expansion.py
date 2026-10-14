"""Independent outer/inner antichain expansion for typed material parameters.

Substitution of a nonprimitive tree for a primitive parameter is NOT a Hopf
morphism. This implements the actual cut partition, including swallowed inputs.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import island_seal
k = island_seal.k


def expand(t, payloads):
    if t.uid in payloads:
        assert not t.children and t.typ == payloads[t.uid].typ
        return payloads[t.uid]
    return k.T(t.kind, t.uid, t.typ,
               tuple(expand(c, payloads) for c in t.children), t.meta)


def outer_cuts(t, parameters):
    if t.uid in parameters:
        return [()]
    cuts = [tuple(v for xs in cs for v in xs)
            for cs in product(*(outer_cuts(c, parameters) for c in t.children))]
    if t.kind == 'prim':
        cuts.append((t.uid,))
    return cuts


def under(t, chosen, swallowed=False):
    swallowed = swallowed or t.uid in chosen
    answer = {t.uid} if swallowed else set()
    for c in t.children:
        answer |= under(c, chosen, swallowed)
    return answer


def canonical(forest, residual):
    return tuple(sorted((k.key(t) for t in forest), key=repr)), k.key(residual)


def reconstructed_profile(template, payloads):
    out = Counter()
    rows = 0
    for outer in outer_cuts(template, payloads):
        covered = under(template, set(outer))
        active = [p for p in payloads if p not in covered]
        choices = [k.coaction(payloads[p]) for p in active]
        for inners in product(*choices):
            inner = dict(zip(active, inners))
            forest = []
            def residual(t):
                if t.uid in outer:
                    whole = expand(t, payloads)
                    forest.append(whole)
                    return k.T('hole', t.uid, t.typ, (), k.check(whole))
                if t.uid in payloads:
                    f, r, _ = inner[t.uid]
                    forest.extend(f)
                    return r
                return k.T(t.kind, t.uid, t.typ,
                           tuple(residual(c) for c in t.children), t.meta)
            r = residual(template)
            assert k.check(r) == ()
            out[canonical(forest, r)] += 1
            rows += 1
    return out, rows


def actual_profile(t):
    return Counter(canonical(f, r) for f, r, _ in k.coaction(t))


def leaf(uid):
    return k.prim(uid, uid, (), 'p')


def node(uid, *children):
    return k.prim(uid, uid, tuple('p' for _ in children), 'p', *children)


def payload(uid, shape):
    if shape == 0:
        return leaf(uid + '_a')
    if shape == 1:
        return node(uid + '_s', leaf(uid + '_a'), leaf(uid + '_b'))
    if shape == 2:
        return node(uid + '_s', node(uid + '_v', leaf(uid + '_a')),
                    leaf(uid + '_b'))
    return k.T('hole', uid + '_inherited', 'p')


def main():
    totals = Counter()
    for shape in range(4):
        for left, right in product(range(4), repeat=2):
            a, b = leaf('parameter_a'), leaf('parameter_b')
            templates = [node('r', a, b),
                         node('r', node('s', a, leaf('c')), b),
                         node('r', a, node('s', b, leaf('c'))),
                         node('r', node('s', a, b), leaf('c'))]
            t = templates[shape]
            ps = {a.uid: payload('A', left), b.uid: payload('B', right)}
            expanded = expand(t, ps)
            k.check(expanded)
            reconstructed, rows = reconstructed_profile(t, ps)
            assert reconstructed == actual_profile(expanded)
            totals['expansions'] += 1
            totals['actual_antichain_terms'] += rows
    # A primitive probe has only empty/whole cuts, but its nonprimitive
    # replacement has a genuine internal two-leaf cut.
    p = payload('proof', 1)
    probe = leaf('probe')
    assert len(k.coaction(probe)) == 2
    internal = [row for row in k.coaction(p)
                if set(row[2]) == {'proof_a', 'proof_b'}]
    assert len(internal) == 1
    assert len(k.coaction(p)) == 5
    result = {'status': 'PASS', 'counts': dict(totals),
              'primitive_probe_terms': 2, 'nonprimitive_payload_terms': 5,
              'internal_two_leaf_cut_retained': True,
              'includes_zero_vertex_payloads': True,
              'scope': 'exact finite cut reconstruction; universal proof in notes'}
    Path(__file__).with_name('faa_di_bruno_expansion_results.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
