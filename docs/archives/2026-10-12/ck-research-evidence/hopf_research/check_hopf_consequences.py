"""Exact finite algebra checks; not Lean or a native POTKIN3 implementation."""
from collections import defaultdict
from itertools import product
from functools import lru_cache


class Poly:
    # Keys: (commutative variable monomial, E/P/Q boundary constraint).
    def __init__(self, terms=None):
        self.terms = {k: v for k, v in (terms or {}).items() if v}

    def __add__(self, other):
        out = defaultdict(int, self.terms)
        for k, v in other.terms.items():
            out[k] += v
        return Poly(out)

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        out = defaultdict(int)
        for (m, state), c in self.terms.items():
            for (n, state2), d in other.terms.items():
                if {state, state2} == {"P", "Q"}:
                    continue
                joined = state2 if state == "E" else state
                out[(tuple(sorted(m + n)), joined)] += c * d
        return Poly(out)

    def scale(self, n):
        return Poly({k: v * n for k, v in self.terms.items()})

    def diff(self, variable):
        out = defaultdict(int)
        for (monomial, state), coefficient in self.terms.items():
            count = monomial.count(variable)
            if count:
                rest = list(monomial)
                rest.remove(variable)
                out[(tuple(rest), state)] += count * coefficient
        return Poly(out)

    def coeff(self, variable, power):
        return Poly({(tuple(x for x in monomial if x != variable), state): coefficient
                     for (monomial, state), coefficient in self.terms.items()
                     if monomial.count(variable) == power})

    def __eq__(self, other):
        return self.terms == other.terms

    def __repr__(self):
        return " + ".join(f"{c}*{'*'.join(m) or '1'}[{s}]"
                          for (m, s), c in sorted(self.terms.items())) or "0"


ZERO = Poly()
ONE = Poly({((), "E"): 1})
P = Poly({((), "P"): 1})
Q = Poly({((), "Q"): 1})


def var(name):
    return Poly({((name,), "E"): 1})


def mul(items):
    out = ONE
    for item in items:
        out = out * item
    return out


def add(items):
    out = ZERO
    for item in items:
        out = out + item
    return out


def forest(trees):
    return tuple(sorted(trees, key=repr))


@lru_cache(None)
def cuts(t):
    """Literal physical cuts of a slotted tree; None denotes a typed hole."""
    if t is None:
        return (((), None),)
    label, children = t
    out = [((t,), None)]
    for entries in product(*(cuts(c) for c in children)):
        pruning = forest(x for packet, _ in entries for x in packet)
        remainder = (label, tuple(r for _, r in entries))
        out.append((pruning, remainder))
    return tuple(out)


def h_add(a, b):
    out = defaultdict(int, a)
    for f, n in b.items():
        out[f] += n
    return {f: n for f, n in out.items() if n}


def h_mul(a, b):
    out = defaultdict(int)
    for f, n in a.items():
        for g, m in b.items():
            out[forest(f + g)] += n * m
    return {f: n for f, n in out.items() if n}


@lru_cache(None)
def antipode_tree(t):
    result = {(t,): -1}
    for pruning, remainder in cuts(t):
        if not pruning or remainder is None:
            continue
        term = {(): 1}
        for p in pruning:
            term = h_mul(term, antipode_tree(p))
        term = h_mul(term, {(remainder,): 1})
        result = h_add(result, {f: -n for f, n in term.items()})
    return result


def eval_h(h, values):
    return add(mul(values[t] for t in f).scale(n) for f, n in h.items())


def U(character, observer, t):
    return add(character(pruning) * observer(remainder)
               for pruning, remainder in cuts(t))


def char(values):
    return lambda f: mul(values[t] for t in f)


def inv_char(values):
    return lambda f: mul(eval_h(antipode_tree(t), values) for t in f)


def convolution_on_tree(left, right, t):
    return add(left(p) * right(() if r is None else (r,))
               for p, r in cuts(t))


@lru_cache(None)
def delta_forest(f):
    return tuple((forest(x for p, _ in entries for x in p),
                  forest(r for _, r in entries if r is not None))
                 for entries in product(*(cuts(t) for t in f)))


def convolution(left, right, f):
    return add(left(p) * right(r) for p, r in delta_forest(f))


@lru_cache(None)
def size(t):
    return 0 if t is None else 1 + sum(size(c) for c in t[1])


def small_trees(bound):
    levels = {0: (None,)}
    for n in range(1, bound + 1):
        level = [("a", ())] if n == 1 else []
        level.extend(("b", (child,)) for child in levels[n - 1])
        for i in range(n):
            level.extend(("r", (left, right))
                         for left in levels[i] for right in levels[n - 1 - i])
        levels[n] = tuple(level)
    return tuple(t for n in range(1, bound + 1) for t in levels[n])


def small_forests(trees, bound):
    def generate(start, remaining, chosen):
        yield tuple(chosen)
        for i in range(start, len(trees)):
            s = size(trees[i])
            if s <= remaining:
                yield from generate(i, remaining - s, chosen + [trees[i]])
    return tuple(generate(0, bound, []))


def check_small_universe(bound=4):
    trees = small_trees(bound)
    forests = small_forests(trees, bound)
    for t in trees:
        lhs, rhs = defaultdict(int), defaultdict(int)
        for p, r in cuts(t):
            for p1, p2 in delta_forest(p):
                lhs[(p1, p2, r)] += 1
            for p2, rr in cuts(r):
                rhs[(p, p2, rr)] += 1
        assert dict(lhs) == dict(rhs), ("coaction", t)
        left, right = {}, {}
        for p, r in cuts(t):
            sp = {(): 1}
            for tree in p:
                sp = h_mul(sp, antipode_tree(tree))
            left = h_add(left, h_mul(sp, {(): 1} if r is None else {(r,): 1}))
            sr = {(): 1} if r is None else antipode_tree(r)
            right = h_add(right, h_mul({p: 1}, sr))
        assert not left and not right, ("antipode", t)

    s, z = var("s"), var("z")
    values = {t: ONE.scale(size(t) + 1) + s.scale(i + 1)
              for i, t in enumerate(trees)}
    phi = char(values)
    inverse = inv_char(values)
    dot_phi = lambda f: phi(f).diff("s")
    gamma = lambda f: convolution(dot_phi, inverse, f)
    alpha = lambda t: mul(z for _ in range(size(t)))
    cumulative = {t: U(phi, alpha, t) for t in (None,) + trees}
    assert gamma(()) == ZERO
    for f in forests:
        if len(f) > 1:
            assert gamma(f) == ZERO, ("infinitesimal", f)
    for t in (None,) + trees:
        derivative = cumulative[t].diff("s")
        assert U(gamma, cumulative.__getitem__, t) == derivative
        single = add(gamma(p) * cumulative[r] for p, r in cuts(t) if len(p) == 1)
        assert single == derivative, ("connected sensitivity", t)
        assert U(inverse, cumulative.__getitem__, t) == alpha(t)

    g_values = {t: ONE.scale(i + 2) for i, t in enumerate(trees)}
    h_values = {t: ONE.scale((i + 3) ** 2) for i, t in enumerate(trees)}
    g = lambda f: g_values[f[0]] if len(f) == 1 else ZERO
    h = lambda f: h_values[f[0]] if len(f) == 1 else ZERO
    bracket = lambda f: convolution(g, h, f) - convolution(h, g, f)
    for f in forests:
        if len(f) != 1:
            assert bracket(f) == ZERO, ("Lie closure", f)
    ug, uh = ({t: U(op, alpha, t) for t in (None,) + trees} for op in (g, h))
    for t in (None,) + trees:
        lhs = U(g, uh.__getitem__, t) - U(h, ug.__getitem__, t)
        assert lhs == U(bracket, alpha, t), ("commutator representation", t)

    a, b = ("a", ()), ("b", (None,))
    chain = ("b", (a,))
    da = lambda f: ONE if f == (a,) else ZERO
    db = lambda f: ONE if f == (b,) else ZERO
    assert convolution(da, db, (chain,)) == ONE
    assert convolution(db, da, (chain,)) == ZERO
    print(f"PASS: all {len(trees)} slotted trees and {len(forests)} forests through degree {bound}")
    print("PASS: full cut-flag coaction, both antipode identities, polynomial inversion")
    print("PASS: logarithmic derivative infinitesimal and connected sensitivity on every tree")
    print("PASS: Lie closure, commutator representation, directional two-node witness")


def check_full_lq_frontiers():
    from check_lq_certificates import fixture, validate, raw_count

    source = fixture("q", "q")
    validate(source)

    def convert(node, scope=(), address=()):
        label = (node.rule, node.ant, node.succ,
                 tuple((c.ant, c.succ) for c in node.children), scope,
                 address if node.rule == "owner" else None)
        converted = []
        for i, child in enumerate(node.children):
            next_scope = scope + ((address, i),) if node.rule == "owner" else scope
            converted.append(convert(child, next_scope, address + (i,)))
        return label, tuple(converted)

    t = convert(source)
    cached = t[1][1][1][0]
    assert cached == t[1][1][1][1] and size(cached) == 5
    assert size(t) == 21 and len(cuts(t)) == 963
    assert tuple(raw_count(fixture(a, b), ["p", "q"])[0]
                 for a, b in product(("p", "q"), repeat=2)) == (1, 0, 0, 1)

    @lru_cache(None)
    def has_ghost(obj):
        return obj is not None and (obj[0][0] == "GR" or any(has_ghost(c) for c in obj[1]))

    u, v, z = map(var, ("u", "v", "z"))
    alpha = lambda obj: mul(z for _ in range(size(obj))) * (Q if has_ghost(obj) else ONE)
    old_value = lambda obj: v * Q if obj == cached else ZERO
    new_value = lambda obj: u * P if obj == cached else ZERO
    old = lambda f: mul(old_value(obj) for obj in f)
    new = lambda f: mul(new_value(obj) for obj in f)

    @lru_cache(None)
    def inverse_tree(obj):
        result = -old_value(obj)
        for pruning, remainder in cuts(obj):
            if not pruning or remainder is None:
                continue
            weight = old_value(remainder)
            if weight != ZERO:
                result = result - mul(inverse_tree(p) for p in pruning) * weight
        return result

    inverse = lambda f: mul(inverse_tree(obj) for obj in f)

    @lru_cache(None)
    def beta_tree(obj):
        return convolution_on_tree(new, inverse, obj)

    beta = lambda f: mul(beta_tree(obj) for obj in f)

    @lru_cache(None)
    def cumulative_old(obj):
        return U(old, alpha, obj)

    old_result = cumulative_old(t)
    new_result = U(new, alpha, t)
    rebased = U(beta, cumulative_old, t)
    zn = lambda n: mul(z for _ in range(n))
    assert old_result == zn(21) * Q + (v * zn(16) * Q).scale(2) + v * v * zn(11) * Q
    assert new_result == zn(21) * Q + u * u * zn(11) * P
    assert rebased == new_result
    assert beta_tree(cached) == u * P - v * Q
    active_terms = [(p, r) for p, r in cuts(t) if new(p) * alpha(r) != ZERO]
    assert len(active_terms) == 2
    assert sorted(size(r) for _, r in active_terms) == [11, 21]
    all_provider_supported = [(p, r) for p, r in cuts(t) if new(p) != ZERO]
    assert len(all_provider_supported) == 4
    s = var("s")
    enlarged = lambda f: mul(v * Q + s * u * P if obj == cached else ZERO for obj in f)
    enlarged_result = U(enlarged, alpha, t)
    assert enlarged_result == old_result + s * s * u * u * zn(11) * P
    assert enlarged_result.coeff("s", 1) == ZERO
    assert enlarged_result.coeff("s", 2) == u * u * zn(11) * P
    assert min(m.count("z") for (m, _), n in new_result.terms.items() if n > 0) == 11
    print("PASS: all963 native-like21-node LQ cuts enumerated without restricting coproduct")
    print("PASS: exactly4 cache-supported frontiers;2 survive shared-owner join; minimum11")
    print("PASS: old q-cache to new p-cache full963-cut antipode rebase")
    print("PASS: genuine cooperative update: first sensitivity0, Hasse order2=u²z11[P]")
    print("Old cache polynomial:", old_result)
    print("New cache polynomial:", new_result)


def main():
    a = ("a", ())
    r = ("r", (None, None))
    bL = ("r", (None, a))
    bR = ("r", (a, None))
    t = ("r", (a, a))
    trees = (a, r, bL, bR, t)
    assert len(cuts(t)) == 5 and bL != bR
    expected_s = {(t,): -1, forest((a, bL)): 1,
                  forest((a, bR)): 1, forest((a, a, r)): -1}
    assert antipode_tree(t) == expected_s

    x, y, l, rr, v, d = map(var, ("x", "y", "uL", "uR", "v", "d"))
    values = dict(zip(trees, (x, y, l, rr, v)))
    alpha = dict(zip((None, a, r, bL, bR, t),
                     map(var, ("A0", "Aa", "R", "BL", "BR", "T"))))
    phi = char(values)
    inverse = inv_char(values)
    cumulative = lambda obj: U(phi, alpha.__getitem__, obj)
    for obj in (None,) + trees:
        assert U(inverse, cumulative, obj) == alpha[obj]

    values2 = {**values, a: x + d}
    psi = char(values2)
    beta_values = {obj: convolution_on_tree(psi, inverse, obj) for obj in trees}
    beta = char(beta_values)
    assert beta_values[t] == -(d * (l + rr)) - d * d * y
    for obj in (None,) + trees:
        assert U(beta, cumulative, obj) == U(psi, alpha.__getitem__, obj)
    expected_change = d * (alpha[bL] + alpha[bR]) + (x * d).scale(2) * alpha[r] + d * d * alpha[r]
    assert U(psi, alpha.__getitem__, t) - cumulative(t) == expected_change

    u, vq, z, w = map(var, ("u", "v", "z", "w"))
    cached_leaf = u * P + vq * Q
    assert cached_leaf * cached_leaf == u * u * P + vq * vq * Q
    # Boundary examples only. No actual typed LQ proof is claimed.
    source_alpha = {None: ONE, a: z * Q, r: z,
                    bL: z * z * Q, bR: z * z * Q, t: z * z * z * Q}
    source_phi = char({a: cached_leaf, r: y, bL: l, bR: rr, t: w})
    actual = U(source_phi, source_alpha.__getitem__, t)
    expected = z * z * z * Q + (z * z * vq * Q).scale(2) + z * (u * u * P + vq * vq * Q) + w
    assert actual == expected

    print("PASS: 5 physical corolla cuts; ordered one-leaf remainders distinct")
    print("PASS: connected-graded antipode agrees with four-term formula")
    print("PASS: generic inversion on all six typed remainder states")
    print("PASS: cache rebase on all six states and exact quadratic update")
    print("PASS: simultaneous shared-port replacement and multiplicity 2")
    print("C_phi(t) =", actual)
    print("Evidence: exact finite symbolic checks only; no Lean/native/LQ revival claim")
    check_small_universe()
    check_full_lq_frontiers()


if __name__ == "__main__":
    main()
