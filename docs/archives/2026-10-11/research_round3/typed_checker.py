"""Independent sorted CK antichain / correlated provider residual checker.
Finite ranked rule registry. An extracted root is represented by an explicit
sort-labelled hole (never by the CK unit). Provider correlations are recognised
by a deterministic word automaton on (sort, target-observer-state) letters.
No independent-provider or unrestricted-grafting assumption is used.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product

@dataclass(frozen=True)
class Rule:
    name: str
    inputs: tuple
    output: str

@dataclass(frozen=True)
class Tree:
    rule: str
    children: tuple = ()

@dataclass(frozen=True)
class Hole:
    sort: str

class Model:
    def __init__(self, rules, observe_rule, word_states, word_initial, word_final,
                 word_step, good):
        self.rules = {r.name:r for r in rules}
        self.observe_rule = observe_rule
        self.word_states = tuple(word_states)
        self.word_initial = word_initial
        self.word_final = frozenset(word_final)
        self.word_step = word_step
        self.good = good
        self.sorts = tuple(sorted({r.output for r in rules} |
                                  {s for r in rules for s in r.inputs}))
        self.witness = {s:{} for s in self.sorts}
        self.saturation_rounds = 0
        while True:
            additions=[]
            for r in rules:
                for qs in product(*(tuple(self.witness[s]) for s in r.inputs)):
                    q=observe_rule(r.name,qs)
                    if q not in self.witness[r.output]:
                        children=tuple(self.witness[s][v] for s,v in zip(r.inputs,qs))
                        additions.append((r.output,q,Tree(r.name,children)))
            changed=False
            for s,q,t in additions:
                if q not in self.witness[s]:
                    self.witness[s][q]=t
                    changed=True
            self.saturation_rounds += 1
            if not changed: break
        self.reachable={s:tuple(d) for s,d in self.witness.items()}

    @lru_cache(None)
    def sort(self,t):
        if isinstance(t,Hole): return t.sort
        r=self.rules[t.rule]
        if tuple(self.sort(c) for c in t.children)!=r.inputs:
            raise ValueError('ill-typed rule instance')
        return r.output

    @lru_cache(None)
    def observe(self,t):
        self.sort(t)
        if isinstance(t,Hole): raise ValueError('cannot observe an unfilled hole')
        return self.observe_rule(t.rule,tuple(self.observe(c) for c in t.children))

    def letter(self,t): return (self.sort(t),self.observe(t))

    def provider_accepts(self, providers):
        u=self.word_initial
        for t in providers: u=self.word_step(u,self.letter(t))
        return u in self.word_final

    def identity_word_action(self): return tuple(self.word_states)

    def letter_action(self,letter):
        return tuple(self.word_step(u,letter) for u in self.word_states)

    def compose_actions(self,actions):
        ans=self.identity_word_action()
        indices={u:i for i,u in enumerate(self.word_states)}
        for a in actions: ans=tuple(a[indices[u]] for u in ans)
        return ans

    @lru_cache(None)
    def hole_relation(self,sort):
        return frozenset((u,q,self.word_step(u,(sort,q)))
                         for u in self.word_states for q in self.reachable[sort])

    @lru_cache(None)
    def combine_relations(self,rule,children):
        """(input provider DFA state, filled target state, output DFA state)."""
        r=self.rules[rule]
        if len(children)!=len(r.inputs): raise ValueError('arity mismatch')
        out=set()
        for u in self.word_states:
            acc={(u,())}
            for rel in children:
                by={}
                for a,q,b in rel: by.setdefault(a,[]).append((q,b))
                acc={(b,qs+(q,)) for a,qs in acc for q,b in by.get(a,())}
            out.update((u,self.observe_rule(rule,qs),v) for v,qs in acc)
        return frozenset(out)

    @lru_cache(None)
    def relation(self,skeleton):
        self.sort(skeleton)
        if isinstance(skeleton,Hole): return self.hole_relation(skeleton.sort)
        return self.combine_relations(skeleton.rule,
                    tuple(self.relation(c) for c in skeleton.children))

    def residual_accepts(self,skeleton):
        return self.relation_accepts(self.sort(skeleton),self.relation(skeleton))

    def relation_accepts(self,sort,rel):
        return not any(u==self.word_initial and v in self.word_final and
                       not self.good(sort,q) for u,q,v in rel)

    def counterexample(self,skeleton):
        """Return a real accepted tuple producing a bad assembly, or None.
        Enumeration here is over FINITELY MANY reachable observer states per
        hole, not bounded trees; saturation provides genuine tree witnesses.
        """
        hs=holes(skeleton)
        for qs in product(*(self.reachable[s] for s in hs)):
            providers=tuple(self.witness[s][q] for s,q in zip(hs,qs))
            assembled=fill(self,skeleton,providers)
            if self.provider_accepts(providers) and not self.good(self.sort(assembled),self.observe(assembled)):
                return providers,assembled
        return None

    @lru_cache(None)
    def cut_summary(self,t):
        """Finite observer state of ALL antichain cuts, including empty/root.
        Each pair holds actual material word action and the residual recognizer
        state of the typed remainder. Distinct cuts with equal observations are
        intentionally merged: this is Boolean recognition, not CK coefficients.
        """
        s=self.sort(t)
        out={(self.letter_action(self.letter(t)),self.hole_relation(s))}
        for choices in product(*(self.cut_summary(c) for c in t.children)):
            action=self.compose_actions(tuple(x[0] for x in choices))
            rel=self.combine_relations(t.rule,tuple(x[1] for x in choices))
            out.add((action,rel))
        return frozenset(out)

    def query(self,t):
        initial_index=self.word_states.index(self.word_initial)
        return any(a[initial_index] in self.word_final and
                   self.relation_accepts(self.sort(t),rel)
                   for a,rel in self.cut_summary(t))


def holes(t):
    if isinstance(t,Hole): return (t.sort,)
    return sum((holes(c) for c in t.children),())


def fill(model,skeleton,providers):
    it=iter(providers)
    def go(t):
        if isinstance(t,Hole):
            try: p=next(it)
            except StopIteration: raise ValueError('too few providers')
            if model.sort(p)!=t.sort: raise ValueError('provider type mismatch')
            return p
        return Tree(t.rule,tuple(go(c) for c in t.children))
    ans=go(skeleton)
    try: next(it)
    except StopIteration: return ans
    raise ValueError('too many providers')


def direct_cuts(model,t):
    """A separate structural enumerator; returns (removed tuple, open remainder)."""
    yield (t,),Hole(model.sort(t))
    for cuts in product(*(tuple(direct_cuts(model,c)) for c in t.children)):
        yield sum((x[0] for x in cuts),()),Tree(t.rule,tuple(x[1] for x in cuts))


def trees_up_to(model,bound):
    by={(s,n):[] for s in model.sorts for n in range(1,bound+1)}
    def compositions(total,k):
        if k==0:
            if total==0: yield ()
            return
        for n in range(1,total+1):
            for tail in compositions(total-n,k-1): yield (n,)+tail
    for n in range(1,bound+1):
        for r in model.rules.values():
            for ns in compositions(n-1,len(r.inputs)):
                for cs in product(*(by[s,k] for s,k in zip(r.inputs,ns))):
                    by[r.output,n].append(Tree(r.name,cs))
    return tuple(t for ts in by.values() for t in ts)


def saturate_context_states(model,cap=100000):
    """Least fixed point of ALL sorted skeleton recognizer states.
    Return actual skeleton witnesses. A cap is an explicit failure, never an
    unannounced approximation to saturation.
    """
    witnesses={s:{model.hole_relation(s):Hole(s)} for s in model.sorts}
    rounds=0
    while True:
        additions=[]
        for r in model.rules.values():
            for rels in product(*(tuple(witnesses[s]) for s in r.inputs)):
                rel=model.combine_relations(r.name,rels)
                if rel not in witnesses[r.output]:
                    t=Tree(r.name,tuple(witnesses[s][z] for s,z in zip(r.inputs,rels)))
                    additions.append((r.output,rel,t))
        changed=False
        for s,rel,t in additions:
            if rel not in witnesses[s]:
                witnesses[s][rel]=t
                changed=True
                if sum(map(len,witnesses.values()))>cap:
                    raise RuntimeError('context state saturation cap exceeded')
        rounds+=1
        if not changed: return witnesses,rounds
