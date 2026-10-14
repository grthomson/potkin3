# Safe naming quotients and the open-scope bridge

12 October 2026. Paper-level addendum to `polynomial_bridge.md`; not Lean
checked. This covers owner-name bureaucracy, not general proof identity.

## 1. The owner-name quotient actually justified now

Begin with a raw occurrence-sensitive LQ certificate tree in which every
ghost-disjunction owner carries a distinct identifier and every ghost initial
records its selected owner identifier(s). Its external boundary is an ordered
list of imported ancestor owners with their roles, checkpoint bits and colours.
Internal owners have fresh identifiers relative to that list. Formula atoms
such as p,q remain fixed labels throughout this construction.

A permitted renaming changes internal owner identifiers bijectively and
changes all their bound references by the same bijection. At a fixed named
external boundary it fixes imported identifiers. A more general boundary
transport also renames the imported list, but carries that list's bijection
explicitly as part of the interface transport. Neither operation permutes
premise slots, identifies different physical vertices, or changes formulas.

Canonicalisation traverses the tree carrying its ordered owner environment.
Each owner inserts a new entry; each ghost-leaf reference is replaced by its
de Bruijn position in the active environment. The local-state transitions
are exactly those in `polynomial_bridge.md`. The initial imported environment
is retained; it is never reset to an empty stack at a cut.

**Theorem (safe owner-name quotient).** For raw locally scoped certificate
trees with the same literal sequent/rule tree and matching ordered external
interfaces, their canonical de Bruijn presentations are equal if and only if
the raw trees differ by a consistent owner renaming. At a fixed named
interface, that renaming fixes the imported owner names. With boundary
transport, it extends the specified bijection of imported positions.

**Proof.** A consistent renaming does not change a reference's position in the
active environment, so canonicalisation is invariant. Conversely equal
canonical presentations have identical physical owner positions. Match the
identifier at each internal owner position in the first tree to the identifier
at that position in the second, and match imported identifiers using the
boundary bijection. Distinctness/freshness makes this assignment bijective.
Every selected de Bruijn position resolves to precisely the matched owner in
the other tree, so all references are carried correctly. Operation labels,
colours and literal sequents already agree. QED.

This yields an honest equivalence-class carrier for the owner-naming
bureaucracy. It is not just a representation trick. Physical occurrences and
their cut multiplicities survive the quotient unchanged.

### Cut compatibility

For a raw tree T and each physical cut address set c, owner renaming pi gives
the same physical cut set in pi(T). Its two pieces are the consistently
renamed pieces of T, including any owner references exposed at their boundary.
Canonicalising those pieces with their inherited boundary environments gives
exactly the pieces obtained by cutting the canonical presentation of T.

The proof is a restriction argument: renaming preserves all parent/child
addresses and scope paths; each reference resolves to the same environment
position; cut-edge states contain the same ordered environment on both
sides. Thus the full cut correspondence and its nested flags descend to this
particular quotient. No quotienting of structural-rule bureaucracy or
commuting conversions is included in the theorem.

There is an important interface distinction. If two imported names have a
meaning in an enclosing context, erasing their spellings does not authorise
identifying their ports. Their ordered positions and the map back to the
ambient interface remain. The concrete-colour grammar can compare two stacks
with the same colours/roles/bits because positions still distinguish their
owners; grafting interprets each position relative to its new actual ancestor.

## 2. Why source alpha-equivalence alone is insufficient

Consider the alpha-equivalent process terms

    lambda x. x        and        lambda y. y.

Extract their bodies at the same physical address. If the extracted pieces
are represented as ordinary terms with newly free textual names, the crown
terms are x and y. Ordinary alpha-equivalence does not identify distinct free
variables. Consequently a map that quotients the whole source by bound-name
alpha-equivalence while freezing those exposed free names does not make
extraction well-defined: the same source class produces different crown
classes. The remainder lambda x.[-] may be alpha-equivalent to
lambda y.[-], but that does not repair the lost crown/remainder linkage.

Two safe presentations are available.

1. **Canonical external scope positions.** Both bodies are represented as
   the variable at imported binder position 0, with an interface saying that
   this is the enclosing lambda's binder. The remainder carries the matching
   binder-position port. The body is not treated as an unrelated globally
   free variable named x or y.
2. **Boundary-renaming groupoid.** Objects are open terms plus their explicit
   binder interfaces; morphisms consistently rename both internal binders
   and exposed ports. The source alpha-renaming induces one compatible
   renaming of the cut crown, remainder, and seam. Composition is performed
   over the interface, not after independently discarding port identities.

These are ways to formulate the required congruence theorem, not a licence
to identify free names arbitrarily. In a concurrent process calculus, a
genuinely external shared channel stays shared across copies. A freshly copied
internal binder receives a fresh physical identity. Neither distinction is
settled by string renaming alone.

The owner-name theorem above proves this mechanism for our certificate
owners. Its extension to lambda binders, channel binders, simultaneous
substitution and process copying still requires a binder-aware native syntax
and its explicit cut/substitution equivariance theorem. We have not proved
that extension merely by exhibiting the lambda example. In particular we
claim no quotient by beta/eta equivalence, commuting conversions, process
bisimulation, or general proof permutations.

## 3. What the literature lineage does and does not identify

Ciabattoni--Genco's 2018 work provides embeddings between hypersequents and
2-systems, with scoped upper-rule uses discharged by lower rules. That is a
positive source for the scope/interface architecture. Lang's 2023 development
provides analytic systems and, for LQ, a precise ghost-rule revival condition.
The local grammar developed here exactly presents that LQ certificate
condition. Marin--Miller--Pimentel--Volpe's focusing paper, Section 4.3,
Example 22, separately identifies the propositional weak-excluded-middle
system it obtains with the corresponding hypersequent-derived 2-system.

These connections orient one programme; they are not already an equality of
its native representations. Our canonicalisation theorem handles owner
identifiers inside the specified LQ certificate syntax. It does not yet
construct the native POTKIN3 hypersequent/2-system translation, identify
focused phase expansions with ghost-rule nodes, or prove those translations
commute with all CK cuts. Formula revival can add logical/structural nodes;
focused macro expansion can add internal extraction positions. Those extra
positions must be accounted for by a cut-fibre or local expansion theorem,
not hidden by declaring the translations Hopf morphisms.

The exact next transport target is therefore an open-boundary translation
with: literal sequent correspondence; an explicit ordered scope-port map;
fresh internal owner naming; matching formula-flow/checkpoint obligations;
and a specification of how each native physical cut corresponds to the
expanded representation's cut data. This is a substantive D4/D6 theorem,
with D3 structural assumptions stated separately. The safe owner-name
quotient already proved is available within that theorem, rather than a
substitute for it.

## Review and sources

The revival agent independently checked the local-state endpoint conventions,
owner-choice multiplicities and de Bruijn scope presentation. The adversarial
agent independently checked the connected quotient and one-leg comodule, and
the Green/profile identities; it specifically required that native rigid
owner IDs be mapped to physical ancestor positions explicitly. This addendum
states that requirement and its exact current scope.

Primary literature (the CK/interface conclusions above are our deductions):

* Ciabattoni and Genco, *Hypersequents and Systems of Rules: Embeddings and
  Applications* (2018), https://arxiv.org/abs/1805.04852 .
* Lang, *Some Analytic Systems of Rules* (2023), Definition 5,
  https://discovery.ucl.ac.uk/id/eprint/10182303/1/tableauxRep.pdf .
* Marin, Miller, Pimentel and Volpe, *From axioms to synthetic inference rules
  via focusing* (2022), Section 4.3,
  https://discovery.ucl.ac.uk/10142554/1/1-s2.0-S0168007222000057-main.pdf .
