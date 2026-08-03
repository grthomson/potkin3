# P3-2 architecture

Phases A--C and independent insertion are implemented. The nested-cut
architecture exposes source-addressed transport and precise partial results;
it does not claim the still-missing actual-region, actual-factor,
sequential-root, composed two-stage-filling, or finite-schedule theorems.

## Dependency spine

The aggregate `Potkin.lean` imports one short foundation spine:

```text
Language
  -> Boundary
  -> Occurrence
  -> ProofTheory
  -> Presentation
       \
        -> Checked <- CKTree
              -> RootCut -> CKCut -> CKCutPuncture
                    \          -> CKCutEnumeration -> CKCutValidity
                     \          -> RealizedCut <- RealizedSector
                      \         -> GeneralFilling -> NestedCoherence
                      -> RootProjection
                            -> Examples.Anonymous
                            -> Examples.RecursiveCut
                            -> Examples.MaterialBase
                            -> Examples.Coherence
```

There is deliberately no `GenericCalculusSnapshot`. A `ProofTheory` supplies
admission data, and an `EquippedPresentation T` is directly indexed by that
theory.

## Language and whole boundaries

`Potkin.Language` defines a signature with atoms and operation symbols indexed
by arity. `Formula.app` retains its ordered `Fin n` argument family. A symbol
has no logical behaviour merely because of its name or arity.

`Potkin.Boundary` defines formula contexts and both sides of a sequent as
finite multisets. A `Hypersequent` is a finite multiset of displayed sequents
together with a proof that it is nonempty. Consequently exchange is canonical
at the context and displayed-component levels, while multiplicity is not
discarded. Every premise and conclusion used below is one entire
`Hypersequent`, not one selected component.

## Fully instantiated local occurrences

`Potkin.Occurrence` separates an occurrence's immutable shape from its
admission:

- `LocalOccurrence.id` is the stable registry key;
- `kind` is exactly `material`, `logical`, or `structural`;
- `shape.premises` is an ordered list of whole hypersequents;
- `shape.conclusion` is one whole hypersequent;
- `instanceData` is caller-selected, already-instantiated occurrence data;
- `incidence` is either unknown (`none`) or supplied
  (`some componentIncidence`).

A supplied `ComponentIncidence` first carries an `OccurrenceProfiles` value.
Each `ComponentProfile` is an ordered list proved to enumerate the exact
component multiset. Thus every displayed occurrence, including each copy of
an equal sequent, has a separate local slot tied to its displayed value. A
`ComponentEdge` is oriented from one such slot in one ordered premise to one
conclusion slot. Dependent `Fin` fields validate all three endpoints against
those exact profiles. The edge collection is a `Finset`, so duplicate edges
are canonicalised. `none` is not equal to `some` of the empty edge set. P3-0
does not infer formula action, functionality, totality, or coherent
reindexing from incidence.

## Bases, rules, and proof theories

`Potkin.ProofTheory` makes a `MaterialBase sigma InstanceData primitive` an
exact-occurrence-indexed membership predicate. Membership is indexed by the
whole `LocalOccurrence`: its constructor ID (the manuscript's tag), kind, ordered premises,
conclusion, instance data, and supplied incidence cannot be replaced by a
transport. Membership proves material kind and support of every premise and
the conclusion by an explicitly chosen `PrimitiveFragment`. Positive finite
arity is unrestricted; the atom-only fragment is merely a convenience.

The base has no weakening, contraction, Cut, substitution, monotonicity, or
closure field. `BaseHom B C` maps `B.Member o` to `C.Member o` for the same
implicit occurrence `o`; there is deliberately no occurrence map. Identity,
composition, unit, and associativity are proved. Presentations and realised
components have identity/composition `HEq` laws; checked derivations have the
corresponding exact action on their full occurrence-decorated realizations.
Direct proof-term `HEq` for `CheckedDerivation` remains a dependent
presentation-index cast problem and is not asserted.

A `RuleSystem` has separate logical and structural admission predicates on
fully instantiated occurrences. A `ProofTheory` combines a material base,
that fixed rule system, and a separate initial-boundary predicate. Since the
occurrence-kind vocabulary has only three cases, an initial is admitted as a
nullary logical occurrence through the distinct `Admits.initial` constructor.

`ProofTheory.Admits` is local to one occurrence. It adds no proof-global
normality, freshness, liveness, or search condition.

`Admits.material` takes exact base membership and imposes no nullary
restriction. Logical initials remain a separate nullary logical constructor;
logical and structural occurrence admission is unchanged.

## Finite equipped presentations and checking

`Potkin.Presentation` defines `EquippedPresentation T` as:

- one finite registry list;
- a proof that its occurrence IDs have no duplicates;
- a proof that every listed occurrence is admitted by `T`.

`lookup` is executable and returns the exact registered occurrence together
with its membership and ID-equality evidence. `mapBase` retains the registry
literally and transports only admission evidence.

`Potkin.Checked` separates two levels:

- `RawDerivation` contains node IDs and ordered raw children. Its anonymous
  `puncture` carries no boundary claim: a typed requirement can only be
  inferred from a retained checked parent. The complete checker rejects it
  with `unexpectedPuncture`.
- `CheckedDerivation P G` is indexed by the exact presentation and its whole
  root boundary. `CheckedChildren P premises` is indexed by the entire ordered
  premise-boundary list.

`EquippedPresentation.check` infers a checked root, while `checkAt` additionally
requires one exact whole root boundary. They reject an unknown ID, a raw
puncture, wrong arity, or a wrong ordered/root boundary.
`CheckedDerivation.boundaryCorrect` exposes the intrinsic root guarantee.

The `CheckedDerivation.node` and `CheckedChildren` constructors are private to
`Checked.lean`. The checker is therefore the only public construction route.
The anonymous fixture extracts its derivations from proved-successful
`checkAt` results; it does not manufacture checked nodes.

## Rich checked and open CK carriers

`Potkin.CKTree` first defines `OpenTree Boundary Decoration`, the CK
combinatorics generic in an arbitrary boundary type. Its ordered
`OpenChildren` family keeps premise positions distinct. `CKTree` is the
occurrence-decorated specialization indexed by whole hypersequents and has
exactly two constructors:

- `interface G`, a typed vacancy with no ordinary vertex;
- `ordinary o children`, a positive vertex decorated by the complete local
  occurrence and supplied with ordered children indexed by all of `o`'s
  premise boundaries.

`CheckedDerivation.realize` structurally maps a complete checked derivation to
an open CK tree without losing occurrence ID, kind, instance data, incidence,
boundary, or child order. Its image contains no interfaces. `CKTree.Bare` is
the whole-hypersequent instance of the boundary-generic carrier with unit
decoration. `CKTree.erase` is the explicit comparison map: it forgets
occurrence decoration but retains every whole boundary index and ordered tree
shape. Erasure is not injective and is not used to infer source rule identity.

The ambient CK type is intentionally larger than the realised sector. An
arbitrary `CKTree` can contain interfaces or occurrence decorations not tied
to a particular registry. `LocallyAdmittedTree P t` is the recursive sector
certificate: an interface is an admitted vacancy, while every ordinary node
must be the exact occurrence of `P.registry` and every ordered child must be
locally admitted. `RealizedOpenComponent P` adds a positive ordinary root.
This is not defined as the range of complete proof realisation: it includes
admitted open terms whose interfaces may have no complete filler. Complete
`CheckedDerivation`s enter the sector, and `BaseHom` transports the certificate
while leaving the ambient decorated tree literally unchanged.

## Immediate and recursive cutting

`Potkin.RootCut` fixes the internal address representation to zero-based child
selectors, with `[]` at the root. `CKTree.VertexAt` has no interface case, so
an interface is never accidentally certified as a vertex.

A `RootConstruction` retains one positive occurrence and its exact ordered
children. A `RootCut` selects a nonempty finite set of immediate child slots
and requires each selected child root to be ordinary. Its sites therefore
denote existing nonroot vertices and their singleton addresses are pairwise
prefix-incomparable when their slots differ.

The cut keeps two deliberately different views:

- `detached : cut.Site -> CKTree ...` is the dependent, site-indexed tuple.
  It retains exact address alignment and is the input to reconstruction.
- `detachedForest` maps those selected occurrences into the positive
  `CKForest` carrier. It forgets address order but preserves an ordinary-root
  factor for every selected site, including equal tree presentations at
  distinct sites.

`retained` preserves the original positive root and all unselected children,
replacing each selected child by `interface` at exactly that premise's whole
boundary. `fill` accepts a filler indexed by every selected site. The theorem
`fill_detached_reconstructs` proves that filling with the retained detached
family gives the original root construction. No search, assembly, Mix,
Gentzen Cut, proof normalization, or forest multiplication occurs during
filling.

P3-1 preserves this API unchanged and adds `Potkin.CKCut`. Its intrinsic
recursive decomposition is the occurrence-witness representation. At each
ordered child a branch is exactly one of:

- detach that ordinary child root and stop below it;
- descend into one recursively constructed cut;
- the empty recursive descent, which selects nothing in that branch.

An interface has only the empty descent. The public `CKCut t` additionally
requires `t` to have a positive ordinary root, so a bare typed interface is
never a connected cut source. There is no constructor selecting the current
root. A detach branch suppresses all descendant choices, and independent
ordered branches combine by a Cartesian product, so ancestor/descendant pairs
are unrepresentable. `ProperCKCut` is the nonempty subtype; the all-descend
plan is the empty cut retained for later coproduct work.

Recursive sum site identities retain occurrence multiplicity. Their canonical
walk follows premise order and recursive address order, yielding the
lexicographically ordered address list and aligned `detachedTuple` before the
separate `detachedForest` projection. Equal detached trees at different
addresses remain different tuple occurrences.

`CKCut.remainder` replaces exactly detach choices by typed interfaces.
Existing interfaces outside detached regions stay at their old addresses;
existing interfaces inside a detached subtree travel with that detached
factor. Filling ranges only over the new site type, so it cannot fill an old
interface accidentally. Constructor induction proves exact reconstruction
and the ordinary-vertex degree partition.

`Potkin.CKCutPuncture` gives this provenance distinction a total computational
address semantics. A new hole means that the source status was ordinary and
the remainder status is interface; `newHoleAt_iff_selectedSite` proves that
this happens exactly at one selected site. Separately, an old source interface
outside every selected-address prefix remains an interface at the identical
address. `CKCut.requirement` exposes the site's exact whole boundary, and
`selectedPuncture_matches_detachedRoot` packages the relational remainder
interface with equality to the aligned detached root boundary. These are
universal recursive theorems, not fixture observations.

`Potkin.CKCutEnumeration` uses the same decomposition as an executable
enumerator. Tail choices form the outer Cartesian loop and earlier premise
slots vary fastest. The plan, child-product, and branch-alternative
enumerations are each proved complete and duplicate-free. Validation compares
the canonical address list after lexicographically sorting the request;
duplicates are deliberately retained by sorting and therefore still rejected.
Roots, interfaces, duplicates, and prefix-comparable requests have no
structural witness.

`Potkin.CKCutValidity` supplies the independent extensional direction. A
`ValidAddressCut t` is a genuine finite address set whose members are existing
nonroot ordinary vertices, are pairwise prefix-incomparable, and whose source
is positive. Constructor recursion restricts that set to each exact premise;
a relative root forces whole-branch detachment, otherwise the construction
descends. `ValidAddressCut.toCut` preserves the address finset exactly, and
`exists_mem_enumerate_with_addressFinset` proves that every such external
finite antichain occurs in the recursive enumeration.

Direct extensional equality of arbitrary legacy `CKCutPlan` values remains
awkward because dependent elimination exposes occurrence conclusions through
different projections. P3-2 puts identity at the correct public level:
`ExtensionalCKCut` is a one-field structural wrapper around `ValidAddressCut`
and is proved equivalent to it. Its plan is the canonical recursive
compilation. Public enumeration deduplicates on structural address identity,
is Nodup and exact-once, and validation returns the unique public cut. No
quotient is used; constructor-recursive `CKCut` remains an implementation
witness.

`Potkin.RealizedCut` combines recursive cuts with the exact-presentation local
admission judgement. Admission is hereditary to every addressed detached
factor and to the retained remainder. Both closures, their component
packaging, and reconstruction are stable under proof-preserving `BaseHom`
transport. This depends on admission being local to finite registered
occurrences; no claim is made for proof-global admission conditions.

## General filling and typed punctures

`Potkin.GeneralFilling` distinguishes recursive `CKTree.IsComplete` from
local admission and adds proof-relevant `PunctureAt H tree p` path data, which
retains the exact boundary erased by the older untyped interface relation.
`HasPunctureAt` is its propositional `Nonempty` wrapper. Arbitrary filling has
an exact puncture decomposition: a result puncture is either an old source
puncture outside every selected prefix or a filler puncture whose relative
address is prefixed by its selected source address. Constructor recursion
proves root preservation, local admission, completeness, old-hole
preservation, filler-hole prefixing, distinguished reconstruction, and base
transport.

Typed single-puncture insertion fixes all retained occurrence constructors.
Insertion prefixes every replacement-internal address. A second
prefix-incomparable puncture transports at its literal old address, and the
two possible insertion schedules are structurally equal.
`insertIncomparable_replacementPunctures_prefixed` places internal punctures
of both replacements at their respective literal outer-prefix addresses in
that common result.

## Nested source-addressed coherence

`Potkin.NestedCoherence` uses `StrictlyInside inner outer` for the consistent
strict-prefix orientation. Two valid cuts are `Noncrossing` when their address
sets are disjoint and they do not exhibit both cross orientations;
incomparable branches impose none.

Transport splits the second cut into `retainedAfter` and one `insideAfter`
family for each exact detached first occurrence. Entries retain original
source addresses, and detached entries also retain relative addresses and the
prefix equations recovering their source. Full status preservation outside
selected prefixes and exact detached/source lookup prove that these are valid
cuts of the target remainder and detached trees.

`CanonicalTwoStageWitness` stores the noncrossing certificate and determines
derived transports, four labelled source regions representing three geometric
layers, and the source-nearest final root frontier. Its
`detachedOccurrenceEquiv` is a `Sum` swap of source-cut address identities; it
preserves distinct source occurrences but does not compare actual transported
detached tree entries. Reconstruction is proved by separate retained and
inside-factor laws in both directions, not by one composed two-stage schedule.
A `RankedCutHierarchy` supplies a global finite rank respected by every
comparable pair and determines a final source frontier.

`sourceRegion_swap` compares only the four-valued source-address classifier;
it does not identify transported region components, occurrence sets, or
relative maps, and it does not use the witness's `noMixedOrientation` field.
That field presently proves rejection/diagnostic facts, not a substantive
coherence theorem. The reconstruction laws also restart from each original
first-stage cut rather than filling forward from the further-cut final root.

This does not yet prove structural equality of the two actual sequential
remainders with the canonical frontier remainder. That exact target is named
`ExactTwoStageRemainderCoherence` but deliberately has no theorem. The proved
frontier result is only common untyped interface presence at every canonical
frontier address, not equality of roots or interface sets. The current
parenthesisation result is generic associativity of append for supplied
address-segment leaves; it is not connected to hierarchy levels or arbitrary
iterated cut schedules. All stronger statements require a recursive theorem
composing retained remainders without erasing occurrence decorations.

The rank is necessary. Three pairwise noncrossing families can force the
cycle `A < B < C < A`; hence manuscript v56 clause (iv) needs a globally
acyclic/ranked orientation hypothesis, and its two-cut definition needs
explicit set disjointness.

## Forests and root projections

`Potkin.CKTree` packages an ordinary-rooted `CKComponent`; its interior may be
open. A `CKForest` is a multiset of these connected factors, so external
exchange is commutative and multiplicity remains.

Two projections have different information content:

- `blockRoots` returns one whole hypersequent boundary per connected factor;
- `flattenedRoots` returns `none` for the empty forest and otherwise binds all
  displayed occurrences into a proof-carrying nonempty whole hypersequent.

For the anonymous binary example, the flattened projection of the connected
proof of `S | T` equals that of the separate `S` and `T` forest. The block
projection distinguishes them because the former has one connected block and
the latter has two. This is a structural presentation theorem, not a proof
quotient or an operational assembly rule.

## Anonymous fixtures

`Potkin.Examples.Anonymous` supplies two material nullaries, one binary logical
occurrence, and one unary structural occurrence. It checks the raw binary and
unary candidates, demonstrates unknown versus known-empty incidence, selects
both immediate children of the binary root as one nontrivial cut, proves the
address and puncture facts, reconstructs the tree, transports it along a base
homomorphism, and proves the two root-projection results.

The fixture has no intended proof-theoretic interpretation beyond exercising
the generic declarations.

`Potkin.Examples.RecursiveCut` reuses the same anonymous occurrences for the
manuscript-shaped tree `i(m(bS,bT))`. It records the empty cut and exactly four
proper address families, their literal addressed tuples and retained
remainders, the degree splits, and executable invalid-address cases. A second
open source distinguishes its old interface from a newly cut site. A duplicate
binary source detaches two structurally equal `bS` trees at different premise
addresses, demonstrating tuple identity and forest multiplicity separately.

These finite examples are acceptance witnesses and falsifiers only. The
universal claims are the constructor-recursive library theorems, not agreement
with the fixture enumeration.
