# P3-0 architecture

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
              -> RootCut
                    -> RootProjection
                          -> Examples.Anonymous
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

`Potkin.ProofTheory` makes a `MaterialBase` an arbitrary boundary-indexed
evidence family. It has no weakening, contraction, Cut, substitution,
monotonicity, or closure field. A `BaseHom B C` is exactly a family of maps
from `B.Evidence G` to `C.Evidence G`; identity and composition are ordinary
function identity and composition.

A `RuleSystem` has separate logical and structural admission predicates on
fully instantiated occurrences. A `ProofTheory` combines a material base,
that fixed rule system, and a separate initial-boundary predicate. Since the
occurrence-kind vocabulary has only three cases, an initial is admitted as a
nullary logical occurrence through the distinct `Admits.initial` constructor.

`ProofTheory.Admits` is local to one occurrence. It adds no proof-global
normality, freshness, liveness, or search condition.

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

The ambient CK type is intentionally larger than the realized image. An
arbitrary `CKTree` can contain interfaces or occurrence decorations not tied
to a particular registry. A realized tree comes from a
`CheckedDerivation P G`, and therefore from one exact presentation. P3-0
proves realization preservation under `BaseHom`; it does not yet package a
separate `RealizedComponent` or `RealizedForest` predicate.

## Proper root cutting and filling

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

P3-0 proves this for immediate-root cuts. Recursive address descent and
arbitrary-depth prefix-free multicuts are intentionally deferred.

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

## Anonymous vertical slice

`Potkin.Examples.Anonymous` supplies two material nullaries, one binary logical
occurrence, and one unary structural occurrence. It checks the raw binary and
unary candidates, demonstrates unknown versus known-empty incidence, selects
both immediate children of the binary root as one nontrivial cut, proves the
address and puncture facts, reconstructs the tree, transports it along a base
homomorphism, and proves the two root-projection results.

The fixture has no intended proof-theoretic interpretation beyond exercising
the generic declarations.
