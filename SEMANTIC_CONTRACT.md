# P3-1 semantic contract

This contract distinguishes what P3-1 implements from conventions fixed now
for later milestones. A convention marked **deferred** is not a theorem or API
claim about the current source.

## Boundaries and equality

- Formula contexts and displayed hypersequent components are finite
  multisets. Exchange is therefore canonical and multiplicity is retained.
- Every CK boundary is a nonempty whole hypersequent. A premise slot never
  denotes merely one displayed component.
- Premise order is the order of the occurrence's premise list. Equal premise
  boundaries at different slots remain distinct positions.
- Current equality is structural presentation equality. There are no proof
  quotients, commuting conversions, implicit Weakening, Contraction, Mix,
  assembly, or Gentzen Cut.

## Occurrences, incidence, and admission

- A local occurrence is already fully instantiated. Its ID, kind, ordered
  premise boundaries, conclusion boundary, instance data, and optional
  incidence travel together.
- Supplied incidence carries explicit local occurrence profiles. Each profile
  is an ordered display list proved to enumerate the exact component
  multiset, so equal displayed components retain distinct local slots.
- Incidence edges are oriented from `(premise slot, premise component slot)`
  to a conclusion component slot. Slots are local and zero-based in Lean;
  dependent finite types validate them against the supplied exact profiles.
- `incidence = none` means unavailable or unknown. `incidence = some {}` means
  a supplied, known-empty relation. Neither is inferred from an occurrence
  ID, kind, name, tag, arity, or rule predicate.
- Component incidence alone says nothing about formula copying or erasure.
- A material base is an arbitrary family of evidence for whole boundaries.
  No structural or substitution principle follows from that family.
- The current `ProofTheory.Admits.material` constructor is narrower than both
  manuscript v56 and Racket: it additionally requires a nullary occurrence.
  P3-1 proves heredity for this exact current carrier and does not silently
  claim positive-arity material admission.
- A finite equipped presentation is one immutable registry value with unique
  IDs and local admission evidence. Lookup is by exact ID. A `BaseHom`
  preserves evidence; it is not deletion, invalidation, revision, or a cast
  between unrelated presentations.

## Raw, checked, ambient, and realized terms

- Raw candidates and checked derivations are different types. Raw nodes carry
  only IDs and ordered children; raw punctures are anonymous. Their typed
  requirements arise only from retained checked parents.
- The complete checker rejects raw punctures and constructs a result only
  after registry lookup, exact arity checking, and ordered whole-boundary
  checking at every node.
- `CheckedDerivation P G` records exact presentation provenance in its type.
  `CKTree sigma InstanceData G` does not: it is the ambient open carrier.
- `OpenTree Boundary Decoration` is generic in its boundary type;
  `CKTree.Bare` instantiates that combinatorics with whole hypersequents and
  unit decoration.
- An ambient CK interface is a typed vacancy, not an ordinary vertex. An
  ordinary node is positive and retains its full occurrence decoration.
- `LocallyAdmittedTree P t` is the explicit realised open sector judgement.
  Interfaces are admitted typed vacancies. Every ordinary vertex must occur
  in the exact immutable registry `P`, and its exact ordered children must be
  recursively locally admitted.
- A `RealizedOpenComponent P` has a locally admitted tree and a positive
  ordinary root. It may contain old interfaces. A bare interface is valid as
  an open context but is not a connected realised component.
- A complete checked derivation realizes into this sector. The sector is not
  defined as the range of complete realization, so open terms with no complete
  filling fibre are not excluded artificially.
- `CKTree.erase` deliberately forgets occurrence decorations while retaining
  whole boundaries and ordered branching. Equality after erasure never proves
  equality of rich checked derivations or common presentation provenance.
- `CheckedDerivation.node` and the checked-child constructors are private to
  `Checked.lean`. `check` and the exact-root `checkAt` wrapper are the public
  certification route; the fixture extracts only proved-successful results.

## Addresses and orientation

- Lean internal addresses are lists of zero-based child slots. They are read
  from the root downward. `[]` denotes the root.
- Racket and user-facing addresses are lists of positive one-based premise
  slots. Conversion is pointwise successor; inverse conversion is pointwise
  predecessor on a `RacketAddress` carrying positivity evidence.
- `RacketAddress.toInternal_toRacket` proves that zero-based address conversion
  round-trips exactly.
- `RacketAddress.toRacket_toInternal` proves the converse for every valid
  positive address. Positivity is essential: zero has no Racket premise-slot
  meaning.
- Prefix order follows root-to-leaf path extension: `a` prefixes `b` exactly
  when `b = a ++ tail`.
- `InternalAddress.toRacket_prefix_iff` preserves and reflects prefixing.
  For every recursive site, `selectedRacketAddress_toInternal` recovers the
  exact internal address and `selectedRacketAddress_exists` locates the same
  ordinary source vertex; the corresponding remainder-address theorem locates
  the cut-created interface.
- A P3-0 `RootCut` remains one nonempty finite selection of ordinary immediate
  child roots. Its addresses are singleton lists, hence nonroot. Distinct
  selected slots yield prefix-incomparable addresses.
- A P3-1 `CKCut t` is a recursive finite cut of a positive ordinary source.
  Each ordered child independently chooses whole-root detachment or recursive
  strict descent. An interface has only the empty descent. The current root
  has no detach constructor.
- Consequently every site is an existing nonroot ordinary vertex, and two
  different sites are prefix-incomparable by construction. A detach choice
  suppresses every choice below it.
- The all-descend plan is the unique empty cut. `ProperCKCut t` is the
  nonempty subtype. Neither type admits the root address; the future
  whole-tree algebraic endpoint remains separate data.
- Recursive sum site identities are walked in ordered premise order. Their
  internal addresses are lexicographically increasing. Pointwise successor
  carries that exact order and prefixing to positive one-based addresses.
- `CKTree.VertexAt` certifies address existence only for ordinary vertices;
  it has no constructor that turns an interface into a vertex.

## Detachment, punctures, and filling

- The direction of a cut edge is from a retained parent premise slot down to
  the detached child root. Detachment leaves a typed interface at that exact
  slot and retains the original positive parent occurrence.
- `RootCut.Site` is the occurrence identity of a selected slot. The dependent
  function `RootCut.detached` is the address-aligned tuple; its result type is
  exactly the site's premise boundary.
- A puncture is the selected typed input position represented by an interface.
  It is not an ordinary vertex, not a detached factor, and not an algebra
  generator.
- `RootCut.requirement site` is literally the whole premise boundary at that
  site. `puncture_matches_detached` packages both the retained interface and
  the address-aligned detached root at exactly that boundary.
- Filling is oriented from the retained open component plus a site-indexed
  filler family back to the original output boundary. Only selected sites are
  replaced. Unselected children and the parent decoration are retained.
- `fill_detached_reconstructs` is exact structural equality. It is not proof
  reduction, normalization, Cut elimination, reconstruction from a
  commutative forest, or an existence claim based on proof search.
- For `CKCut`, `detachedTuple` records an address, exact root boundary,
  decorated tree, and ordinary-root proof for every recursive site. The tuple
  remains primary; `detachedForest` is only its commutative projection.
- `CKCut.requirement site` is the exact whole boundary of that recursive site.
  `selectedPuncture_matches_detachedRoot` proves both that the remainder has an
  interface at its address and that this requirement equals the aligned
  detached tree's root boundary.
- `CKCut.remainder` replaces precisely each selected ordinary subtree by an
  interface of the same whole boundary. Its type therefore preserves the
  exact source root boundary.
- New and old interfaces are distinguished by provenance, not merely by
  boundary equality. `CKAddressStatus` gives a total computational lookup.
  The exact new-hole law is:

  ```text
  status(source, q) = ordinary
    and status(remainder, q) = interface
      iff q is the address of one selected site.
  ```

  The selected site is unique. An old interface inside a detached region
  travels with the detached open factor; every old source interface for which
  no selected address is a prefix remains an interface at its old address.
  This is proved separately so neither direction conflates old provenance
  with a cut-created site.
- Distinguished filling is indexed only by the cut's new site type. It cannot
  fill an unrelated old interface. Filling with the aligned detached family
  reconstructs the exact source presentation.

## Ordered tuples and commutative forests

- Ordered premises and cut-site identities are retained until detachment is
  complete. `RootCut.detached` is indexed by the selected slot subtype.
- `CKCut.Site` is an intrinsic recursive occurrence identity. `orderedSites`
  lists every identity once in lexicographic address order, and
  `detachedTuple` keeps that address next to its exact dependent tree.
- `detachedForest` is a later projection to the positive `CKForest` multiset.
  It forgets site order but preserves one ordinary-root factor occurrence per
  selected slot, including multiplicity for structurally equal trees.
- A `CKForest` is independent commutative juxtaposition of connected factors.
  It does not fill interfaces, assemble a connected proof, or identify a
  connected proof of `S | T` with separate proofs of `S` and `T`.
- Reconstruction always consumes the aligned detached family, never the
  commutative forest image.

## Recursive enumeration

- Enumeration follows the unique child-branch decomposition, never powerset
  filtering over vertex addresses.
- At an ordinary child the canonical branch order is: empty descent, whole
  child-root detachment, then nonempty recursive descents. An interface has
  only empty descent.
- Ordered children combine by Cartesian product with earlier premise slots
  varying fastest. The empty plan is therefore generated exactly once.
- Constructor recursion proves every generated plan sound, every intrinsic
  finite prefix-free nonroot cut present, and the generated witness list
  duplicate-free before projecting to forests or collected results.
- Independently, `ValidAddressCut` stores a finite set of existing nonroot
  vertices with pairwise prefix-incomparability and a positive source.
  Recursive first-slot decomposition constructs a `CKCut` with exactly that
  address finset, proving external finite-antichain completeness without
  defining validity as existence of an intrinsic witness.
- Validation canonicalizes request order lexicographically, as the Racket
  reference does. Sorting does not erase duplicates, so repeated requests
  remain invalid.
- The running four-vertex source generates five `CKCut` objects—one empty and
  four proper—not an inflated assertion-count oracle.

- Structural `CKCut` enumeration is proved duplicate-free. A stronger theorem
  that equal address finsets force equality of dependently transported
  `CKCutPlan` presentations is not yet proved; therefore no mapped-address-list
  Nodup theorem or full intrinsic/extensional equivalence is claimed.

## Cut heredity and base transport

- If the source is locally admitted by an exact presentation, every selected
  detached subtree is locally admitted by that same presentation. The retained
  remainder is locally admitted as well because detachment only replaces an
  admitted child by a typed vacancy.
- Detached factors may themselves contain old interfaces. Heredity is not a
  completeness or fillability assertion.
- These results rely on admission being local to each finite registered
  occurrence and its exact ordered boundaries. They do not generalise to
  calculi with proof-global admission conditions.
- `BaseHom` maps only the local admission evidence. Registry occurrences and
  the ambient CK presentation remain literally unchanged. Consequently
  subtree selection, the remainder, addressed detached tuple, distinguished
  reconstruction, and their realised-sector packages commute with base
  transport without a cast of occurrence provenance.

## Root projections

- `blockRoots` keeps one whole hypersequent for each connected forest factor.
- `flattenedRoots` is `none` on the empty forest. On a nonempty forest it
  forgets block boundaries and returns a nonempty whole hypersequent
  containing all displayed sequent occurrences.
- The connected `S | T` component and the forest of separate `S` and `T`
  components have equal flattened roots but unequal block roots. The
  inequality follows already from factor cardinality, independently of rule
  names or formula content.

## Reserved algebraic conventions — deferred

P3-1 defines neither a formal-sum carrier nor a coproduct. The following
orientation is fixed to prevent later API drift:

- A cut witness contributes `detached forest tensor retained component`.
- Tensor coordinates are ordered. Commutativity inside either forest
  coordinate must never identify `F tensor G` with `G tensor F`.
- The empty cut, when introduced, contributes `1 tensor t` exactly once.
- The algebraic whole-tree endpoint is `t tensor 1`, added separately exactly
  once. It is not represented by a root cut.
- Root cuts remain invalid. The nodeless typed identity context, an interface,
  the empty forest unit, and formal additive zero are distinct objects.
- Collected coefficients may forget address alignment; an occurrence-level
  witness API must continue to retain it.
- Forest multiplication will mean independent commutative juxtaposition only,
  never filling, assembly, Mix, reconstruction, or Gentzen Cut.

No endpoint, tensor, coefficient, counit, coproduct, or antipode theorem is
claimed in P3-1.

## Vertex degree

`CKTree.degree` is the number of ordinary vertices:

- an interface contributes zero;
- an ordinary node contributes one plus the degrees of its ordered children;
- a typed nodeless context is outside the positive rooted CK carrier and must
  not be assigned a carrier degree merely for convenience.

For every `CKCut`, constructor recursion proves

```text
degree(source)
  = degree(remainder) + sum(site in canonical order, degree(detached(site))).
```

The ordered sum counts each occurrence separately, including equal detached
trees at distinct addresses. P3-1 does not infer a connected grading or an
antipode from this arithmetic theorem.

## Explicitly deferred

The following are outside P3-1: empty-cut and whole-tree coproduct endpoints;
formal sums and tensors; coefficient
collection; counit, coassociativity, grading, and antipode; concrete featured
calculi; Sandqvist IPL; constructor deletion and compatible revisions;
historical liveness and repair; protected defects; recurrence and cyclic
frames; focusing and proof search; GL, Oudom, and pre-Lie constructions;
normalization, Cut elimination, and proof quotients.
