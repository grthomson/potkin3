# P3-0 semantic contract

This contract distinguishes what P3-0 implements from conventions fixed now
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
- A realized CK tree is the structural image of a complete checked derivation.
  It has an ordinary root and no interfaces. The current code proves this
  pointwise but does not yet define a global realized-sector predicate for
  arbitrary forests.
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
- A P3-0 `RootCut` is one nonempty finite selection of ordinary immediate
  child roots. Its addresses are singleton lists, hence nonroot. Distinct
  selected slots yield prefix-incomparable addresses.
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

## Ordered tuples and commutative forests

- Ordered premises and cut-site identities are retained until detachment is
  complete. `RootCut.detached` is indexed by the selected slot subtype.
- `detachedForest` is a later projection to the positive `CKForest` multiset.
  It forgets site order but preserves one ordinary-root factor occurrence per
  selected slot, including multiplicity for structurally equal trees.
- A `CKForest` is independent commutative juxtaposition of connected factors.
  It does not fill interfaces, assemble a connected proof, or identify a
  connected proof of `S | T` with separate proofs of `S` and `T`.
- Reconstruction always consumes the aligned detached family, never the
  commutative forest image.

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

P3-0 defines neither a formal-sum carrier nor a coproduct. The following
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
claimed in P3-0.

## Reserved degree convention — deferred

When grading is added, degree is the number of ordinary vertices:

- an interface contributes zero;
- an ordinary node contributes one plus the degrees of its ordered children;
- a forest degree is the sum over every factor occurrence, with multiplicity;
- the empty forest unit has degree zero;
- a typed nodeless context is outside the positive rooted CK carrier and must
  not be assigned a carrier degree merely for convenience.

P3-0 has no `degree` declaration and proves no connected-graded or antipode
result.

## Explicitly deferred

The following are outside P3-0: arbitrary-depth recursive cuts; empty-cut and
whole-tree coproduct endpoints; formal sums and tensors; coefficient
collection; counit, coassociativity, grading, and antipode; concrete featured
calculi; Sandqvist IPL; constructor deletion and compatible revisions;
historical liveness and repair; protected defects; recurrence and cyclic
frames; focusing and proof search; GL, Oudom, and pre-Lie constructions;
normalization, Cut elimination, and proof quotients.
