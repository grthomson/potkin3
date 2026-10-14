# LQ revival certificates as a coefficient system for the full CK comodule

12 October 2026. Paper-level mathematics; no Lean theorem is claimed. This note
develops the connectivity lemma into an exact all-cut composition theorem for
the **fixed-assignment certificate conditions** of Lang's Definition 5. The
proof of sequent-calculus revival itself remains a separate implementation
obligation. The theorem concerns certificates and their variable choices, not
the number of all possible revived proofs.

## 1. The concrete certificate model

Fix a finite literal occurrence-labelled proof tree `T` in the ghost extension
of the single-conclusion intuitionistic calculus. Its ghost rules must be just
ghost disjunction-left and the three ghost initial-sequent shapes. Let `O(T)`
be its physical ghost-disjunction owners. An assignment `omega` specifies:

* for every ghost initial `p =>`, one owner `i`, on whose left branch it lies;
* for every ghost initial `=> p`, one owner `j`, on whose right branch it lies;
* for every ghost initial `=>`, one left owner `i` and one right owner `j`.

The owners in these statements are physical ancestor occurrences, not repeated
textual rule names. An assignment is **routing-correct** if each prescribed
owner is an ancestor in the prescribed premise branch. It is
**checkpoint-correct** if each right-assigned initial occurrence has an
empty-succedent sequent on its path above its prescribed owner, using precisely
the endpoint convention of Definition 5.

The mandatory link `L_i ~ R_i` in that definition lets us represent the two
slots of owner `i` by a single variable `x_i`. Then its entire colour-consistency
condition is this finite equality network:

* a ghost `p =>` assigned to `i` adds `x_i = p`;
* a ghost `=> p` assigned to `j` adds `x_j = p`;
* a ghost `=>` assigned to `(i,j)` adds `x_i = x_j`.

Every owner contributes a variable, including owners to which no leaf was
assigned. Such an owner is an isolated, unforced component unless another
constraint reaches it. The graph's components contain at most one distinct
forced atom exactly when Lang's variable-consistency condition holds.

This is an exact reformulation of the fixed-assignment part of Definition 5,
not a conjectured analogy with it. It does not select a unique assignment for
an unannotated proof, and it does not claim uniqueness of revival.

## 2. The first new quantitative invariant

Fix a finite palette `A` containing every forced atom occurring in `T`; put
`q = |A|`, and assume `q > 0`. This is a counting parameter, not a restriction
on the original logic. If the graph for `omega` is consistent, let `u(omega)`
be its number of connected components containing no forced atom.

**Theorem 1 (exact owner-colouring count).** The number of assignments
`c : O(T) -> A` compatible with `omega` is zero when the graph is inconsistent
and otherwise `q ^ u(omega)`.

**Proof.** All vertices in one graph component have the same colour. A
component containing a forced atom has exactly one possible colour; a component
without one has exactly `q`. Components impose no further mutual condition:
different components may receive the same colour. Multiplication gives the
formula. An inconsistent component has no colour. QED.

Let `Omega(T)` be the finite set of routing-correct owner assignments. Define

```
Rev_T(q) = sum over omega in Omega(T)
              [checkpoint-correct(omega)]
              [colour-consistent(omega)] q ^ u(omega).
```

This is a polynomial with nonnegative integer coefficients. Its value at a
positive integer `q >= number of distinct forced atoms` counts pairs
`(omega, compatible owner colouring)` over a palette with those distinguished
atoms. It counts neither all formula-flow annotations nor all possible revived
proofs. A fixed palette of size `max(1, number of forced atoms)` suffices for
the decision problem: `T` has a Definition-5 certificate iff this value is
positive. There is no requirement that different unforced components receive
different variables.

This polynomial keeps physical assignment multiplicity. Quotienting proofs or
owner assignments before defining the count would change the invariant.

## 3. Why ordinary closed summaries lose the necessary information

A closed fragment may be individually consistent while two such fragments are
jointly inconsistent: one exports `x = p`, the other `x = r`, with `p != r`,
and their exterior identifies the exported owner. Existentially closing both
fragments first returns `true and true`, whereas the actual gluing is false.

Even without forced colours, a shared exported variable gives `q` choices
after identification, while closing two independent copies first gives `q^2`.
This is why the coefficient of a cut must retain its ports until the matching
remainder has consumed them. It is not an obstruction to CK: it specifies the
coefficient category in which its decomposition must be interpreted.

There is a second, subtler loss. An internally isolated unforced owner and an
empty graph induce the same Boolean summary on an empty boundary. Their counts
are respectively `q` and `1`. Thus the earlier boundary partition/forced-label
summary is sufficient for consistency, but not for assignment multiplicities.

## 4. Compact counting summaries: forced-colour partition diagrams

For a finite equality network `G` with distinguished boundary ports `B`, define
its summary to be either `0` (inconsistent) or a triple

```
S_B(G) = (pi, lambda, k).
```

Here `pi` is the partition of `B` induced by full-network connectivity;
`lambda` assigns to each block its forced colour, if it has one anywhere in
the corresponding network component; and `k` counts unforced components of
`G` disjoint from `B`. Consistent forced components disjoint from `B` need no
extra factor: each has one colouring.

For a fixed boundary colouring `b : B -> A`, the number of extensions is

```
K_G(b) = q^k  if b is constant on every block and respects lambda;
         0   otherwise.
```

**Theorem 2 (compact kernel).** This formula equals the exact number of
colourings of every interior variable extending `b`.

**Proof.** Each component meeting the boundary has its colour fixed by `b`,
provided all its boundary occurrences agree and all forced colours agree with
them. Every forced closed component has one choice. Each unforced closed
component has `q` choices. These exhaust the components. QED.

This is a genuinely compact interface: it discards interior vertices, paths,
constraint occurrences and closed forced components. It does not discard the
proof/certificate carrier itself. In particular we do **not** quotient CK
trees by equality of these summaries; different length interiors can have
equal kernels but different CK cuts.

### Vertical composition

View a network as an arrow `X -> Y`, with disjoint named copies of input and
output ports, and a summary on `X + Y`. To compose `f : X -> Y` and
`g : Y -> Z`:

1. identify only the matching physical copies of `Y`;
2. join the two partitions by equivalence closure;
3. pool forced labels in each joined block and return `0` if they conflict;
4. restrict the joined partition to `X + Z`;
5. add to `k_f + k_g` one for every newly closed, unforced joined block that
   meets only the eliminated `Y` ports.

An identity arrow pairs each input with its matching output and has no forced
colour or closed component. Horizontal composition is disjoint union, with
`k` added. Shared exterior owner names are represented by explicit diagonal
wiring, not by silently identifying independent ports in the tensor product.

**Theorem 3 (associativity and matrix semantics).** This composition is
associative and unital. Its kernel satisfies

```
K_(g o f)(x,z) = sum_(y : Y -> A) K_f(x,y) K_g(y,z).
```

**Proof of the kernel law.** A colouring of the glued network has one uniquely
determined shared colouring `y`. Conversely a compatible pair of colourings
with the same `y` glues uniquely. Distinct `y` give disjoint sets of colourings.
The boundary-components description above computes this same set by Theorem
2, including its newly closed free components. QED.

**Direct associativity proof.** Three composable diagrams define one finite
equivalence relation generated by all their component relations and both
sets of seam identifications. Both parenthesizations yield that relation on
the final boundary and the same forced labels. A globally closed unforced
component contributes exactly one factor `q`: it is counted at the first
stage when its last external port disappears. It cannot be counted earlier
while it still has a live external port, and it cannot be counted again after
being removed. The already closed components of the three inputs contribute
the same initial exponents. Conflicts persist under further joins, so zero is
absorbing in either order. Identity and disjoint-union laws follow directly.
QED.

This is the useful nearby construction: the unlabelled Boolean part is a
finite-set corelation, while retaining a factor for each closed free component
is the partition-diagram composition rule. Forced colours add a simple
constraint decoration. We use this as a coefficient category; it is not a new
general theorem about partition categories.

## 5. Checkpoints are a second compositional coefficient

For each physical right-assignment `(leaf a, owner i)`, retain a distinct token
along its unique rootward path. Let its bit mean that an empty succedent has
already occurred before the current position. A segment with an empty
succedent flag `e` transports the bit by

```
b_out = b_in OR e.
```

At the leaf, initialize using the endpoint convention of Definition 5. At the
owner, require `true`, excluding the owner conclusion if it is outside that
definition's permitted path interval. A fragment containing the token's birth
or discharge has respectively a constant-output or acceptance relation.

The full transfer description is a relation between boundary bits; for a
through-going segment it is a deterministic two-state map. Since OR is
associative, composing segments gives exactly the flag for their concatenated
path. For a completed path there is exactly one compatible internal sequence
of bits, or none if the checkpoint test fails. Thus this decoration introduces
no spurious multiplicity into Theorem 1.

Different tokens can share an owner or proof edge but are not identified: they
represent different initial occurrences and different path obligations. Their
horizontal coefficient is the product of their transition relations. Formula
occurrence identities and the actual sequents remain on the syntax carrier.

Routing is independently checked from literal ancestry and premise role before
forming this fixed-assignment coefficient system. For existential assignment
search, owner choices must also remain part of boundary states; erasing them
early would change the problem.

## 6. Canonical placement on the proof tree

The equality constraints above can be localized without changing the proof
tree or restricting its cuts. For each owner `i`, let `Support(i)` be the union
of the paths from that owner to every leaf assigned to it, together with the
owner itself. Routing correctness ensures this is a connected subtree.

At every vertex in `Support(i)`, place a physical port carrying a copy of
`x_i`. Along each support edge connect its two copies by equality. At a branch
vertex, the copies on different incident edges are explicitly equated. At a
ghost leaf, place its forced-colour or two-owner equality constraint. A support
consisting of the owner alone still contributes one variable. The checkpoint
token supports are individual paths and are localized in the same fashion.

There is a bijection between owner colourings in Section 1 and satisfying
colourings of this localized network: propagate each owner's colour along its
connected support, or read it at the owner. Checkpoint states, when they exist,
are uniquely determined. This proves that the local network computes exactly
the fixed-assignment certificate count.

When an edge is cut, its live ports are precisely the owner supports and token
paths crossing that edge. **Do not** recompute them solely from constraints
inside the current piece. A value may pass through a piece with no local
constraint mentioning it; this requires an identity wire. Existing interface
ports remain part of the piece when it is cut again.

## 7. The full-cut theorem

The underlying carrier is the existing occurrence-sensitive typed open proof
tree, refined with the above local certificate decorations. It retains every
native CK cut, including cuts that separate a leaf from its owner or a token
from its checkpoint. A piece is allowed to export obligations. It is not
required to be a closed grounded proof.

For a native cut `c`, write `P_c` for its detached positive forest and `R_c`
for its literal remainder with typed holes. Restrict the localized network to
these pieces and expose every cut-edge port. Use distinct physical copies of
ports on the two sides of each seam, joined only in the contraction. Denote
the resulting open kernels by `K(P_c)` and `K(R_c)`.

**Theorem 4 (all-cut certificate contraction).** For every cut `c`, the exact
number `Z(T,omega)` of compatible owner colourings and checkpoint states is

```
Z(T,omega)
  = contraction_c( (tensor over p in P_c of K(p)), K(R_c) ).
```

For an open source, this is an equality of kernels at its inherited outer
ports. The equality preserves physical occurrence multiplicities.

**Proof.** The cut partitions the proof vertices. All local network constraints
are retained in exactly one piece. The only removed constraints are the edge
identifications replaced by seam matching. Restricting a global satisfying
assignment gives piece assignments with equal seam values. Conversely any
such compatible family glues uniquely, because every global variable copy and
every local constraint belongs to one piece and its shared seam values agree.
Thus there is an exact bijection before counting. Summing over seam values and
multiplying independent interior choices gives the displayed formula. This is
Theorem 3 for colour constraints combined with the checkpoint relation law.
No condition of closed validity has removed a cut. QED.

### Nested cuts and coassociativity

**Theorem 5 (full cut-flag coherence).** Refining a cut in the detached pieces,
or taking the corresponding cut of its remainder, yields the same three-layer
matching packet under the native CK cut-flag bijection. Evaluating either
packet in the coefficient category gives the same kernel.

**Proof.** A two-stage cut flag assigns every positive tree vertex to one of
three ordered regions, monotonically along every root-to-leaf path. Equivalently
it specifies two nested rootward ideals. Both sides of the CK flag bijection
retain the same vertices in each region, and every original edge is either
internal to one region or connects exactly the same pair of regions. The same
owner-support and token-support incidences cross those edges. If an edge
passes through an empty middle region, the corresponding middle operation is
an identity on its full typed port state. It is not a forgotten state.

Consequently both constructions yield the same local constraints and the same
seam equalities, with only the order of gluing changed. Theorem 3 and relational
associativity for checkpoint states identify the evaluations. Equivalently,
both sums are a partition of the same finite assignment set according to two
orders of exposing its seam coordinates. QED.

At the syntax level this is the ordinary full CK/comodule cut-flag law with
additional local decorations. At the semantic level it is a representation
of that law in open partition/checkpoint diagrams. A formal scalar character
on *closed* factors is insufficient; the full boundary-valued coefficient
category is essential for these observations.

The distinction between a typed interface and the coefficient unit remains:
the positive forest coefficient may omit edge-only providers, but the state
coordinate must preserve their interface types and identity propagation.

## 8. A useful convolution consequence

Choose a finite palette and fix the physical interface types. For any
compatible two-region kernel assignments `F` and `G`, define a cut convolution
by summing their compatible contractions over **all** native cut witnesses:

```
(F star G)(T) = sum_(c in Cuts(T))
                contraction_c( F(P_c), G(R_c) ).
```

Here the notation abbreviates a family of kernels indexed by boundary types;
it is not multiplication of arbitrary rectangular matrices. On a forest, `F`
uses horizontal tensor product. Extra semiring weights on local regions are
allowed when they multiply under the same three-region decomposition.
Arbitrary cut-dependent weights are not automatically allowed: the products
attached to corresponding two-stage flags must agree (the relevant two-cocycle
identity).

Theorem 5 gives the correctly typed associative iterated convolution: either
parenthesization sums once over the same full cut flags and contracts the same
three-region data. This is the actual CK use: whole families of extraction and
reconstruction frontiers can be composed without changing certificate answers
or losing shared-owner correlations. It supports modular cached kernels and
incremental replacements at any frontier, rather than a single global check.

**Qualification.** A constant network evaluation `K` alone yields the same
global count at every frontier, so summing it over cuts merely multiplies by
the number of cuts. Nontrivial applications attach genuinely different
regional operations or costs, e.g. a library of permitted replacement-module
kernels against an exterior reconstruction kernel. The framework proves the
composition law for those choices; it does not itself prove that an arbitrary
replacement is a valid sequent inference or a sound revival operation.

The precise coefficient package is therefore:

* full literal CK/comodule carrier for extraction and cut multiplicities;
* an open diagram coefficient category for colour compatibility and counts;
* path-transition coefficients for checkpoint obligations;
* independently checked proof transformations for actual analytic revival.

No new restricted coproduct and no quotient by connectivity are needed.

## 9. Contextual replacement theorem

**Theorem 6 (D5, fixed-assignment boundary replacement).** Suppose two proof
fragments `P,Q` have the same exact sequent/interface types and externally
interpreted owner ports, the same colour kernel, and the same checkpoint
transfer relation, including all token identities and routing obligations.
Then substituting either into any matching exterior gives the same number of
compatible certificate colourings and the same fixed-assignment certificate
feasibility. Any multihole version follows by tensoring the fragment kernels.

**Proof.** By Theorem 4, exterior feasibility/count is obtained by contracting
its kernel with the substituted fragment kernel. Equal kernels have equal
contractions with every matching exterior. The same argument applies to all
frontiers in the exterior that leave the module opaque, and to corresponding
staged decompositions that retain its interface kernel. QED.

Equal kernels do not imply equal internal CK spectra: the two modules can
have different interiors and different numbers of internal cuts. This theorem
does not claim a cut-preserving bijection inside arbitrary replacements.

This theorem is stronger than matching rule inventories: it preserves remote
owner equalities and path obligations. It remains a theorem about certificate
compatibility. To convert it to a transformation of actual intuitionistic
revival proofs, one must supply the fragment's independently proved revival
and its formula-flow/weakening/contraction adapters. Equal matrices alone do
not produce a proof term or establish Cut elimination.

## 10. What to mechanize first

1. Encode fixed physical owner assignments and prove their equality-network
   condition equivalent to the colour clause of Lang's Definition 5.
2. Define summary composition and prove the compact kernel/count theorem,
   keeping the closed-unforced-component exponent.
3. Encode checkpoint path maps and prove segment composition.
4. Refine native cut restriction by crossing-port data and prove the explicit
   global-assignment/piece-assignment bijection (Theorem 4).
5. Prove cut-flag packet equality before linearizing it; instantiate the
   coefficient functor to obtain the convolution law.
6. Add a native LQ fixture and a conditional revival adapter; do not count
   colourings as distinct full proof revivals.

The construction is compatible with D4 leading, D1 revival obligations, D5
stable fragments and D3's explicit structural adapters. Copying in D2 must
freshen physical port copies while preserving intended external owner equality.
Comparisons across bases in D6 remain parameterized by their actual transport
and Cut-elimination hypotheses.

## 11. A stronger result: sum over owner assignments locally

The preceding fixed-assignment construction can be extended without globally
enumerating `Omega(T)`. The crucial fact is that once owner colours are fixed,
each ghost initial occurrence chooses its owner(s) independently. There is no
nonemptiness or coverage condition on the sets `L_i,R_i` in Definition 5.

For a ghost leaf `a`, let `Left(a)` and `Right(a)` be its ghost-disjunction
ancestors whose respective left or right premise branch contains `a`. Let
`RightOK(a)` consist of those right ancestors for which the path from `a` to
the owner, excluding the owner's conclusion, includes an empty succedent.
These are finite sets determined by the literal proof tree. For an owner
colouring `c : O(T) -> A`, define

```
f_(p =>)(c) = sum_(i in Left(a)) [c(i)=p];
f_(=> p)(c) = sum_(j in RightOK(a)) [c(j)=p];
f_(=>)(c)   = sum_(i in Left(a), j in Right(a)) [c(i)=c(j)].
```

For the empty ghost leaf its own sequent is already an empty-succedent
checkpoint, hence `RightOK(a)=Right(a)`. Its chosen left and right owners are
automatically distinct since one path cannot enter both premise branches of
the same owner.

**Theorem 7 (full certificate partition function).** Assuming the ghost-rule
shape condition, the exact polynomial evaluation from Section 2 satisfies

```
Rev_T(q) = sum_(c : O(T) -> A) product_(ghost leaves a) f_a(c).
```

**Proof.** Fix `c`. For a one-sided ghost leaf the displayed factor is precisely
the number of allowed, correctly routed owner choices with matching colour,
including its checkpoint condition in the right case. For an empty ghost leaf
the factor is precisely the number of correctly routed owner pairs with equal
colours. A family of one such choice at each ghost leaf defines the sets
`L_i,R_i` uniquely and satisfies the required exact membership conditions.
Conversely those sets uniquely recover the leaf choices. Forced-colour and
equality conditions ensure that every connected component has one colour;
conversely every certificate graph colouring satisfies precisely those local
tests. No further condition couples choices at different leaves once `c` is
fixed. Product therefore counts compatible owner assignments at fixed `c`.
Summing over `c` counts the same pairs as Theorem 1 followed by Section 2's sum
over `omega`. QED.

### Exact tree recursion

At a node carry its active ancestor-owner environment. Each entry contains its
physical ID, its colour, the branch role in which the current node lies, and
the bit recording whether an empty succedent has appeared strictly between the
owner and the current node. At entry to the node, incorporate the node's own
empty-succedent flag for inherited owners.

* An ordinary proof leaf contributes `1`.
* A ghost initial contributes the corresponding `f_a` above, read from the
  current environment.
* An ordinary inference contributes the product of its children's values in
  the inherited environment.
* At ghost disjunction owner `i`, sum over one colour `a in A`, use that same
  colour in both children, and multiply their values. Give its new entry the
  left role in one child and the right role in the other, with its checkpoint
  bit initially false. The owner's own conclusion is not a checkpoint for its
  own new entry, but was already processed for inherited entries.

**Corollary 7.1.** This recursion computes `Rev_T(q)` exactly from the literal
tree. Its evaluation is a tensor-network contraction with explicit diagonal
copying of each owner colour at branching and summation at its owning node.

**Proof.** Each ghost owner introduces its one colour variable exactly once;
diagonal propagation shares it over its descendant leaf factors. No descendant
factor depends on an owner outside its active ancestors. Repeated application
of finite distributivity therefore evaluates exactly the sum of products in
Theorem 7. Checkpoint bits are deterministic path summaries and introduce no
additional choices. QED.

This is stronger than fixed-certificate verification: it decides existence
and counts assignments and colour choices without explicitly listing all
global owner maps. It does not settle proof search for an unspecified tree.

### Boundary-width consequence

Let `g` be the maximum number of active ghost owners on a root-to-node path,
`n` the number of proof vertices, and `d` the maximum inference arity. For a
fixed finite palette, tabulating subtree values for every external owner
colouring gives an elementary bound

```
O(n (d + g^2 + 1) q^(g+1))
```

arithmetic operations. This is a conservative bound: ghost-leaf pair choices
cost at most `g^2`, while an owner step sums at most `q` shared-colour choices.
Roles and checkpoint bits are fixed by the source path; they are not additional
enumerated variables in this algorithm. Bit complexity of the growing integer
counts must be accounted for separately. This is not a polynomial-time claim
when `g` is unbounded, nor a complexity claim about finding the proof tree.

The cut interfaces provide cached conditional tables. Replacing a subtree with
another having the same table preserves the global certificate count. Partial
re-evaluation after a changed module touches only the path of its ancestors.
The all-cut/flag theorem justifies equivalent staged decompositions and reuse
at arbitrary CK frontiers.

### Extension of the coefficient category

The leaf formulas are sums of forced-colour or equality diagrams. Hence the
whole construction lives in the additive closure of the forced-colour
partition-diagram category, composed with deterministic scope/checkpoint
transport. Expanding its sums selects precisely a fixed assignment `omega`;
the earlier `q^k` rule then evaluates that summand. Thus fixed-assignment and
full certificate semantics are two presentations of the same coefficient
system, not competing carriers.

## 12. Optional checkpoint compression for fixed assignments

For feasibility under a fixed `omega`, an open subtree need not export one bit
per physical right leaf. It can export one bit per external owner: the bit is
true when **at least one** right-assigned leaf for that owner has not yet met
an empty-succedent checkpoint inside the subtree. At a branch, join these bits
by OR. An empty-succedent node clears all passing external-owner debts. At an
owner, first require its own debt to be false and remove that owner, then let
the owner's conclusion clear debts for other, external owners. This ordering
prevents counting an owner's conclusion as a checkpoint above itself.

**Theorem 8 (debt quotient).** These aggregate updates accept exactly when
every physical right token is accepted by the path semantics in Section 5.

**Proof.** Induct on subtrees. A boundary debt is true exactly when some
corresponding incoming leaf path has seen no permitted empty succedent. Union
of child sets is represented by OR. An empty node lies on every path passing
through it, so clears every such unmet requirement simultaneously. At owner
`i`, all and only its right-token paths end, and acceptance means there are no
unmet ones. Removing `i` is therefore exact. QED.

This quotient preserves feasibility, and it can be used in a deterministic
fixed-assignment tree evaluator without creating multiplicity. It is not an
identity of kernels on all independently chosen physical-token boundary bits:
several bit patterns can share the same aggregate debt. Full physical token
provenance remains on the carrier whenever occurrence-sensitive transformations
or arbitrary open-token kernels require it.

## Sources and attribution

### Finite-palette completeness

For clarity, the finite-palette claim used in Sections 2 and 11 has no hidden
freshness assumption. Let `A` be any nonempty finite set of atoms containing
every atom forced at a one-sided ghost initial sequent. Every consistent
certificate graph has an `A`-colouring: assign its forced colour to each forced
component, and choose one fixed `a0 in A` for **all** unforced components.
Conversely an `A`-colouring witnesses consistency. Thus changing the palette
changes the number of colour-decorated certificates, but not the existence of
a Definition-5 certificate. If there are no forced atoms, a singleton palette
suffices. This is an exact existence theorem, not a finite-agreement heuristic.

### A literal LQ coordinated-replacement fixture

Let `p != q`, `S = p,not p,q,not q =>`, and
`R = not p,q,not q,p or p =>`. Define `M_p` by the ghost initial `=>p`, followed
by ordinary negation-left to obtain `not p=>`, followed by three one-formula
left weakenings to obtain `S`. Define `M_q` symmetrically. Both have five rule
vertices and the exact same root sequent.

Use ordinary disjunction-left, with principal disjuncts both `p` and background
`not p,q,not q`, to combine two module conclusions `S,S` into `R`. Put this
ordinary subtree in the right premise of a single ghost-disjunction owner `x`.
For its left premise, use an ordinary LJ proof of `R`: each `S` premise follows
from identity `p=>p`, negation-left and two weakenings; disjunction-left joins
the two four-node proofs into a nine-node proof of `R`.

The complete tree has 21 rule vertices. Each of its two ghost initials can be
assigned only to the right side of `x`, and each passes an empty succedent at
its negation-left conclusion. Thus two `M_p` modules force `x=p`, two `M_q`
modules force `x=q`, and either mixed pair is inconsistent. This holds even
after existentially quantifying over owner assignments: there is only one
eligible owner. It is a certificate distinction on real local inference
instances, not a claim that `R` is unprovable; `R` is already LJ-provable.

Replacing both `M_q` modules simultaneously with the same-interface `M_p`
modules succeeds, while either single replacement fails. Both selected roots
form one legal CK antichain. The exact remaining rule count is `21-10=11`.
This is the source-specific realization of the joint-replacement interaction
used in the accompanying Hopf cache-convolution example.

### Executable checks

`check_lq_certificates.py` checks every local rule in all four versions of the
21-node fixture, compares a raw enumeration of owner assignments followed by
component counting with an independent scoped colour recursion, and tests
2,000 further abstract tree/palette cases. The fixture values are respectively
`1,0,0,1` for `pp,pq,qp,qq`. The abstract trees test the certificate combinatorics
only; they are not claimed to be sequent derivations. Results are saved in
`lq_certificate_results.json`. These checks are supplementary evidence for the
universal paper proofs, not a replacement for them or for Lean checking.

* Timo Lang, *Some Analytic Systems of Rules* (2023), Definition 5 and Theorem
  12, pp. 108–109. https://discovery.ucl.ac.uk/id/eprint/10182303/1/tableauxRep.pdf
  The source supplies the LQ certificate and revival sketch; it does not claim
  the CK coefficient construction in this note.
* Brandon Coya and Brendan Fong, *Corelations are the prop for extraspecial
  commutative Frobenius monoids* (2017).
  https://www.tac.mta.ca/tac/volumes/32/11/32-11abs.html
  This identifies the standard partition/corelation part of the interface.
* Tom Halverson and Arun Ram, *Partition Algebras*.
  https://arxiv.org/abs/math/0401314
  Closed-component weighting is existing diagram-algebra mathematics; our
  proposed contribution is its exact placement inside this proof/certificate
  decomposition programme, not invention of that weighting rule.

All displayed universal claims above have paper proofs. They are not
kernel-checked. Native proof syntax, formula flow, and complete revival have
not been implemented by this note.
