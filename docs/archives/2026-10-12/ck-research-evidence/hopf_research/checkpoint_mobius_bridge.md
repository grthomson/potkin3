# Checkpoint interfaces as a Boolean-lattice zeta/Möbius coordinate change

12 October 2026. Paper proof with a two-owner executable check. This is a
coefficient-interface identity; its Möbius inversion is not the CK antipode.

## 1. The two counting functions

Fix a literal open source fragment T, its ordered external owner scope, the
LEFT/RIGHT role of every imported owner, and concrete external owner colours.
Fix a nonempty finite palette containing those colours and all forced atoms.
Let R be the finite set of external RIGHT owner positions.

Let Omega be the finite set of colour-decorated routing certificates inside
T satisfying all colour constraints and all checkpoints for internal owners.
Do not yet impose checkpoints for the external owners. For omega in Omega,
its deterministic bottom-up annotation defines a subset d(omega) of R:
precisely the external owners with a pending descendant right token after
processing T's root sequent.

Define the exact-debt interface

    G(d) = #{omega in Omega : d(omega)=d}.

For any formal subset s of R, evaluate the top-down checker with initial
external `seen` flags equal to s, interpreted as checkpoints strictly before
the current root sequent. Define

    F(s) = #{omega in Omega accepted with these initial seen flags}.

Internal owner bits are introduced false at their actual owner nodes in the
top-down checker. The source root sequent is processed by that checker on
entry. Bottom-up debt already includes the same root's processing. This
endpoint convention is essential.

## 2. Exact invertible transformation

**Theorem.** For every subset s of R,

    F(s) = sum_{d subseteq s} G(d).                              (1)

Conversely, over the integers or any abelian coefficient group,

    G(d) = sum_{s subseteq d} (-1)^{|d\s|} F(s).                (2)

**Proof of (1).** Fix omega. An external owner's descendant leaves have either
all found checkpoints inside T, in which case the owner is absent from its
debt, or at least one has not, in which case precisely those pending paths
require a checkpoint on the ancestor side. All leaves for that owner have
the same external path segment. Thus its external obligation is accepted
exactly when membership in d(omega) implies membership in s. Internal
obligations are already discharged in Omega. Hence omega is accepted exactly
when d(omega) is a subset of s. Partition Omega by its unique debt set. QED.

**Proof of (2).** Substitute (1) into its right side and interchange the finite
sums. The coefficient of G(e), for e subseteq d, becomes

    sum_{e subseteq s subseteq d} (-1)^{|d\s|},

which is 1 if e=d and 0 otherwise, by the binomial identity
(1-1)^{|d\e|}. Thus only G(d) remains. QED.

So top-down checkpoint acceptance and bottom-up exact debt are invertible
counting coordinates on the full Boolean interface. Their individual bits
have different meanings; no equality of bits is asserted.

### Formal states versus physically realised ancestors

The formulas use F(s) for **all** subsets s. A concrete ancestor chain may
realise only some flag patterns: a checkpoint after a younger owner also lies
after certain older owners, constraining its possible seen flags. We can
still evaluate the checker at every formal Boolean state and obtain the
coordinate change above. Values only on physically realised flags need not
determine every G(d). In particular one must not claim that arbitrary native
context observations alone provide the full inverse transform.

An empty source root clears every pending debt, so G(d)=0 for nonempty d and
F is constant. Both formulas correctly recover this degenerate case.

## 3. Symbolic and partition-diagram coefficients

The argument is additive and works entrywise in any abelian group. Instead of
fixing concrete external colours, let each routing choice contribute its
forced-colour partition diagram on external owner ports, weighted by q for
each hidden unforced component. Keep only internally checkpoint-valid choices
and classify each diagram by its deterministic external debt d. Then G(d)
is an element of the diagram coefficient module over Z[q], and the same
identities (1)--(2) hold in that module. They therefore hold after any valid
boundary-colour evaluation or closed-component trace.

This does not equate the Boolean-lattice incidence algebra with the CK Hopf
algebra. Boolean Möbius inversion changes coordinates of a local interface;
the CK antipode inverts full-cut convolution on proof forests. They operate
at distinct levels and can be used together without being conflated.

### Branching multiplication is also transported exactly

For two fragment interfaces on the same external RIGHT-owner set, their
nonempty-succedent ordinary combination joins pending obligations by union.
Before any owner is hidden, let coefficient multiplication be the matching
boundary-colour product (or the forced-partition join product). Define

    (G unionstar H)(d) = sum_{a union b = d} G(a) H(b).

Writing Z for (1), finite distributivity gives

    Z(G unionstar H)(s) = Z(G)(s) Z(H)(s).                       (3)

Indeed, a union b subseteq s holds exactly when both a and b are subsets of
s. Thus Boolean zeta is an algebra isomorphism from union-convolution debt
tables to pointwise-multiplied acceptance tables, with Möbius inverse over
the integer coefficient algebra. It is not an isomorphism if one silently
uses the same pointwise product on both coordinate systems.

An empty source conclusion then sends every debt to the empty set. In seen
coordinates the resulting table is constant, equal to the pre-clearing
table evaluated at s=R. This gives an exact match between bottom-up union and
clear, and top-down acceptance multiplication and forced-all-seen behaviour.

## 4. A literal two-owner test

Take two external RIGHT owners a,b of colour p. Let T be the ordinary
conjunction-right inference with two ghost initials =>p, concluding
=>p and p (i.e. =>(p conjunction p)). There is no empty-succedent source node.
Each physical ghost leaf independently chooses a or b, giving the four
certificate assignments aa,ab,ba,bb. Thus

| subset | G: exact debt | F: inherited seen acceptance |
|---|---:|---:|
| empty | 0 | 0 |
| {a} | 1 | 1 |
| {b} | 1 | 1 |
| {a,b} | 2 | 4 |

The mixed assignments are different physical certificates, so the last G
coefficient is 2. Möbius inversion gives 4-1-1+0=2. If the two leaves were
incorrectly identified merely because their formulas match, this multiplicity
would be lost. Depending on the physical ordering of a,b, one of the singleton
seen states can be only a formal interface state; the transform intentionally
includes it as explained above.

## 5. Useful consequences

* A cached acceptance table F can be converted exactly to the compiler's
  debt table G, and conversely, provided its full formal Boolean domain is
  available. No proof-tree cuts are re-enumerated for this conversion.
* Feasibility in external state s is equivalent to the existence of a
  supported debt d subseteq s. Minimal supported debt sets give minimal
  checkpoint requirements among this fragment's available certificates.
* Every exact counting interface has nonnegative Möbius coefficients G(d).
  A negative coefficient obtained from an alleged F table demonstrates that
  the table is inconsistent with this exact-debt certificate model. Mere
  monotonicity of F is weaker than this test.
* The conversion commutes with sums of cached alternatives and turns
  ordinary-branch union convolution into pointwise multiplication by (3).
  It can be applied to partition-diagram-valued interfaces before choosing
  concrete colours. The multiplication must be transformed along with the
  table; arbitrary products are not automatically preserved.

This supplies a precise mathematical connection between the earlier
top-down certificate search and the new compiler-aligned polynomial grammar,
while preserving the direction and meaning of each checkpoint state.

## 6. A concrete interface-combination algorithm

With r external RIGHT owners, direct union-convolution enumerates 4^r ordered
pairs of subsets. Instead perform two Boolean zeta transforms, multiply their
2^r entries pointwise, and apply one Boolean Mobius inverse. A transform adds
the entry at s without bit i into the entry at s with bit i, for each bit i
and each containing subset s. The inverse performs the corresponding
subtractions. Each pass uses r*2^(r-1) coefficient operations.

Equation (3) proves the result is exactly the union convolution. The total is
O(r*2^r) coefficient-ring operations and O(2^r) table entries. This is the
standard fast subset-transform algorithm instantiated on these certificate
interfaces, not a new general transform algorithm. Partition/polynomial
coefficient operation costs and construction of input tables remain separate.
All formal Boolean states are required; observing only physically realizable
ancestor flags is insufficient. The inverse needs subtraction, so this bound
is not a claim about arbitrary subtraction-free semirings. No whole-proof
polynomial-time or measured runtime claim follows from this local bound.
