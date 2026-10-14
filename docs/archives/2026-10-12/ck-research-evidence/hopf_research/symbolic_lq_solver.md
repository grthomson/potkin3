# Symbolic LQ certificate solver and exact-inventory separator

12 October 2026. Universal paper proofs plus independent finite executable
checks. No Lean checking and no complexity novelty claim.

## The state space

Fix a literal LQ ghost derivation `T` satisfying the local rule-shape condition.
At a subtree root let `E` be its active physical ancestor ghost owners, each
carrying its branch role and the already-seen empty-succedent bit. Roles and
bits are deterministic functions of the source path. They are not variables
that the algorithm searches over.

A symbolic colour state on `E` is a partition of `E`, with at most one forced
atom attached to each block. A conflicting pair of distinct forced atoms is
zero. Coefficients are polynomials in `N[q]`. A table is a finite linear
combination of these states. The coefficient exponent counts free equality
components already closed inside the subtree; the integer coefficient counts
physical ownership choices producing that state and exponent.

The identity state is the discrete unforced partition of `E`.

## Operations

**Join/product.** Join two partitions on the same active owners, pool forced
labels and reject clashes. Multiply their polynomial coefficients and sum
equal resulting states. This is shared-variable multiplication, not independent
tensor multiplication: both branches refer to the same exterior owners.

**Trace an owner.** Remove owner `i` from a state. If its block still has an
external member, keep that reduced block and its forced label. If the block
becomes empty, multiply by `q` exactly when it was unforced; otherwise multiply
by `1`. Sum resulting equal states.

**Ghost-leaf sums.** At `p=>`, sum states forcing each eligible left ancestor
to `p`. At `=>p`, sum states forcing each eligible right ancestor with a valid
checkpoint to `p`. At empty `=>`, sum states joining each eligible left/right
ancestor pair. The empty leaf already supplies its own checkpoint.

**Ordinary leaf.** Return the identity state with coefficient `1`.

**Ordinary inference.** Multiply its child tables by shared-variable join.

**Ghost-disjunction owner.** Evaluate both children with the new owner exposed,
using their respective roles and an initially false checkpoint bit; join their
tables, then trace the new owner. At node entry, update the empty-succedent
flags of inherited owners before introducing this node's own owner. Thus the
owner's own conclusion does not serve as a checkpoint above itself.

## Exactness theorem

**Theorem.** At every subtree, the symbolic table is exactly the sum of compact
partition summaries of all local physical owner-assignment choices, exposing
all ancestor owners and tracking every closed free component. At the closed
root its sole possible state is the empty partition, and its coefficient is

```
Rev_T(q) = sum_(consistent, route/checkpoint-correct omega) q^u(omega).
```

**Proof by structural induction.** For a ghost leaf, its ownership requirements
are exactly its finite sum of forcing/equality constraints, one summand per
physical choice. For an ordinary leaf no new constraint exists. At an ordinary
inference, child choices are independent except for their shared exterior
owner colours; joining partitions imposes precisely these shared constraints.
Distributivity enumerates each joint choice once, while a colour clash rejects
it. At a ghost owner, the children's exposed copies name one common variable.
Joining is therefore required before hiding it. Tracing removes exactly that
owner from the exterior; if its entire component has become internal and has
no forced atom, there are `q` choices for its colour. Otherwise there is no new
choice, or the colour remains exposed through the rest of the block. A closed
component cannot acquire any future constraint, because every future
attachment owner has been retained in the interface. The trace is therefore
sound and complete. This establishes the invariant at every constructor and
the closed-root formula. QED.

This is partition-diagram algebra doing actual certificate search. It does
not require a finite palette enumeration. Physical ownership choices remain
distinguished by coefficients even when they induce the same compact state.

## Three readings of the same polynomial

1. For a finite palette of size `q` containing the forced atoms, `Rev_T(q)`
   counts ownership certificates decorated by a compatible colour per owner.
2. A nonempty palette containing all forced atoms suffices for existence:
   assign each forced component its forced atom and all unforced components
   any one palette atom. Hence polynomial nonzeroness decides the certificate
   condition; unbounded searches for fresh atoms are unnecessary.
3. **Formal specialization at `q=1` counts raw ownership certificates.** Each
   valid owner assignment contributes one monomial, which becomes `1`.
   Distinct forced atom names remain distinct during clash detection. When
   more than one forced atom occurs, this is polynomial specialization—not
   interpreting distinct forced atoms in a one-element palette.

No reading counts all possible revived LJ proof terms. Different proof
assemblies can share a certificate.

## Width and algorithmic bound

Let `w` be the largest active ancestor-owner set size in `T` (including a newly
introduced owner in its children), `r` the number of distinct forced atoms,
`N` the number of ghost owners, `n` the number of all proof vertices, and `d`
the maximum inference arity. There are at most

```
S_w = Bell(w) (r+1)^w
```

partition/forced-label states on any interface. This is a deliberately loose
bound: each block has at most `r+1` label options, and the number of blocks is
at most `w`. Polynomial degree is at most `N`.

Naively joining pairs of tables takes at most `S_w^2` state pairs. Using direct
partition joins and coefficient convolution gives, for example, the conservative
bound

```
O(n (d+w^2+1) S_w^2 (w^2+(N+1)^2))
```

unit-cost arithmetic operations. Integer bit complexity is separate. This
establishes a concrete boundary-width-sensitive algorithm, not a polynomial-time
claim for unbounded width. More efficient union-find joins, canonical merging
of equal forced labels and sparse polynomial arithmetic can improve the
implementation; they are not needed for correctness.

The finite-palette table alternative from `revival_algebra.md` uses at most
`q^w` colour assignments and has a simpler `O(n(d+w^2+1)q^(w+1))` conservative
bound. The symbolic version additionally gives raw witness counts and the
whole polynomial without fixing `q`.

## A genuine weak-excluded-middle example

Let `S` be the sequent `=> not p or not not p`.

For an inner ghost-disjunction owner, use these two premises:

* Left: ghost `p=>`, ordinary negation-right to `=>not p`, then ordinary
  disjunction-right to `S`.
* Right: ghost `=>p`, ordinary negation-left to `not p=>`, negation-right to
  `=>not not p`, then disjunction-right to `S`.

Make two physical copies of this inner-owner proof, called `B` and `C`, and
use them as the left and right premises of an outer ghost owner `A`. The
result is a 17-rule-vertex actual LQ ghost derivation of weak excluded middle.

The left ghost under `B` can choose left owner `A` or `B`; its right ghost can
choose only `B`. The left ghost under `C` can choose only `C`; its right ghost
can choose `A` or `C`. Every required right path has an empty checkpoint at
negation-left. Thus there are four ownership certificates. In three, `A` is
forced to `p`; in the fourth it is unused and unforced. `B,C` are always forced
to `p`. Therefore

```
Rev_T(q) = q + 3,
Rev_T(1) = 4.
```

This example exercises genuine LQ content rather than an already LJ-provable
endsequent, and tests the convention that a ghost owner need not own a leaf.

## Exact local-rule inventory does not determine this observer

Use the 21-node proofs `T_ab` from `revival_algebra.md`, where `a,b` are each
`p` or `q`. Their common conclusion is

```
R = not p,q,not q,p or p =>.
```

Join two such proofs using ordinary disjunction-left with both principal
disjuncts equal to `(p or p)`, so the common conclusion becomes

```
not p,q,not q,(p or p) or (p or p) =>.
```

Compare the 43-node proofs

```
Good = orL(T_pp, T_qq),
Bad  = orL(T_pq, T_pq).
```

Both contain exactly two `M_p` modules and two `M_q` modules, the same ordinary
background proof copies, two identical-shape ghost owners, and the same final
ordinary rule. Therefore their multisets of complete local rule instances,
including literal conclusion and premise sequents, are equal. The physical
placement under the two owners differs. Since the final combining rule is
ordinary, it introduces no new ghost owner that could repair a mixed module's
assignment. `Good` has one certificate and `Bad` has none.

This defeats the project's previous exact-inventory factorization obstruction
for this new observer. It does not assert that ownership annotations are
identical—the point is that raw local inference inventory omits those global
relations, whose recovery and verification is the query being studied.

## Executable evidence

`check_lq_certificates.py` validates every local inference of the 21-node,
43-node and 17-node fixtures. It compares raw ownership enumeration plus graph
components with a separately written finite-palette scope recursion on those
fixtures and 2,000 additional abstract-tree/palette cases.

`check_lq_symbolic.py` implements the symbolic diagram table above and compares
its entire polynomial with raw enumeration on the fixtures and 1,481 further
abstract trees (up to seven owners in this bounded sample). It also checks that
one/two independent unused owners contribute `q`/`q^2`.

The abstract random trees are certificate-combinatorics checks, not claimed
sequent derivations. The fixtures are locally checked derivations. Neither
kind of executable evidence replaces the universal proof or Lean mechanization.

The full CK carrier is not quotiented by these tables. The tables are open
coefficients evaluated on its cut pieces. Nested-cut coherence remains the
all-cut/flag theorem of `revival_algebra.md`; equal table states need not imply
equal internal cut spectra.
