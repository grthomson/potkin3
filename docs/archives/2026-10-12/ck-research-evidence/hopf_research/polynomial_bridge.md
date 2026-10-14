# Local certificate grammars, typed P-trees, and the CK/Faà di Bruno bridge

12 October 2026. New paper-level development for POTKIN3. None of the results
below is claimed to be Lean checked. The certificate input is Lang's Definition
5, as transcribed and independently analysed in `revival_algebra.md`. The
polynomial-tree machinery is established mathematics; its exact application
to the scoped LQ certificate grammar and its relation to our typed CK state
space are the constructions developed here.

## 1. An exact local grammar for a global certificate condition

Fix a nonempty finite palette A containing the atoms that can occur at the
one-sided ghost initial sequents under consideration. Keep literal formula
occurrences, actual sequent rule instances, and ordered premise slots. No
quotient by rule inventory, boundary equivalence, or formula erasure is taken.
The construction is a family P_A as A varies. A symbolic q-colouring count is
obtained from the equality/partition semantics, not by pretending the concrete
state set I_A is unchanged when the palette changes.

The top-down `seen` checkpoint bit used below is different from a revival
compiler's bottom-up `pending debt` bit for right tokens originating inside a
fragment. They must not be identified. One may retain the latter separately
in the coefficient/compiler interface, or refine the polynomial states by
debt bits and the deterministic local OR/empty-node/owner-discharge laws. For
a fully decorated valid source their bottom-up annotation is unique, so this
refinement introduces no new certificate multiplicities.

A **state** i is a pair (S,E), where S is a literal sequent and E is a finite
stack of active ancestor ghost-disjunction owners. Each stack entry contains:

* one colour in A;
* a role L or R, indicating which premise of that owner contains the current
  position;
* one bit recording whether an empty-succedent sequent occurred strictly
  between the owner's conclusion and the current sequent.

Stack positions, equivalently de Bruijn indices counted from the most recent
owner, identify external owners. They are not global textual names. At a node
with conclusion S, first OR its empty-succedent indicator into the bits of
all inherited stack entries. Call this updated stack E^S.

The following are local operations, with their output state and finite list
of input states specified as part of the operation label.

1. An ordinary inference instance with conclusion S and ordered premises
   S_1,...,S_m has output (S,E) and inputs (S_k,E^S). Ordinary initial rules
   are the nullary case. Distinct actual inference instances remain distinct.
2. A ghost-disjunction owner with conclusion S chooses one colour a in A.
   Its two inputs have the corresponding literal premise sequents and stacks
   E^S extended respectively by (a,L,false) and (a,R,false). The same chosen
   a occurs in both input types. The owner's conclusion is deliberately not
   counted as a checkpoint for its own newly introduced entry.
3. A ghost initial p=> has one nullary operation for each L entry of E^S with
   colour p. Its operation label records the selected stack index.
4. A ghost initial =>p has one nullary operation for each R entry of E^S with
   colour p and checkpoint bit true. Its label records the selected index.
5. A ghost initial => has one nullary operation for every selected pair
   consisting of an L entry and an R entry with equal colours. Its own empty
   succedent supplies the right checkpoint. Both selected indices are kept.

Every nullary ghost choice is a separate constructor. Thus two eligible
owners of the same colour still give two different certificates. An unused
owner still chooses its colour at its owner constructor. These two details
preserve precisely the multiplicities in the earlier certificate polynomial.

### Local/global theorem

For a literal ghost proof T with an empty external-owner stack, there is a
bijection between:

* Definition-5 certificates on T together with a compatible A-colouring of
  each physical ghost-disjunction owner; and
* locally typed rule trees over the above grammar, with underlying literal
  tree T, empty-stack root state, and no open input edges.

**Proof.** Given the certificate and colouring, traverse T from conclusion to
premises. Maintain the active ancestor stack. At each owner, insert its chosen
colour and the premise's correct role. Bits are uniquely determined by the
sequent path. At a ghost leaf, its certificate membership picks the unique
corresponding stack entry or pair. Routing ensures the entry is present with
the required role, equality consistency ensures the colour tests, and the
right checkpoint clause ensures the bit test. This determines every local
operation label and every edge state uniquely.

Conversely, reconstruct physical owners by their addresses in the underlying
tree. A selected de Bruijn position at a ghost leaf designates one actual
ancestor owner. Collect these choices into L_i,R_i. The grammar enforces exact
membership multiplicity, left/right routing, forced-atom equality, equality
at empty ghost leaves, and the permitted checkpoint interval. Each owner has
one colour shared by both branches. Hence the connected-component colour
condition holds. The two constructions undo one another, because all stack
and bit propagation was deterministic. QED.

This theorem is about certificates and their owner colours. It does not
identify certificates with distinct revived LJ proofs. The constructive
revival transformation, including structural adapters, remains a separate
theorem. An empty-stack root and absence of open input edges are the acceptance
condition for a closed certificate; arbitrary states are needed for fragments.

## 2. The polynomial is explicit

Let I be the set of states; B the set of permitted local operations just
defined; E the set of pairs (b,k) with k a physical premise slot of b. Write
t(b) for the output state and s(b,k) for the input state. Then

    I <-s- E -p-> B -t-> I

is a finitary polynomial: every operation has finitely many premise slots,
although I and B need not be finite. Its endofunctor on I-indexed sets is

    P(X)_i = sum_{b : t(b)=i} product_{k in premises(b)} X_{s(b,k)}.

The least solution of T_i = 1_i + P(T)_i consists of its finite **open** rule
trees. The summand 1_i is the zero-node edge e_i of state i. It represents an
open proof obligation, not an ordinary axiom and not an accepted closed proof.
The nullary ordinary/ghost rules are positive one-node trees with no input
edges. Confusing those with e_i would erase the distinction between proving
an obligation and leaving it unproved.

This is an exact P-tree presentation, not an analogy based on tree shape.
Premise-slot bijections are specified by the literal inference instance;
matching an edge requires its entire sequent, owner stack, colour, role, and
checkpoint state. Internal binders use new stack entries, so substitution does
not require reusing global owner names. External stack positions retain their
meaning relative to the enclosing context.

Open trees compose by replacing any physical input edge with a tree having
exactly that output state. The local/global theorem extends to this operation:
local typing at the seam guarantees that its owner and checkpoint interface
is the inherited one. No global certificate test is needed after grafting a
fully decorated locally typed fragment, although existentially summing over
decorations still requires joint matching of their states.

## 3. The full operadic cut bialgebra

Let B_P be the free commutative algebra on isomorphism classes of P-trees.
Because premise slots are fixed and ordered, trees have no nontrivial slot
permuting automorphisms. Physical cut multiplicities are nevertheless retained:
distinct cuts that produce the same algebraic monomial are added.

For each tree T, define

    Delta_B(T) = sum_{c} P_c tensor R_c.

Here R_c is a root-containing operadic subtree, including the possibility of
the zero-node root edge, and P_c is the forest attached to its exposed input
edges. Cutting duplicates the seam edge into a root edge of the crown and an
input edge of the remainder, retaining its complete state. It does not delete
that state. Original open leaves produce trivial crown edges when reached.

There is a direct bijection between cuts and lower/rootward node ideals,
equivalently positive-vertex extraction antichains. Once retained positive
nodes are selected, the operadic edges required by their arities are forced.
There is no extra binary choice at an already open external input edge.

Cut flags correspond to three-layer decompositions with identical matched
states. This proves coassociativity. Disjoint union of forests gives
multiplicativity. The counit is 1 on every forest of zero-node edges and 0 on
forests containing a positive node. In particular,

    Delta_B(e_i) = e_i tensor e_i,     epsilon(e_i)=1.

The e_i are distinct group-like generators. Therefore B_P is not connected
and is not itself the connected CK Hopf algebra. This feature is useful:
its boundary types are the data needed for typed substitution and the Green
function identities below.

## 4. A connected Hopf algebra AND a typed state space, canonically

Let J be the ideal generated by e_i-1 for all states i. It is a homogeneous
biideal for positive-node grading, since

    Delta_B(e_i-1)
      = e_i tensor (e_i-1) + (e_i-1) tensor 1,
    epsilon(e_i-1)=0.

Consequently H = B_P/J is a bialgebra, with quotient map q. As an algebra it
is free commutative on the **positive** P-trees. Its degree-zero part is the
ground ring, and node grading is nonnegative. The standard connected graded
bialgebra recursion supplies its antipode over any commutative ground ring:

    S(h) = -h - sum S(h') h''

for the reduced coproduct of a positive homogeneous h. Thus H is a genuine
CK-style connected Hopf algebra derived from the proof grammar.

The quotient only identifies standalone zero-node forest factors with the
coefficient unit. It does not erase a typed leaf embedded in a positive tree,
identify two positive generators with different interface types, or change
the allowed graftings. In particular an internal typed hole remains part of
the positive generator's syntax.

For each output state i let M_i be the free module spanned by all P-trees with
that output, including e_i. The original coproduct has

    Delta_B(M_i) subset B_P tensor M_i.

Therefore

    rho_i = (q tensor id) Delta_B : M_i -> H tensor M_i

is a left H-coaction. Coassociativity follows from that of Delta_B and the
bialgebra identity for q; the counit law is inherited. Explicitly,

    rho_i(e_i) = 1 tensor e_i.

For positive T with root state i, the whole-tree extraction has term
q(T) tensor e_i. The state e_i has not become 1. Distinct e_i,e_j remain
distinct basis elements of the state module, even though their coefficient
images are both 1. This proves the desired dictionary entry:

    full typed polynomial-tree bialgebra
      -> connected positive-tree Hopf coefficients + typed-hole comodule.

After the trivial crown edges collapse, the coaction is exactly the sum over
all positive-vertex extraction antichains, with the literal typed remainder.
No cuts were filtered out to achieve the connected Hopf structure. Matching
to POTKIN3's native eligible-node policy remains an implementation obligation
if that policy omits some rule occurrences; the abstract theorem uses all
positive nodes of the specified grammar.

## 5. Genuine many-type Faà di Bruno identities

For each state i define the formal Green sum G_i of all P-trees with output i,
including e_i. For a finite-support profile n : I -> N, let g_{i,n} be the sum
of those trees whose open input edges have profile n. Then

    G_i = sum_n g_{i,n},
    Delta_B(G_i) = sum_n (product_j G_j^{n_j}) tensor g_{i,n}.       (1)

This is the many-type Faà di Bruno formula. It is a theorem for this exact
proof/certificate grammar, conditional only on the stated completion in which
the sums are interpreted.

**Direct proof.** A tree with a cut is the same data as a remainder R and, for
every physical open input edge of R, a matching-output tree grafted at that
edge. The remainder with profile n contributes g_{i,n}; its n_j distinct
physical slots of state j contribute n_j factors G_j. Multiplication forgets
the slot order only after all assignments to those slots have been counted.
Hence repeated isomorphic detached trees and distinct eligible positions have
exactly the same multiplicities on both sides. QED.

Equation (1) is not merely a resemblance to chain-rule notation. It is the
cut/grafting bijection which gives the Faà di Bruno substitution law. However,
one must distinguish the existence of this formula from an assertion that
an arbitrary chosen proof grammar contains a faithful copy of every generator
of the unrestricted classical Faà di Bruno Hopf algebra. Some profiles may
have no trees, or obey special restrictions. We claim the exact typed formula
and its generated bialgebra relations, not an unchecked nondegeneracy theorem.

The coefficient-profile form is also explicit. Introduce formal leaf markers
x_j and put G_i(x)=sum_n g_{i,n} x^n. Then

    Delta_B(g_{i,n})
      = sum_m [x^n](product_j G_j(x)^{m_j}) tensor g_{i,m}.       (2)

The bracket counts all typed distributions of the n external leaves among
the m grafted components. This is the precise point at which partition/fibre
combinatorics enters the proof calculus; it is not supplied by a one-hole
derivative alone.

### Closed proofs are an acceptance condition, not a subcoalgebra

Let C_i be the sum of positive P-trees with output i and no open inputs.
Only those root states i with empty owner stack are accepted whole proofs.
Their all-cut identity is

    Delta_B(C_i)
      = sum_n (product_j C_j^{n_j}) tensor g_{i,n}.               (3)

Indeed, cutting a closed tree gives closed detached components, but those
components can have nonempty inherited owner stacks. The remainder is open.
Conversely grafting a closed matching-output component at each input edge of
an arbitrary remainder closes all its inputs. This proves (3).

Applying q on the first leg gives the corresponding Hopf-comodule formula
for actual closed certificate sums, while preserving the typed open
remainders. Restricting both legs to empty-stack closed proofs would destroy
this formula and cut closure. Equation (3) supplies a positive reason to keep
all open states rather than treating them as an inconvenient side condition.

### Completion and numerical specialisation

The safest interpretation of (1)--(3) is objective: they are explicit
bijections before taking cardinalities. A basiswise formal-series completion
also works: for a fixed crown forest and remainder, only finitely many
state-compatible grafting bijections exist. Forest multiplication has finite
coefficient fibres. Infinite families of states therefore do not invalidate
the object-level identity.

To turn the identities into numerical generating functions, require a finite
operation signature or another explicit local-finiteness hypothesis. A finite
palette alone is insufficient: unrestricted weakening/formula choices can
still give infinitely many one-node rule instances. One can instead use a
finite registry of literal rule instances closed under its listed input and
output states, or attach sufficiently discriminating formal operation labels.

Nullary inference rules make the leaf-number grading nonpositive in places;
do not use leaf number alone to justify convergence. Introduce a parameter u
for positive-node number. Under finite local branching, the formal series
F_i(u,x) starts with e_i*x_i, while constant-in-x terms are O(u). This makes
typed substitutions well-defined u-adically, even with actual axiom rules.
For coefficient characters f,g with f(e_i)=g(e_i)=1, equation (2) yields the
composition orientation

    F_i^{f*g}(u,x) = F_i^g(u, F^f(u,x)),

where each node weight u occurs once in its own factor. This assertion
requires the stated continuity/local-finiteness hypotheses; arbitrary scalar
evaluation of an infinite Green sum is not automatically meaningful.

## 6. Where McBride's derivative fits exactly

The derivative of this indexed inductive family is the family of well-typed
one-hole contexts: an output state i, a selected hole state j, and a literal
context with that missing subtree. It is not the set of all CK cuts. The
derivative provides the one-slot operation used in grafting and local updates.
Higher derivatives mark several distinct physical holes. Substitution of
open trees composes these contexts, and the full cut/grafting correspondence
assembles them into (1)--(3).

More explicitly, let C_{ij} be contexts of output i with one distinguished
input hole of state j, allowing other unmarked open inputs. Decomposition
along the unique path to the distinguished hole gives the exact set equation

    C_{ij} = delta_{ij}
      + sum_{b:t(b)=i} sum_{k in premises(b)}
          (product_{l != k} T_{s(b,l)}) * C_{s(b,k),j}.            (4)

The product here constructs a tagged frame with its literal operation b and
selected premise k; it is not commutative identification of frame syntax.
The delta term is the typed identity context. Equation (4) follows by taking
the root operation and its unique distinguished child, or recognizing the
identity context. It therefore proves a concrete indexed McBride-context
description, including all scope/checkpoint typing information.

After a locally finite scalar weighting in which each positive operation
has a factor u, put T_i(u,x)=x_i+u P_i(T(u,x)). Ordinary formal differentiation
then gives the matrix chain-rule equation

    C(u,x) = I + u J_P(T(u,x)) C(u,x),
    C(u,x) = sum_{m>=0} (u J_P(T(u,x)))^m.                       (5)

Here C_{ij}=partial T_i/partial x_j counts a distinguished physical input
edge, and J_P is the Jacobian of the scalar polynomial signature. This
inverse is u-adic and exists because every nonidentity spine step uses at
least one positive rule node. It is a context-spine resolvent, not the Hopf
antipode. Formula (5) provides a concrete incremental sensitivity operator;
(1)--(3) supply its multihole substitution/decomposition setting.
Setting all remaining leaf markers x to zero after differentiation yields
contexts with exactly one open obligation: the marked hole. Those are the
contexts obtained by extracting one subtree from an otherwise closed proof.
Differentiating before this specialization is essential; specializing first
would erase the input variable whose hole is to be distinguished.

Thus there are three distinct, connected objects:

* the McBride derivative: one distinguished typed hole;
* multihole substitution: a typed family of physical slots and matching trees;
* CK/Faà di Bruno: all extraction/grafting decompositions, with their exact
  multiplicities and iterated composition laws.

Copying one logical payload into several slots identifies the values of
several physically different variables; it does not identify the slots or
their cut choices. No macro-expansion map is declared a Hopf morphism here.
Such a map would need its own cartesian/arity-preservation or cut-compatibility
proof; ordinary derivation expansion usually introduces new internal cuts.

## 7. What this changes in the research programme

The global revival condition now has an exact local typed grammar, giving a
canonical polynomial-tree bialgebra. The connected Hopf coefficient algebra
and typed remainder comodule are derived from it, rather than bolted onto an
unrelated tree observation. Its Green sums satisfy an actual many-type
Faà di Bruno identity. This is a coherent framework linking the Lang route,
open-proof interfaces, CK extraction, and typed substitution.

Applications already justified at the certificate level are modular
verification, colour-decorated certificate counting, and cache/replacement
composition across arbitrary full frontiers. The separate partition-diagram
semantics compresses concrete boundary colour tables without changing this
syntax carrier. Actual analytic proof revival still needs its formula-flow
and structural-rule theorem; computational reductions still need subject
reduction and freshening proofs. These are D1/D3 obligations within the D4
framework, not reasons to discard the framework.

Lean order: (1) local-state syntax and the certificate bijection; (2) cut/graft
equivalence for indexed trees with explicit zero-node edges; (3) quotient-leg
coaction on typed remainders; (4) finite profile identity before infinite Green
series; (5) instantiate compact kernel semantics and actual native fixtures.
Do not start by formalising groupoids or general formal power series if the
finite witness bijections are sufficient for the next theorem.

### Executable supplemental evidence

`check_polynomial_bridge.py` independently enumerates cuts and graftings in a
two-state, six-constructor grammar with nullary, unary and binary operations.
Through three positive nodes it checks 98 trees, 374 physical cuts and 332
distinct crown/remainder pairs. The two independently enumerated sides of
the full Green identity agree, including occurrence multiplicities. It also
checks the quotient-leg comodule flag identity on every tree, retains both
distinct zero-node state edges, and verifies the closed-input specialization.
Results are in `polynomial_bridge_results.json`. This is bounded diagnostic
evidence for the stated universal paper proofs, not a native LQ or Lean proof.

## Primary source

Joachim Kock, *Polynomial functors and combinatorial Dyson--Schwinger
equations*, arXiv:1512.03027v4 (2017), Sections 3 and 7.
https://arxiv.org/pdf/1512.03027
Section 3 supplies the indexed polynomial and P-tree setup; Section 7 supplies
the cut bialgebra, group-like zero-node edges, connected quotient, and Green
function Faà di Bruno formula. The scoped LQ polynomial, its exact certificate
bijection, and the explicit one-leg quotient/comodule comparison above are
our application and deductions. Kock does not discuss Lang's LQ certificates.
