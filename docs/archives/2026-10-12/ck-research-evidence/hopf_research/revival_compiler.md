# Constructive revival as a linear macro compiler

12 October 2026. Paper theorem plus an executable fixture compiler; not a Lean result.

## Source and scope

Lang, *Some Analytic Systems of Rules* (2023), Definition 5 and Theorem 12,
pp.108–109, supplies the LQ correctness criterion and sketches its revival.
Primary source: https://discovery.ucl.ac.uk/id/eprint/10182303/1/tableauxRep.pdf .
The result developed below makes the structural adapters and open-fragment
composition explicit. It is not claimed as a new soundness theorem for LQ.
The new project contribution is the compiler interface and its compatibility
with the full source extraction/refill operation.

Fix the cutfree, propositional, single-succedent LJ presentation used there,
with finite-multiset antecedents, explicit left weakening/contraction,
negation, and context-sharing binary rules. Extend it only by ghost initials
`p=>`, `=>p`, `=>` and the ghost binary rule `Γ=>Δ, Γ=>Δ / Γ=>Δ`.
Fix a physical routing assignment satisfying Definition 5 and a consistent
owner colouring. Owners and ghost leaves have distinct physical IDs.

Write `W(p)=¬p∨¬¬p`. We construct a cutfree ordinary LJ derivation of

    Γ, [W(colour(i)) | i a physical ghost owner] => Δ.

The displayed list is a multiset: equal colours do not silently identify owners.
This is a derivation with WEM assumptions, not a claim that ordinary LJ proves
WEM. The passage to an LQ theorem is Lang's deduction/axiom-extension step.

## Marked token interface

Each ghost leaf contributes at most two distinct tokens. Its left token carries
`¬p`; its right token initially carries `p`. Right tokens convert to `¬¬p` at
the first source sequent with empty succedent on their path towards their
owner, with the owner's conclusion excluded. The checkpoint exists by the
certificate. A discharged owner contributes one terminal token `W(p)` which
persists to the endsequent.

These are occurrence marks for the construction, not extra connectives. Two
marks can carry the same formula. The output interface of a source node is its
literal source sequent plus the finite marked multiset of currently live
formulas. The marks remember owner, leaf, phase, and terminal-WEM status.

Structural padding introduced at a rule is not a new routed ghost token. It
is a local proof occurrence needed to match the contexts of that inference.
In particular it creates no new checkpoint obligation or owner assignment.

## Local construction

1. At `p=>` assigned left owner i, start from identity `p=>p` and apply `¬L`
   to obtain `p,¬p=>`. The added formula has the leaf's left-token mark.
2. At `=>p` assigned right owner i, use identity `p=>p`, marking its antecedent
   occurrence as the new raw right token.
3. At `=>` assigned left i and right j, colour consistency gives `p_i=p_j=p`.
   Identity followed by `¬L` gives `p,¬p=>`, carrying the two distinct marks.
4. At an ordinary inference, take the union of the incoming marked token bags.
   In each premise, add missing token formulas by left weakening. Apply the
   same original rule to its original principal occurrences, treating the
   common token bag as additional antecedent context. This is a literal LJ
   inference in the shared-context presentation. Original weakening/contraction
   acts on the original marked formula occurrence, not on a routed token.
5. At owner i, the left child contains only i's left tokens `¬p_i`, and the
   right child contains only i's already converted tokens `¬¬p_i`. No raw
   right i-token can remain, because its first checkpoint is above this owner.
   Contract each nonempty collection to one occurrence. If a collection is
   empty, add one occurrence by weakening. Pad both premises to the union of
   their remaining external/terminal token bags. Apply ordinary `∨L`, producing
   one new marked terminal formula `W(p_i)`.
6. After the local inference at any source node with empty succedent, convert
   every raw right token whose first checkpoint is that node. For each such
   marked occurrence, use exactly

       Σ,p =>   /   Σ => ¬p   /   Σ,¬¬p =>

   by `¬R` then `¬L`. All other tokens belong to Σ. A fixed total order on
   token IDs makes the multiple-token case deterministic. At an owner, do
   step 5 before step 6, so its own conclusion cannot satisfy its own debt.

Converting one token leaves the succedent empty after its two-rule macro, so
all scheduled conversions at that node can be performed successively.

## Theorem C1: constructive sound revival

For every well-typed cutfree source derivation with a Definition-5 routing
certificate and compatible colouring, this algorithm constructs the displayed
cutfree LJ derivation. It uses every source premise derivation exactly once.

**Proof.** Induct over source nodes. Ghost-leaf cases are the explicit identity
macros. For an ordinary inference, the induction hypotheses give its literal
premise sequents extended by their token bags. Weakening pads those bags to a
common bag; every propositional LJ rule admits the unchanged common antecedent
context. Reapplying the original inference therefore produces its literal
conclusion plus that bag. In the ghost-owner case, routing excludes left
owner tokens from the right child and right owner tokens from the left child.
Checkpoint correctness excludes raw own-right tokens. The two principal
formula collections therefore have the required shapes. Contraction or
weakening gives exactly one principal occurrence on each side. The shared
background is obtained by weakening; `∨L` then produces the promised WEM.
Checkpoint macros are valid because their source node has empty succedent.
No macro uses Cut. Every child derivation occupies exactly one premise slot.
At the root, every leaf token has reached and been discharged by its owner,
so only the one terminal WEM token per owner remains. QED.

The theorem is constructive: it supplies a proof object, not merely a
satisfiability test of the equality network. It is also uniform in the owner
colouring, including owners with no assigned ghost leaves.

## Structural-resource audit (D3/D6)

Left weakening is used for: padding unequal incoming token bags at shared-
context inferences; supplying an unused left/right owner assumption; and the
original proof's own weakening steps. Contraction is used to consolidate
multiple same-owner tokens at discharge, in addition to source contractions.
Exchange is implicit in multiset antecedents. No right weakening or Cut is
needed by the new compiler macros. If the source includes right weakening,
its original occurrence can be replayed, but the compiler does not add one.

This proves the result for the stated LJ base. It does not prove it for a
linear/relevant/noncommutative base. Such a transfer must replace each listed
adapter with an admissibility theorem or restrict token flow so that it is
unnecessary. An immediately identifiable contraction-free *added-macro*
fragment has at most one left and one right assigned ghost leaf per owner;
this does not remove source contractions or padding weakenings.

## Theorem C2: source-cut gluing coherence

Decorate every source edge with the live marked formula interface computed
above; record the owner colouring and predetermined checkpoint schedule.
Decorate each source node with its deterministic local macro, including fixed
orders of weakenings, contractions, and checkpoint conversions. For any full
native CK antichain c, compiling the open remainder and detached fragments,
then plugging their matching compiled interfaces, gives exactly the globally
compiled proof tree. This equality is literal after fixing list presentation
and deterministic mark-erasure convention. Every source cut is included.

**Proof.** The compiled tree is the simultaneous substitution of one fixed
open proof macro for every source node. Each macro has exactly one proof hole
for each source premise, used exactly once. The source cut partitions nodes
into the detached pieces and remainder. Composing macros separately on those
pieces and then filling the corresponding holes substitutes exactly the same
macros at exactly the same tree incidences. Associativity of typed tree
substitution proves the equality. There is no duplicated proof hole and no
lost macro. Nested source cuts give the same result by the same argument for
three layers. The decorations must be inherited from the whole source; one
must not recompute a checkpoint while pretending an open piece is closed.
QED.

This is a compiler/refill theorem over the full source CK cut structure. It
is **not** a Hopf morphism to the entire ordinary LJ proof algebra: compiled
macros contain additional internal rule nodes, hence additional target CK
cuts. The theorem compares the source cuts with their macro-boundary images.
The existing full target coproduct is not filtered or modified.

## Compiler interface versus compact certificate kernel

A partition/checkpoint kernel answers which colour/token boundary assignments
are compatible and how many certificate choices they allow. It need not
contain the internal source proof or an LJ proof. The compiler additionally
requires that proof and its concrete routing/phase witness. A certified cache
entry can store (1) the compact kernel and (2) the compiled open proof generator
indexed by satisfying boundary assignments. Equal kernels then justify the
*compatibility* of module replacement; the generators deliver the resulting
proof objects. This is a precise way to avoid mistaking matrix equality for
proof synthesis.

Theorem C2 lets one compile/reuse all modules at a selected CK frontier and
assemble them without rerunning reconstruction of unaffected interiors.
Convolution over full frontiers can count or optimize these choices; every
nonzero chosen term carries actual proof-producing data. This closes the
specific gap between certificate feasibility and reconstruction, subject to
mechanizing this compiler on the native proof syntax.

## Theorem C3: explicit reconstruction-size bound

Let n be the source rule-node count, b its number of binary nodes, ℓ its number
of ghost initial nodes, and o its number of ghost owners. Let τ bound the
number of surviving marked tokens in the union of the child interfaces at a
binary node (for owners, remove their own discharged tokens first). Then the
compiler's ordinary proof has at most

    n + b τ + 5ℓ + 2o

rule nodes. In particular τ≤2ℓ+o≤2n, so `2n²+6n` is a uniform coarse bound.

**Proof.** One source node contributes one replayed inference or replacement
macro base node. Replacing a left/empty ghost initial by identity-plus-negation
adds at most one extra node, hence at most ℓ. Every right ghost token converts
exactly once by two negation rules, adding at most 2ℓ. Owner contractions add
at most the number of routed left/right tokens, hence at most 2ℓ. Missing own
principal tokens require at most two weakenings per owner, hence 2o. Child
token marks belong to disjoint source subtrees, so at a binary node the total
number of missing tokens padded into the opposite premises is at most τ.
Unary ordinary nodes require no padding. Sum these contributions. QED.

This is a rule-node bound; it does not count serialized formula lengths or
integer/identifier representation costs. It shows that this fixed-certificate
revival compiler itself need not duplicate proof subtrees exponentially. It
does not bound the search for certificates or the size of a prior Cut-
elimination transformation. The dependence on live token width also suggests
an implementation parameter alongside the colour-kernel boundary width.

## Executable fixture evidence

`check_revival_compiler.py` compiles both valid uniform-colour versions of the
21-node coordinated-replacement fixture in `check_lq_certificates.py`. Each
output has 29 rule nodes: 4 ordinary identities, 6 negation-left rules,
2 negation-right rules, 3 disjunction-left rules, 13 weakenings and 1 contraction.
Every output inference is checked against its literal multiset sequent.
There is no ghost rule and no Cut. The root is the source endsequent extended
by exactly one WEM formula, with the relevant owner colour.

For each output, all 963 full source antichain choices (empty and whole-root
included) are tested by caching compiled detached subtrees and reassembling
the source remainder against their inherited token interfaces. All reconstruct
the identical proof tree. This checks these two actual fixtures, not a
universal theorem or a native kernel. C1–C3 above have paper proofs; none has
been implemented in Lean here.

## Exact structural debt and additive regional accounting

A source-edge token has a unique birthplace and follows one rootward source
path. It therefore cannot arrive along two different premise edges of one
source node. Tokens with the same owner but different ghost-leaf IDs remain
distinct; their phases may differ until their checkpoints. Formula occurrences
introduced by padding live inside that node's macro and do not create new
source-edge token births. Terminal WEM tokens obey the same invariant, with
their owner's conclusion as birthplace. This proves the disjointness used in
C3 and makes the following exact accounting possible.

Let L count ghost `p=>` plus ghost `=>` leaves, and R count ghost `=>p` plus
ghost `=>` leaves. Let Wadd and Cadd be the numbers of newly inserted left
weakenings and contractions (excluding replayed source structural rules).
Then, for the stated deterministic compiler,

    |compile(T)| = |T| + L + 2R + Wadd + Cadd.

At an ordinary k-premise rule with incoming token sets E1,…,Ek and union E,
the new weakening count is `k|E|−Σj|Ej|`. For a ghost owner i, first remove
its own tokens from each child bag, obtaining Bleft,Bright. Its added counts
are

    C_i = max(nleft−1,0) + max(nright−1,0),
    W_i = [nleft=0] + [nright=0]
          + 2|Bleft∪Bright|−|Bleft|−|Bright|.

Here nleft and nright count its own left and converted-right tokens. All
other new structural counts are zero. The ghost-leaf macro contributes one
extra rule exactly for the L leaves. Every R token contributes two negation
rules at its unique scheduled checkpoint. Ordinary rules replay once; an
owner's ordinary disjunction rule replaces its ghost node one-for-one.
Summing these exhaustive contributions proves the identity.

For the 21-node fixture, `L=0`, `R=2`, `Wadd=3`, `Cadd=1`, so the exact output
count is `21+0+4+3+1=29`. Two of the three new weakenings pad the distinct right
tokens across ordinary disjunction premises; the third supplies the unused
owner-left assumption. The source already has ten weakenings, explaining the
output's thirteen.

Each contribution belongs to exactly one source node. Its value is determined
by that node's local rule and inherited token interfaces. Therefore Wadd,
Cadd, L, and checkpoint-conversion counts are additive over EVERY CK vertex
partition, including cuts that separate a token from its checkpoint or owner.
A fragment exports its unresolved token interface; it does not prematurely
charge its future discharge. Corresponding nested-cut packets carry identical
sums. Thus a coefficient `u^Wadd v^Cadd z^newRules` can accompany the certificate
kernels and proof generators with no new frontier restriction.

This measures the D3 structural debt of the actual reconstruction. It allows
cached plans to be compared by weakening/contraction cost as well as retained
source nodes. Zero cost in this compiler is a sufficient witness that its
added macros use no corresponding structural rule; a positive cost is NOT a
lower bound over all possible proof reconstructions.

### A zero-added-structure WEM benchmark

There is an eight-node genuine source derivation of `=>W(p)`:
its owner-left branch is `ghost p=>`, then `¬R`, then `∨R` into W(p);
its owner-right branch is `ghost=>p`, then `¬L`, then `¬R`, then `∨R` into
W(p). The root ghost disjunction joins those identical endsequents. Assign
its one left leaf and one right leaf to the root owner. The right leaf's
negation-left conclusion provides its checkpoint.

Here L=R=1 and Wadd=Cadd=0. The compiler produces the eleven-node cutfree LJ
proof `W(p)=>W(p)`. Its implication for the original ghost proof is the
actual WEM theorem, not an already-LJ-provable empty-succedent example.
The executable checker validates every output rule and every full source
cut/reassembly for this fixture as well.

More generally, the exact accounting proves that the compiler inserts no W
and no C precisely when every padding contribution is zero and every owner
has exactly one left and one right token. This is a syntactic, decidable
zero-added-structure fragment. It is not automatically a theorem about all
linear bases: the chosen base must still admit the logical context transports
used in replaying each rule. It gives a concrete D3/D6 test case where the
new revival construction itself spends neither weakening nor contraction.

## A canonical proof interface for reusable cached modules

The marked compiler above preserves exact occurrence provenance and costs.
For cache interchangeability, a second, deliberately structural normalization
removes dependence on the number of internal owners and assigned leaves.
This result was proposed by the revival-algebra reviewer and is proved here.

Fix a nonempty finite atom palette A containing all owner colours and forced
atoms in the source and proposed replacement library. Let `W(A)` contain one
WEM formula for each palette atom. At a source boundary, an active owner is a
strict ancestor owner whose left/right premise contains that boundary. Fix its
colour and branch role. Let d_i mean that at least one right-assigned leaf for
owner i below the boundary has not yet encountered its required empty
checkpoint. This is the aggregate pending-debt state.

Define the canonical extra antecedent multiset to contain:

* one copy of every formula in W(A);
* one marked `¬colour(i)` for every active LEFT owner i;
* one marked `¬¬colour(i)` for every active RIGHT owner i;
* additionally one marked `colour(i)` for each active RIGHT owner with d_i=true.

Marks distinguish equal formulas belonging to distinct owners. Its type
depends only on palette, active scope, colours, roles and debt, not on the
fragment's leaf multiplicities or number of internal owners.

**Theorem C4 (canonical certified module generator).** Every correctly routed
and colour-consistent source subtree, with no undischarged debt at any internal
owner, compiles to an ordinary cutfree LJ derivation of its source endsequent
extended by this canonical multiset. The construction is uniform in all
satisfying boundary colour/debt assignments.

**Proof by explicit local construction.** At ordinary initial leaves, replay
the original initial rule (including bottom-left if present); at ghost leaves,
use the appropriate identity revival macro. Pad by W to the required canonical
assumptions, retaining any newly born raw token until empty-node processing.
A ghost leaf contributes its genuine raw/left assumptions; all other canonical
formulas may be introduced by W. At an ordinary node, both children have the
same active scope. Join their right debts by OR and pad missing raw formulas
by W, so both antecedents share the same canonical context. Replay the source
rule. At an empty source conclusion (including an empty ghost initial), convert each still-present raw p by
`¬R;¬L` and contract its resulting `¬¬p` with the already-present canonical
double-negation copy. Only after this postprocessing assert the final canonical
antecedent with cleared debt; the temporary raw formula at an empty ghost
initial is not prematurely discarded. This clears exactly the passing debts.

At an internal owner i, its left canonical child has the own principal `¬p_i`,
and its right child has `¬¬p_i`. Its own right debt is false by hypothesis.
Remove those two own fields when forming the external context; join/pad the
remaining external debts. Apply `∨L`. Its newly produced WEM occurrence is
contracted with the copy already in W(A). Process any empty conclusion only
AFTER discharging i, so it cannot clear i's own debt. All inferences are
ordinary LJ and cutfree. At every step the output has exactly the prescribed
canonical context. QED.

The canonical compiler spends additional W/C by design. It must not be used
to claim the marked compiler's zero-debt benchmark remains zero-debt. Its
purpose is a stable proof type for cache replacement. Fixed-palette atomic
WEM assumptions remain legitimate LQ axioms; this construction does not treat
them as ordinary LJ theorems.

**Corollary C4.1 (proof-producing stable replacement).** Suppose two source
modules have the same root sequent, active scope/roles, palette, and the same
certificate kernel on boundary colour/debt states. Attach to each nonzero
state a witness certificate and the canonical compiled proof generator.
Either module can replace the other in any exterior accepting that state:
the replacement has exactly the expected ordinary-LJ interface and can be
plugged into the same canonical compiled exterior, producing an actual
cutfree proof under W(A). Equality of kernels preserves feasibility/count;
the supplied generator establishes reconstruction.

The replacement theorem compares source boundaries and opaque module uses.
It does not identify the internal CK spectra of the modules. Compiling the
exterior in canonical form (or supplying a one-time interface adapter) is
part of the theorem; it does not silently assume the marked and canonical
interfaces are literally equal.

This closes the concrete gap where the compact certificate kernel omitted
internal-owner WEM multiplicities needed by a raw revival proof. It also
separates two legitimate interfaces: occurrence-sensitive marked types for
exact resource accounting, and canonical scope/debt types for stable reuse.

### Further executable checks of owner scope and canonical adapters

`check_revival_nested.py` implements the marked compiler for arbitrary owner
routes within its represented LJ rule fragment. On the real 17-node nested
WEM fixture, the two-atom palette has five compatible colour/routing witnesses.
All five compile to checked ordinary cutfree proofs (sizes 27–29); each of
its 442 full source cuts reassembles literally. A further ten-node fixture
contains an empty ghost initial whose left token belongs to the outer owner
and right token to an inner owner. Its unique witness compiles to an 18-node
ordinary proof; all 53 source cuts reassemble. Every exact structural-debt
identity is checked.

At every subtree boundary in those six compiled witnesses, a separate W/C
adapter contracts marked formula multiplicities and pads to the canonical
palette/scope/debt antecedent. All 95 resulting ordinary proof objects are
locally validated. This checks the interface normalization used by C4; the
script does not claim an independent executable implementation of the entire
direct canonical compiler or of the universal contextual replacement theorem.
