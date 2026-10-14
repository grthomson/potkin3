# An inverse ghostification compiler and a conditional D1 bridge

12 October 2026. Paper-level construction; no Lean theorem or native proof-
normalization implementation is claimed. This note sharpens the inverse half
of Lang's Theorem 12 for a specified ordinary LJ presentation.

## 1. Exact input discipline

Use cutfree propositional LJ with atomic identity `p=>p`, bottom-left, explicit
left/right weakening, left contraction, primitive negation, and the usual
context-sharing logical rules. Antecedents are occurrence-labelled multisets.
For each inference, choose its ordinary premise-to-conclusion formula ancestry
maps, including both copies created by contraction or shared-context branching.
Each premise occurrence has one descendant conclusion occurrence unless it is
discharged as the indicated ancestor of that inference's principal formula.
Logical principal formulas retain their standard constructor ancestry.

The input is a cutfree proof of `Γ, Ω => Δ`, where Ω is a designated multiset
of atomic weak-excluded-middle formulas `W(p)=¬p∨¬¬p`. Occurrences in Ω are
marked individually. Equal formulas in Γ or Δ are NOT marked merely because
they have the same text. Root occurrence marks propagate upwards along formula
ancestry; contraction and shared-context rules can produce several marked
premise occurrences from one marked conclusion occurrence.

Atomic identity is essential. Erasing the left occurrence in an unexpanded
identity `W(p)=>W(p)` would produce the forbidden ghost initial `=>W(p)`.
A presentation allowing general identities must first provide its standard
cutfree identity-expansion lemma, with ancestry marks transported through the
expansion. This prerequisite is explicit, not silently assumed.

## 2. Erasure algorithm

Delete every formula occurrence ancestral to a designated Ω occurrence.
Then transform each rule occurrence as follows.

* An atomic identity becomes an ordinary identity, one-sided ghost `p=>` or
  `=>p`, or empty ghost `=>`, according to which of its two occurrences vanish.
* A disjunction-left occurrence whose principal formula is a marked W(p)
  becomes the ghost binary rule with two identical erased premises/conclusion.
  Give this occurrence its OWN physical owner ID and colour p.
* A negation-left/right occurrence whose principal formula is marked becomes
  a unary identity-on-the-erased-sequent step. Suppress this dummy step.
* Marked weakening/contraction steps likewise become dummy steps (or the
  same structural rule on any surviving unmarked principal occurrences in a
  simultaneous structural-rule presentation). Suppress only actual dummies.
* Every other rule remains the corresponding ordinary rule on the surviving
  formulas. Bottom-left cannot lose its bottom formula: bottom is not an
  ancestor of an atomic W(p).

The output retains all genuine ghost binary owners, even if their two erased
premises happen to be identical or they receive no assigned ghost leaves.
A source Ω occurrence introduced entirely by weakening creates no owner.
Contraction of one Ω occurrence may create several owners: owner identity is
therefore the actual disjunction inference, not the root Ω occurrence.

## 3. Why these are all the cases

A marked formula is a syntactic subformula of W(p), with side determined by
its constructor ancestry. Starting at the left root W(p), its only possible
principal decomposition is disjunction-left. Above its left premise, the
marked lineage is left `¬p`, then right `p` through negation-left. Above its
right premise, the lineage is left `¬¬p`, then right `¬p` through negation-left,
then left `p` through negation-right. Weakening can terminate a lineage;
contraction and shared-context branching can copy it; passive transport keeps
its formula and side. Atomic identities terminate the remaining lineages.

No other logical constructor can be marked: neither implications nor
conjunctions are subformulas of W(p). In particular a marked disjunction-right
or conjunction-right case cannot arise. Ordinary rules with marked context
occurrences remain ordinary rules after those context occurrences are deleted.
The single-succedent constraint is preserved because erasure only removes
formulas. These observations are a rule-by-rule induction on the marked proof,
not an appeal to an unspecified global subformula property.

## 4. Extracting the owner certificate

For every marked atomic occurrence in an identity, trace its formula ancestry
rootwards until its unique disjunction-left constructor of a W(p) is reached.
This occurs before its designated root Ω occurrence. The constructor is unique
on that lineage; any copying above it has only created distinct initial
occurrences sharing the same owner, not a second possible owner for one trace.

* If the marked occurrence is the identity's RIGHT p, it came through the
  owner's left `¬p` branch. Assign the resulting ghost `p=>` to that owner's L.
* If it is the identity's LEFT p, it came through the owner's right `¬¬p`
  branch. Assign the resulting ghost `=>p` to that owner's R.
* If both are marked, assign the empty ghost to the L owner found from its
  right occurrence and the R owner found from its left occurrence.

An empty ghost's two owners can differ and are allowed to do so. Their colours
are equal because the original atomic identity used the same atom on both
sides. The two traces cannot belong to opposite branches of the SAME physical
owner: one identity node cannot lie in both disjoint premise subtrees.

Each owner is coloured by its principal W(p). Hence every one-sided ghost
forces its own original atom, every empty ghost equates its two owner colours,
and each owner already equates its own left and right roles. The connected-
component consistency clause follows without any search for fresh variables.
Exact once-only membership follows from the unique ancestry trace of each
physical marked occurrence. Branch routing follows from the owner's literal
premise position.

### The checkpoint lemma

A right-assigned atomic occurrence travels through the owner's right branch
via a negation-right inference

    Σ,p =>   /   Σ => ¬p

before the subsequent negation-left step produces `¬¬p` on the left. Its
premise has empty succedent. Erasing marked formulas therefore leaves an
empty-succedent sequent strictly above the owner. This supplies the required
checkpoint for every right-assigned leaf passing through that inference.

Suppressing unary dummy rules does not destroy this witness: a suppressed
rule has equal erased premise and conclusion. The finite chain of suppressed
nodes can be replaced by its surviving child root carrying that same erased
sequent. Eventually a surviving ordinary rule, ghost owner, or initial occurs.
If that survivor is another ghost owner, its empty conclusion is still
strictly above the owner currently being discharged. If it is an empty ghost
initial, that leaf itself is the checkpoint. Thus the permitted endpoint
convention is preserved.

## 5. Theorem G1: constructive inverse soundness

From every input proof satisfying Section 1, erasure constructs a cutfree
LQ-grounded ghost proof of exactly `Γ=>Δ`, together with a Definition-5 owner
assignment and compatible owner colouring.

**Proof.** Section 3 verifies that all surviving local rules belong to the
required ghost extension. No Cut is introduced. Formula erasure removes
exactly Ω from the endsequent. Section 4 constructs exact leaf memberships,
colour consistency, branch routing and a checkpoint for each right assignment.
These are all of Definition 5's conditions. QED.

The output may be smaller than the input because dummy inferences disappear.
It is not an inverse on literal proof trees: forward revival introduces
structural padding, and subsequent erasure can leave different ghost-owner
multiplicities or administrative branches. The theorem promises a correct
certificate and the same unmarked endsequent, not a round-trip identity.

## 6. Conditional D1 theorem using base Cut elimination

Assume an executable, sound Cut-elimination operation for this ordinary LJ
presentation, returning a cutfree proof of the same occurrence-labelled root
sequent; if necessary also assume the atomic-identity expansion operation.
Given any well-typed finite composition by Cut of already certified LQ ghost
proofs, the following algorithm returns a cutfree LQ-grounded proof of its
endsequent:

1. Fix one finite palette A containing all certificate owner colours and
   forced atoms in the finite input. Canonically compile each input proof to
   ordinary LJ with the common added antecedent W(A).
2. Perform the requested original Cut compositions in ordinary LJ, retaining
   the added W(A) occurrences as designated assumptions. Where context-splitting
   Cut creates duplicate copies of W(A), contract them to the chosen common
   root multiset. Do not designate equal original Γ formulas by textual equality.
3. Invoke the ordinary LJ Cut-elimination algorithm on this ordinary proof.
   Mark the designated W(A) occurrences at its unchanged endsequent and trace
   their ancestry anew in the resulting cutfree proof. The normalization need
   not preserve the original interior owner IDs or ghost routes.
4. Apply G1 to obtain the desired cutfree grounded ghost proof and certificate.

Correctness is immediate from C4, ordinary Cut/structural rule soundness,
the assumed base normalization theorem, and G1. Crucially, no unproved claim
that the ORIGINAL certificate is invariant under Cut reduction is needed:
the normalized ordinary proof yields a newly extracted certificate.

This is a constructive strongly modular route in Lang's sense, once its
ordinary-LJ normalization dependency is supplied. We have given its explicit
proof-object interfaces; we have not implemented a base Cut eliminator here.
It is a D1 consequence of the D4 compiler framework with D3 resources exposed.
The finite-palette WEM premise is legitimate for LQ; no transfer to arbitrary
substructural bases is claimed.

## 7. Relationship to CK and to the existing dictionary

Forward reconstruction is coherent across all original source CK cuts via
linear macro substitution. Its canonical kernels and structural-debt weights
support cached reconstruction plans. G1 provides the missing return path from
ordinary normalized proof objects into certified analytic ghost syntax.
Therefore the framework can organize reconstruction, invoke a trusted base
normalizer, and recover a checked ghost certificate rather than ending at
an ordinary proof with additional axioms.

G1 itself is not asserted to commute with every CK cut: erasing dummy chains
changes addresses, and proof normalization can copy or remove regions. A
combined Hopf-compatible transformation requires explicit marked macro/cut
comparison maps. Nor is the composite forward/normalize/erase operation a
literal involution or a coalgebra morphism by definition. These remain
separate mathematical statements, not prerequisites for the conditional D1
correctness theorem above.

## 8. Analyticity and extraction cost

For the specified cutfree LJ rules, each premise formula occurrence has one
rootward formula descendant, and its formula is a subformula of that
descendant. A retained occurrence has an unmarked root descendant: otherwise
it would have been erased by the marking algorithm. Therefore every formula
in the ghost output is a subformula of an unmarked endsequent formula in Γ or
Δ. Dummy suppression preserves this property. In particular auxiliary palette
atoms appearing only inside designated WEM assumptions disappear completely
unless already subformulas of Γ or Δ.

Thus G1 returns an analytic proof in this exact sense, not merely a syntactic
proof with Cut absent. The proof uses the local subformula ancestry property
of the specified LJ rules; an extension with nonanalytic primitive rules
requires a separate audit.

With formula ancestry maps supplied explicitly, marking and owner-role
propagation use one pass through the explicit formula occurrences. Erasure
never copies a proof subtree, so its output rule count is at most the input
rule count. Atomic-identity expansion, if needed, is a preceding operation
with its own size cost. No complexity bound for the assumed base Cut eliminator
is implied.

## 9. Executable inverse evidence

`check_ghostification.py` implements occurrence-specific root designation,
formula ancestry through the represented atomic LJ rules, erasure, dummy
suppression, and physical owner/leaf certificate extraction. It checks fourteen
actual ordinary proofs: the two coordinated-replacement outputs; marked and
canonical outputs for each of the five nested-WEM certificate witnesses; and
two tests designating different occurrences among two textually identical WEM
antecedents.

Every extracted certificate is independently checked for branch routing,
colour consistency, and the surviving empty-succedent checkpoints. Every
result is then revived again into a locally checked ordinary cutfree LJ proof.
In the identical-formula tests, designating the weakened occurrence gives
zero ghost owners, while designating the other gives one ghost owner. Both
preserve the unmarked equal WEM occurrence. This directly exercises the
occurrence-sensitive qualification needed by the theorem.

These are executable fixtures, not universal kernel checking. No ordinary-LJ
Cut-elimination algorithm is present in this script; the D1 normalization
bridge remains conditional on that explicit dependency.

## 10. Extension to globally certified proofs whose owners cross Cut

The closed-composition theorem in Section 6 is not the strongest available
paper statement. A grounded owner may lie below a Cut whose premise is not
independently grounded. Cutting the source into separately closed certificates
would miss that case. The marked compiler has a direct additional clause for
ordinary context-splitting Cut:

    Γ => B       B, Σ => Δ
    --------------------- Cut
          Γ,Σ => Δ.

If the two compiled premises have extra marked token bags E1 and E2, apply
ordinary Cut to the two ORIGINAL B occurrences. The result is

    Γ,Σ,E1,E2 => Δ.

The incoming token IDs are disjoint because their birthplaces lie in distinct
source premise subtrees. Thus concatenation is exactly the required outgoing
marked bag. No extra weakening or contraction is needed for this Cut adapter.
Afterwards perform scheduled empty-succedent checkpoint conversions as usual.
Owner routing and first-checkpoint existence are unchanged: a token may cross
Cut while remaining an antecedent assumption, and its source Cut conclusion
may itself be its first permitted empty checkpoint.

This extends C1 to proofs containing Cut: the output contains precisely the
replayed source Cuts, and all newly inserted compiler macros remain cutfree.
For a primitive context-sharing Cut presentation, use its common-context
transport; if simulating that presentation via context-splitting Cut, record
the necessary explicit contractions separately. Do not conflate these two
resource counts.

**Theorem G2 (relative constructive Cut elimination).** Suppose the source is
the specified propositional ghost extension with ordinary context-splitting
Cut, and its complete finite tree has a routing/colour/checkpoint certificate.
Assume an ordinary-LJ Cut-elimination operation returning the same root
sequent, and atomic identity expansion if its output requires it. Then:

    marked revival including the above Cut adapter
      ; ordinary LJ Cut elimination
      ; occurrence-designated ghostification G1

constructs a cutfree grounded ghost proof of the same source endsequent.

**Proof.** The extended C1 induction gives an ordinary LJ proof with precisely
one extra designated WEM assumption per ghost owner. Apply the assumed base
normalizer. The endsequent multiset, including those individually designated
assumptions, is unchanged. Mark their ancestry afresh in the normalized proof
and apply G1. The result has the original endsequent, has no Cut, and carries
its newly extracted grounding certificate. QED.

This theorem includes certificates whose owners span Cut-premise boundaries;
it does not require premise certificates to close independently. It does not
assert preservation of the original owner IDs, routes, CK cut spectrum, or
structural cost through base normalization. Those are distinct quantitative
questions. Its dependency on a correct base Cut eliminator is explicit and
is not implemented by the current scripts.

### An executed Cut-spanning-owner example

`check_cut_bridge_fixture.py` exercises the stronger scope of G2. Its ten-node
source proves WEM with an outer ghost owner and a right-assigned `=>p` leaf
inside the FIRST premise of an ordinary Cut. That premise is not independently
grounded. The Cut's empty conclusion is the leaf's first checkpoint, so this
case also tests checkpoint creation at the Cut adapter itself.

Marked revival produces a thirteen-node ordinary proof containing the one
original Cut. A specifically checked identity-Cut reduction removes that Cut
and its left identity premise, giving an eleven-node ordinary cutfree proof.
Ghostification extracts the expected eight-node grounded WEM proof and its
new valid certificate. The compiler adds neither weakening nor contraction
in this example; its three extra nodes are one left-ghost revival step and
two right-checkpoint steps.

This is an executed end-to-end witness for G2 with one elementary normalization
case. The script explicitly implements ONLY identity-Cut reduction, not a
general ordinary-LJ Cut eliminator. The universal theorem still takes that
normalizer as a dependency.
