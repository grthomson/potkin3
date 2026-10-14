# Independent audit: full CK cuts with certificate coefficients

12 October 2026. Paper arguments and finite executable checks; no Lean claim.

## Decision

The positive framework is viable at the level of fixed certificate constraint
networks and complete named cut interfaces. It should retain the full proof
carrier and interpret its cut diagrams in boundary-indexed kernels. This is
an algebraic programme with legitimate applications even when one local
checker admits an elementary implementation. The meaningful questions are
which all-cut laws are true, what they compute, and which semantics they
transport—not an impossible demand that no alternative implementation exist.

The following cautions are constructive design choices, not a veto on the
framework.

## 1. Three distinct operations must not be confused

1. Restrict a fixed global witness along a physical cut.
2. Glue independently supplied open witnesses under shared names.
3. Replace a syntax tree by a compact contextual summary.

(1) can preserve validity with exported obligations at every full CK cut.
(2) needs compatibility; factorwise validity alone does not suffice.
(3) can preserve a contextual observation while destroying the CK coproduct.

The intended architecture performs the full syntax decomposition first and
applies summaries as coefficients. It does not demand that summaries carry
an independently well-defined CK coproduct.

## 2. Minimal shared-name obstruction and correction

Take a variable x with values {0,1}. One detached factor has constraint x=0;
another has x=1. Both are separately satisfiable; their union is not.

Thus neither Boolean conjunction of closed satisfiability values nor an
ordinary tensor product of separately existentially closed kernels describes
gluing. The correct operation is

    exists x. (f(x) and g(x)),

or, for counting,

    sum_x f(x) g(x).

The common x is an intentional exported correlation, not a collision to
alpha-rename away. Internal binder names may be freshened while exported
names remain fixed.

For f=g=1 on q values, shared gluing has q assignments, whereas independent
fresh copies have q^2. This is the smallest multiplicity test for the proposed
copying semantics. Physical copies of syntax do not decide whether a semantic
parameter is copied with equality or freshly quantified; the interface must.

Consequence: valid closed proof/certificate objects need not form a Hopf
subalgebra under a forest product that identifies shared names. Keep all raw
objects and evaluate incompatible combinations to zero, or use explicitly
boundary-indexed matching products. Do not delete CK cuts.

## 3. Exact live-variable condition

Let a finite constraint network have atoms assigned once to proof nodes.
Let V be its variable universe and Inc(x) the nonempty set of node occurrences
whose atoms mention x. Explicitly designate any externally observable variables.
For a rootward ideal I of nodes define

    B_I = {x : Inc(x) meets I and its complement},

with observable variables retained as long as their observation requires.
Variables with empty incidence must either be excluded from counted certificate
assignments or have an explicit allocated introduction/observation site. Leaving
this convention unspecified changes certificate counts.

For I subset J, a region kernel sums assignments to variables internal to J\I,
conditional on assignments to B_I and B_J. It must include identity equalities
on B_I intersection B_J even when no atom in J\I mentions that variable.

This handles nonconsecutive usage: if x occurs in an early and a late region,
it stays live across every intermediate separator. A boundary built only from
adjacent rules would forget x and permit incompatible later choices.

### Composition proof

For I subset J subset K, expand the matrix product over assignments on B_J.
Every variable is in exactly one of these roles:

* it survives at the external boundary B_I union B_K, so equality propagation
  identifies all its appearances with the specified external value;
* it is internal to K\I and lies in B_J, so the matrix sum quantifies it once;
* it is internal to one of J\I or K\J and not in B_J, so that region sum
  quantifies it once;
* it lies outside the region and is irrelevant to this kernel.

Global liveness excludes an extra disappearing-and-reappearing case. Local
atom ownership excludes duplicated or lost factors. Distributivity and finite
Fubini now give K_(I,K) = K_(J,K) composed with K_(I,J), with the convention
that kernels act in rootward-ideal growth order. This works over any commutative
semiring for finite domains; Boolean existential composition needs no finite
domain when arbitrary joins are interpreted relationally.

For sibling factors use joint kernels on the shared boundary, not independent
closure. The proof is invariant under reordering independent finite products.

## 4. Compact connectivity summaries are legitimate but have a limit

For equality constraints with unary forced labels, consistency is summarized
by the induced partition of live ports and the forced label of each block.
An internal inconsistent component maps to zero. A closed consistent component
can then be forgotten for Boolean feasibility.

For counting over a q-element label set, every closed unforced component
contributes q; every closed forced component contributes 1. Therefore the
partition alone is insufficient. An additional weight q^k, or the corresponding
formal semiring weight, corrects this. This is not a small technicality:
forgetting an unconstrained closed component conflates q different certificates.

Eliminating a port before its final future attachment also loses information.
Example: a piece forces x=0; forgetting x yields true. A later piece forces x=1.
The original union is false, but gluing the prematurely closed summary gives
true. Correct live-port discipline avoids this example and proves nested
coherence rather than merely testing it.

This summary does not hide the interior certificate. Paths of arbitrarily
different lengths with the same live-port connectivity induce equal summaries.
The full proof remains the syntax coordinate, so omitted internal structure is
still available for subsequent native cuts.

## 5. Substitution congruence is not a coalgebra congruence

A minimal general example uses undecorated rooted ladders l_1 and l_2. Give both
the same trivial boundary signature s and extend the summary multiplicatively
to forests. In ordinary CK,

    Delta(l_1) = l_1 tensor 1 + 1 tensor l_1,
    Delta(l_2) = l_2 tensor 1 + 1 tensor l_2 + l_1 tensor l_1.

After mapping both trees to s, the two right sides differ by s tensor s.
Hence no coproduct on this summary quotient makes that projection a coalgebra
map over a nonzero coefficient ring in this example.

The same mechanism affects any proposed summary which erases arbitrarily
many neutral interior stages. It is not a counterexample to using summaries
as CK coefficients, and it does not show that all semantic quotients fail.
It shows that contextual equivalence alone supplies no Hopf-ideal theorem.

## 6. What can be asserted about a comodule

A complete decorated witness can restrict to every cut, provided each local
atom is allocated once and each crossing reference is retained as a live port.
Two-stage restrictions are independent of order: their regions are the same
physical node partition, local atoms retain the same owners, and their final
port equalities refer to the same global variable names. This gives an exact
cut-flag reindexing at the decorated-witness level.

To call this an ordinary H-comodule, one must additionally identify the
coefficient object and tensor product in which shared ports live. If detached
factors export correlated variables, they are not independently closed scalar
coefficients. A safe initial statement is the cut-indexed kernel composition
law with a specified joint boundary assignment. Linearization can follow after
that target has been defined. Merely writing rho=(Delta,signature) does not
supply a coaction equation.

The scalar projection which forgets constraints is ordinary CK. The enriched
construction adds coefficient semantics without pruning the underlying cuts.
This is a productive route to all-frontier verification, incremental reuse,
and exact copy-sensitive counts. Whether a particular full LQ revival obeys
these local constraint hypotheses remains a separate proof-theoretic theorem.

## 7. Remaining source-specific obligations

* Lang certificates include routing, ownership and checkpoint constraints,
  not only equality graphs. These must be compiled to local atoms with finite
  state or retained relational ports; equality consistency alone is insufficient.
* An assignment-level gluing theorem need not reconstruct the exact revival
  derivation. Sound proof reconstruction and its staged coherence need proof.
* Copying introduces a map on variable supports: external diagonal sharing and
  internally fresh components must be distinguished occurrence by occurrence.
* Native coefficients omit some trivial edge factors. Typed identity kernels
  must remain in the boundary state even if their positive forest factor is 1.
* The full theorem should quantify over all addressed cut flags, not only one
  nested factor or finite agreement on selected frontiers.

## 8. Assessment

The framework has passed a substantive feasibility check: global certificate
constraints can be composed exactly over all full cut flags without pretending
that local feasibility is independent. The shared-name and live-port rules
are sufficient constructive corrections for the minimal obstructions above.

This is not yet a theorem that arbitrary revivable proofs form a Hopf algebra,
nor a proof of full analytic reconstruction. Those stronger claims are not
needed to establish the worthwhile intermediate theorem: the full CK syntax
admits exact boundary-sensitive kernel interpretations whose convolution
retains occurrence multiplicity and whose staged composition is associative.

## 9. Independent finite falsification attempt

`python3 hopf_research/check_adversarial_kernels.py` passed:

* all 512 networks of three atom locations drawn from eight nullary, unary,
  equality, disequality and explicitly free-variable atoms;
* all 32,768 triples of nested node subsets, including all cut-induced triples;
* 512 independent full-assignment counts compared with empty-to-full kernels;
* explicit identity propagation through a variable-free middle region;
* inconsistent sibling constraints and shared/fresh copy counts 2 versus 4.

This deliberately tests arbitrary node subsets, a superset of rootward ideals.
It validates the constraint-kernel mechanism, not native CK cut multiplicities,
Lang revival, or a proof of the universal theorem.

## 10. Independent migration and Hopf-sensitivity audit

### Canonical typed migration fixture

The `w/r`-wrapped fixture in `migration_algebra.md` Section 7 is well typed.
Its two source processes both have result E. With Y=K→B, the new channel b
has X→Y in the first process and Y→X in the second, exactly the Lin session
roles. The source contexts contain no extra a occurrences, so the displayed
channel uses are rightmost. Taking a active and b fresh inactive meets the
inspected Table 3 cross-reduction side conditions. This is a concrete instance
of the source reduction schema, not merely a type-preserving arbitrary rewrite.

I independently calculated the canonical cut recurrences, using unary channel
application and binary ordinary application:

    source left process:  15
    source right process: 29
    source session:       1 + 15*29 = 436

    target first adapted process: 8 + 9z
    target first session: z + 29(8+9z) = 232 + 262z
    target second adapted process: 16 + 17z
    target second session: z + 15(16+17z) = 240 + 256z

The outer b binder has no free b requirement at its own root. Hence

    Q_target = 1 + (232+262z)(240+256z)
             = 55681 + 122272z + 67072z^2.

The coefficients sum to 245025. These are frontiers, not communications.
The root contributes 1 rather than z, while interior closures can expose b.
This independently validates the reported coefficient arithmetic.

### Context-sensitive substitution separator

For P1=pair(x,lambda h.g) and P2=pair(g,lambda h.x), both old summaries are 7.
Let R=chan(b,y), so Q_R=2+z. The one-hole context maps are

    F1(X)=z+3X,
    F2(X)=z+2(z+X)=3z+2X.

Therefore Q_(P1[R/x])=6+4z and Q_(P2[R/x])=4+5z. Both the typing and the
claimed equality of source interfaces/inventories are correct. The separator
is a substantive reason to retain occurrence-position context information;
a source spectrum plus the number of occurrences is insufficient.

The general one-hole transfer is affine in Q_P *conditional on D(P)*. Its
constant part can depend on D(P), since selecting an enclosing template node
exposes dependencies inherited from P. The product coefficient multiplying
Q_P comes from sibling spectra and is independent of P. Stated this way, the
context-sensitivity theorem is correct; dropping the interface parameter would
make it false around binders.

### Logarithmic derivative and single-cut consequence

In `hopf_consequences.md`, with a commutative coefficient ring A and
left-comodule convention rho:M→H tensor M, the order

    U_phi U_psi = U_(phi * psi)

is correct. Thus gamma=phi' * phi^{-1} gives C'=U_gamma C. Expanding
multiplicativity of Delta and differentiating the character identity proves
that gamma annihilates a product of two positive forest components. Therefore
only one-subtree cuts, including the whole-root cut, survive in the displayed
sensitivity equation. No cocommutativity or division by factorials is needed.

The corolla's antipode and finite-update formulas also check algebraically:

    S(t) = -t + a b_L + a b_R - a^2 r,
    beta(t) = -d(u_L+u_R)-d^2 y.

Substitution cancels exactly to

    C_psi(t)-C_phi(t)=d(B_L+B_R)+(2xd+d^2)R.

The signed connected coefficient already includes the interaction corrections;
it must not be interpreted as permission to ignore coordinated replacements.

### Two qualifications sent to the revival author

1. Equal fragment kernels preserve the enclosing certificate count, but not
   the enumeration of cuts *inside* replaced fragments. Any assertion that D5
   replacement works 'for all frontiers' must specify matching exterior/opaque
   frontiers or retain the fragment's own CK spectrum separately.
2. Arbitrary cut-dependent weights do not automatically preserve convolution
   associativity. Products of weights must agree on corresponding two-stage
   cut flags (a cocycle condition), or arise multiplicatively from the regional
   assignments so that this equality follows by construction.

These qualifications do not undermine the positive kernel-composition theorem.
They prevent it from being silently strengthened into an unproved coalgebra
quotient or an unrestricted weighted-cut construction.

## 11. Constructive strengthening: count ownership certificates without colour inflation

Independent source inspection confirmed that Definition 5 imposes no coverage
or nonemptiness requirement on owner groups. Collapse the mandatory L_i~R_i
pair to one owner variable i. An empty initial assigned to L_i and R_j adds
the equality i=j; a one-sided initial forces its chosen owner's variable.

For a fixed legal owner map omega, let k(omega) count connected components
with no forced variable label. Set

    Rev_T(q) = sum_(consistent, correctly routed omega) q^k(omega).

The checkpoint condition is included in 'correctly routed' here. Then

    Rev_T(1) = number of raw Definition-5 ownership witnesses.

This is formal polynomial evaluation after distinct forced labels and clashes
have been retained. It does NOT map different forced variable names to the
same one-element domain. For actual palette interpretation, the palette must
contain every forced variable; but no such restriction applies to evaluating
this already constructed polynomial at 1.

This gives a practical count which does not inflate the result by arbitrary
choices of fresh variables used to revive unconstrained components.

### Symbolic partition-state algorithm

Let E be the ordered set of ancestor-owner ports active at a proof subtree.
Use a table whose states are partitions of E with at most one forced variable
label per block, and whose values are polynomials in N[q]. Routing roles and
checkpoint bits are obtained from the literal ancestor path.

* Ordinary initial: the identity partition with coefficient 1.
* One-sided ghost initial: sum the state forcing i to p over each permitted
  owner i. Different owner choices add independently, even when summaries agree.
* Empty ghost initial: sum the equality state joining i and j over each allowed
  left/right owner pair. Its own empty succedent satisfies the checkpoint.
* Ordinary inference: multiply its child tables by joining partitions and
  pooling forced labels, discarding conflicting joins. Polynomial weights
  multiply; different decompositions add.
* Ghost-disjunction owner i: both child tables have boundary E union {i}, with
  the same physical owner i and opposite branch roles. Join them there, then
  eliminate i. If its block contains another boundary port, retain the induced
  block and forced label. If the entire block closes, multiply by q when
  unforced and by 1 when forced.

The crucial distinction from independent child closure is that i is shared
before elimination. Every hidden unforced component is counted exactly once,
when its last surviving owner port disappears.

### Exactness proof

Induct on the proof tree. Expand the table as a formal sum over all ghost-leaf
owner choices inside the subtree. The boundary partition records precisely
the equalities induced among still-active owners, and each forced block records
precisely its required variable. The coefficient q^k counts precisely those
unforced connected components completely internal to the subtree. Each leaf
rule gives this invariant directly. Ordinary inference takes the Cartesian
product of choices; partition join computes their combined equalities, and
conflict rejection is exact. At an owner node, all references to its own port
are in its descendant branches. Therefore forgetting it loses no future
attachment. The closure factor is exactly the one newly completed component,
if any. At the root no owner ports remain, so the unique empty-boundary table
entry is Rev_T(q). This proves the algorithm universally at the certificate
level.

Let g bound the number of active owners and r be the number of distinct forced
labels. There are at most Bell(g)(r+1)^g boundary states, a conservative bound.
Polynomial degree is at most the number of owners. This gives a finite symbolic
algorithm parameterized by boundary width, not a globally finite-state calculus.
Naive joins of child tables may require quadratic or higher products in their
state counts; no unproved linear-time bound is asserted.

The existing all-cut kernel theorem justifies caching these tables at arbitrary
full CK frontiers. Equality of tables preserves the exterior certificate count;
the full syntax remains available to enumerate cuts inside a replacement.

## 12. Revival compiler audit and compact-interface repair

### C1: ordinary LJ adapters

I inspected Lang Figure 1, not merely its prose. Its implication-left rule has
shared antecedent Γ in both premises and conclusion; conjunction-right and
disjunction-left likewise share Γ. Therefore the compiler's common-token-bag
padding is a literal instance of the stated source presentation. Implication-
right and negation-right discharge an original source principal occurrence;
new marked tokens remain background assumptions. Formula equality does not
identify these physical occurrences. Original weakening/contraction can also
act on its designated original occurrence while tokens remain background.

If native LJ instead uses split contexts for implication-left or other binary
rules, the exact adapter changes: pad both premises, apply the split rule,
then contract duplicated added-context occurrences in the conclusion. This is
still cutfree and uses each child proof once, but introduces extra contractions.
Any contraction-free fragment claim must retain the shared-context hypothesis.

Multiple raw right tokens at one checkpoint cause no obstruction. Each macro
p⇒[empty] to ⇒¬p to ¬¬p⇒[empty], with the other assumptions retained, restores
an empty succedent, so a deterministic sequence converts all marked tokens.
At an owner, discharge its own tokens before treating its conclusion as a
checkpoint for external owners. This excludes the forbidden endpoint exactly.

Thus C1 is sound for the explicitly fixed shared-context LJ presentation.
It is not yet a theorem about an unspecified native rule registry.

### C2: fixed source cuts

With every source node decorated by its inherited deterministic proof macro,
each child proof hole occurs exactly once. Restricting that macro assignment
to source cut pieces and then refilling consequently yields literally the same
compiled tree by substitution associativity. New cuts strictly inside inserted
macros are extra target cuts and are not images of source cuts. The stated
C2 restriction to macro-boundary images correctly avoids a false Hopf-morphism
claim. All source cuts, including cuts through pending obligations, remain.

### Gap found in replacement claims

Compact certificate kernels can identify fragments with different compiled
marked bags. One versus two left ghost tokens for the same owner give the same
forced-colour constraint but produce one versus two ¬p assumptions. Different
internal-owner populations also produce different terminal WEM assumption bags.
Therefore C2 by itself establishes fixed-source compilation/refill, not literal
plugging of every equal-kernel cached implementation.

### Positive canonical interface theorem

The following correction was proposed independently in discussion with the
revival author and has passed this audit. Fix a finite palette A containing all
forced and selected owner colours. Let W(A) contain one WEM formula for each
colour in A. At a source edge with active owners E and aggregate pending-right-
debt state d, use the canonical compiled antecedent extension

    W(A)
    + one ¬c_g for each active left-role owner g
    + one ¬¬c_g for each active right-role owner g
    + one c_g for each active right-role owner with d(g)=true.

Keep equal-colour owner occurrences physically marked until erasure. The
compiled interface depends on the sequent, scope/colours and aggregate debt,
not on the number of leaves assigned to an owner or internal owner population.

Construction: contract equal-phase multiplicities; weaken to supply absent
canonical left/double-negated assumptions and all W(A). Raw assumptions are
kept exactly when a witness has an unmet right-path debt. At a shared-context
branch, pad the union of child raw-debt states, taking OR. At an empty checkpoint,
convert raw to double negation and contract the duplicate canonical double
negation. At an owner, its own right debt is false by certificate legality;
apply disjunction-left to its canonical left/right assumptions and contract
the produced W(c_g) into W(A). Process any empty owner conclusion only afterward
for external owners.

Proof is by the same node induction as C1. Padding creates proof occurrences,
not new logical routing obligations. Contracting several raw tokens at one
boundary is legitimate because their remaining path to the same owner is the
same and they all lack a checkpoint so far. All constructors use their premise
proofs once, and all new proof operations are left weakening/contraction or
explicit negation/disjunction inferences.

At the root the resulting ordinary LJ proof has conclusion Γ,W(A)⇒Δ. Every
W(A) assumption is valid in LQ. If normalization to these canonical interfaces
is built into every node macro, C2 remains literal on source cuts. If performed
only at selected cut boundaries, the comparison must instead record the extra
structural adapters; literal equality then need not hold.

This is a genuine positive D3/D5 improvement: compact boundary-state kernels
can now index plug-compatible proof-producing cache entries, provided each
entry supplies an actual source witness and the corresponding canonical
compiled proof. Kernel equality still does not invent that witness, nor does
it make differing interiors have identical CK cut spectra.

## 13. Polynomial carrier, Green sums and full context packet audit

The quotient by standalone edge generators e_i−1 is a homogeneous biideal;
its quotient has degree-zero ring and a connected grading by positive nodes.
The antipode recursion is valid without finite-dimensional graded pieces.
Applying the quotient only on the first coproduct leg leaves the second-leg
basis edge e_i intact, so the typed-hole coaction does not reproduce the old
Box/unit mistake. Embedded typed edges are data of positive tree generators.

Concrete-colour ancestor stacks preserve correlation: each owner constructor
chooses its colour once and puts that same value in both premise states.
De Bruijn positions designate the same physical ancestor after grafting at an
exact matching state. Different physical owners with identical colour/role
stacks need not be textually named to enforce these already-fixed colour
constraints. A native rigid-ID comparison must nevertheless exhibit the map
from physical owner occurrences to ancestor positions; local P-tree equality
is not asserted to be native literal equality without that bridge.

The full Green identity, leaf-profile identity and closed-input specialization
are exact grafting/cut bijections. A fixed remainder has finitely many physical
leaves, so it has only finitely many assignments of a fixed crown forest to
those leaves. Formal basiswise coefficients are therefore locally finite.
Numerical total counts still need the separately stated local-finiteness and
positive-node parameter; a finite palette by itself does not provide them.
The character composition order with pruning first is correctly f then g in
convolution and F^g(F^f(x)) in substitution.

For the one-hole context packet identity, I checked all endpoint cases:
identity context, Box payload, Box side sibling, selected outermost ancestor,
and no selected spine node. The stated disjoint decomposition is exhaustive.
Consequently δG_C=L_Cδ+A_C and the context composition law

    A_(CD)=L_C A_D + A_C G_D

hold with the displayed operator order. The triangular representation preserves
the graph of δ exactly. Its scalar affine transfer is the image of that full
packet theorem. Multi-hole linearization is multilinear on *physical* payload
slots; sharing a choice of source proof among several slots uses a basis
diagonal, as distinguished in the note. None of these equations requires a
primitive-to-macro Hopf morphism.

Nested template installation coherence concerns alternative staged presentations
of one final cut. The general three-region iterated-coproduct cut-flag theorem
is a separate underlying law, supplied elsewhere. These related bijections
should not be conflated merely because both use three layers.

## 14. Cost and claim ledger for the final account

**Exact structural debt.** Marked-compiler W/C costs attach to source nodes with
their inherited occurrence-sensitive token interfaces. They are additive over
full vertex partitions, including arbitrary CK flags. Identity seam propagation
costs zero; a future discharge is charged at its actual owner, not at extraction.
For arbitrary replacement, the matched interfaces must carry enough token
multiplicity to calculate these future costs. Colour partitions plus aggregate
debt alone do not retain that information. The canonical compiler has a
different structural cost and needs its own accounting.

**The 21→11 reuse score.** When reported as retained source-rule work, this is
a source-skeleton accounting result under the stated cache-cost model. It is
not a reduction from 21 to 11 nodes in the ordinary compiled proof, not a
runtime measurement, and not a lower bound on checking or normalization time.
The marked 21-node source fixture instead compiles to 29 ordinary rule nodes;
the canonical compiler deliberately spends additional structural rules.

**What is being counted.** A physical cut, a cache replacement plan, a raw
Definition-5 ownership witness, a colour-decorated witness, and a revived LJ
proof are different objects. Their counts must keep different labels. In
particular the WEM fixture has Rev(q)=q+3, hence four raw certificates and five
colour-decorated certificates over a two-atom palette; neither statement says
there are four or five possible ordinary LJ proof terms.

| Item | Correct status |
|---|---|
| Lang's certificate criterion and LQ soundness | Source results, not rediscovered theorems |
| Scoped local certificate polynomial grammar | New explicit application with paper bijection proof |
| P-tree bialgebra, edge quotient, Green/Faà identities | Established general machinery instantiated and checked on this grammar |
| Exact ownership partition solver | New exact project algorithm; constituent partition algorithms are standard |
| Equal-inventory LQ separator | New concrete validated fixture for this observer |
| Marked C1 revival | Detailed constructive development of Lang's sketch; not new LQ soundness |
| C2 source-cut compiler/refill | Explicit compiler bridge, using standard substitution associativity |
| Canonical C4 cache interface | New constructive repair of a genuine compact-kernel/proof-type gap |
| Marked structural debt formula | New exact accounting for this compiler, not optimality over compilers |
| Cache character action and antipode rebase | Standard Hopf action instantiated with correlated certificate coefficients |
| Connected logarithmic sensitivity | Standard infinitesimal-character mechanism, new useful observer interpretation |
| Full context packet/cocycle presentation | Explicit organization of existing cut/fill geometry; no literature-novelty claim |
| Typed Lin spectrum/context separator | New operationally grounded project calculation and abstraction separator |
| Budgeted migration benchmark | Exact result in a declared synthetic analysis model, not measured speedup |
| Lean/native POTKIN3 bridge | Still unimplemented in this workspace |

All universal constructions in this record are paper-level arguments.
Executable finite checks are supplementary falsification attempts. No Lean
kernel verification, native registry equivalence, global new cut-elimination
result, unrestricted substructural transfer, or research-literature priority
claim follows from those checks.

## 15. Final audit: counit lifts the context operad on arbitrary records

The sharpened result in `context_coaction.md` Sections 9–10 passes an
independent algebraic audit. Set `e = epsilon_H tensor id`. The identity
`e L_C = G_C e` holds on arbitrary basis records: every nonempty sibling
pruning forest has positive degree, so the counit selects exactly the unique
all-empty sibling-cut family. Likewise `e A_C = 0`, since an ancestor-selected
packet always has a positive spine factor. No assumption that the input lies
in the image of the coaction is used.

Expanding `(L_C + A_C e)(L_D + A_D e)`, the last cross term vanishes by
`e A_D = 0`, while the other terms are
`L_CD + (L_C A_D + A_C G_D)e = K_CD`. Thus the direct action really holds
on the entire free extraction-certificate module. The identity
`delta G_C = K_C delta` follows separately from the coaction counit.

For a single typed rule, the two-term operation stated in Section 10 is
multilinear in the distinct input slots. Its counit is the ordinary rule
operation on counit-projected inputs; its value on input coactions is the
output coaction. Composition in the free typed linear-tree operad therefore
establishes the asserted multi-hole action on arbitrary tensor records.
Equivalently, the masking proof classifies each final template antichain and
uses the counit precisely at swallowed slots. This remains valid for signed
linear combinations; no positivity hypothesis on arbitrary records is needed.

The correct positive conclusion is an explicit representation of typed linear
contexts on extraction certificates, with delta an intertwiner. It is neither
H-linearity, an unchanged-coefficient comodule morphism, nor a general monad
distributive law. Scalar compression remains a further theorem. This direct
K-action should be an explicit Lean target after the native packet equivalence.

## 16. Final audit: debt grammar, inverse ghostification, and spanning Cut

The bottom-up debt grammar matches the canonical compiler's boundary state.
An owner must test its own right debt before its conclusion is allowed to
clear older owners' debts; otherwise a false certificate is accepted. Empty
ghost leaves create and immediately clear the required obligation. Closed
annotation is unique, but formal open Box states need not be inhabitable.
A reusable cache must supply witnesses for the states it advertises.

The inverse ghostification theorem requires occurrence-designated root WEM
assumptions, atomic identities or preceding identity expansion, and the stated
ordinary LJ ancestry property. Marks follow formula occurrences, not equal
formula text. Under those assumptions erasure and dummy suppression preserve
the required empty checkpoint and leave only endsequent subformulas. This is
a concrete reconstruction of a fresh certificate, not preservation of the
old routing or a claim that normalization commutes with CK extraction.

The stronger G2 Cut adapter also passes. For split-context Cut, the compiler
cuts the two original B occurrences while concatenating the premise token
bags. Physical token births are in disjoint premise subtrees even if some
tokens share an owner, so no additional weakening or contraction is required.
A scheduled checkpoint at the Cut conclusion is performed after the replayed
Cut. Premises need not be independently grounded. The universal relative
normalization theorem remains conditional on an ordinary LJ Cut eliminator
that preserves the root sequent and on any needed identity expansion. The
10→13→11→8 example implements only an identity-Cut reduction.

## 17. Final reader audit of deliverables

The research report correctly distinguishes the abstract all-positive carrier
from native material eligibility; fixed-palette canonical boundaries from
marked occurrence-sensitive cost; source residual work from compiled proof
size or runtime; and conditional base normalization from a newly implemented
general eliminator. Its literature wording explicitly avoids a priority claim
or attributing CK cuts to Lang/Ciabattoni–Genco.

The generic 2-system theorem is a representation theorem for explicitly
parameter-instantiated, owner-scoped derivations. Its claimed bijection is
sound at that level, including repeated tops and varying occurrence-local
contexts. It neither reconstructs unique instance parameters from an
unannotated tree nor proves a hypersequent translation or analyticity merely
from polynomial packaging.

The final mechanization prompt should include K_C and its arbitrary-record
composition law in addition to the affine precursor. All proposed native
claims remain targets to prove or refute. No new Lean result is certified by
this audit.
