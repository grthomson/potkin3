# A compiler-aligned polynomial grammar using pending checkpoint debt

12 October 2026. Paper proof; not Lean checked. This alternate polynomial
presentation P_A^debt replaces the top-down `seen` bit of
`polynomial_bridge.md` with the bottom-up aggregate pending bit required by
the canonical revival interface in Theorem C4 of `revival_compiler.md`.

## 1. State convention

Fix a finite nonempty palette A containing all forced atom labels. A state is

    i = (S, E, d),

where S is a literal source sequent, E is its ordered stack of strict ancestor
ghost-disjunction owners with colours and LEFT/RIGHT branch roles, and d is
a subset of the RIGHT entries of E. Membership i in d means: some physical
right-assigned ghost leaf inside this subtree is assigned to that external
owner and has encountered no empty-succedent checkpoint inside the subtree,
including its current root sequent. The empty-checkpoint processing has
already happened at the output boundary.

The entries of E are canonical scope positions, not interchangeable textual
names. Individual ghost-leaf owner choices remain part of the rule labels.
The debt subset aggregates only their pending checkpoint requirement; it does
not identify their physical occurrences or erase their multiplicities.

Write clear_S(d) for the empty set if S has empty succedent and for d otherwise.

## 2. Local constructors

Each constructor includes its literal source rule instance and all input and
output states satisfying the following equations. Thus this is a local
relational typing condition, not a claim that child states are determined
top-down by the output state.

**Ordinary initial rule.** Its output debt is empty.

**Ghost initial p=>.** Select a LEFT entry i of E whose colour is p. Its output
debt is empty. The selected de Bruijn index remains in the constructor label.

**Ghost initial =>p.** Select a RIGHT entry i of E whose colour is p. Its
output debt is {i}. The nonempty succedent supplies no checkpoint at this node.

**Ghost initial =>.** Select a LEFT entry i and RIGHT entry j with equal
colours. The raw right obligation {j} is created, then this node's own empty
succedent clears it. The output debt is therefore empty. The selected pair
remains in the label; clearing its debt does not erase the certificate choice
or permit the compiler to discard the temporary raw formula before the
empty-node conversion macro.

**Ordinary inference.** All child states have the same E and the literal
premise sequents. If their debts are d_1,...,d_m, the output is

    d = clear_S(d_1 union ... union d_m).

For a zero-premise ordinary rule, this agrees with the initial-rule case.

**Ghost-disjunction owner.** Choose one colour a, shared by both premises.
The left child extends E by a new LEFT entry (a,L); the right extends it by
a corresponding RIGHT entry (a,R). Let their output debts be d_L,d_R.
First require the new owner's RIGHT entry to be absent from d_R. Its LEFT
entry cannot occur in d_L, because debt is only defined on RIGHT entries.
Delete the own entries, identify the inherited E positions, and set

    d = clear_S((d_L restricted to E) union (d_R restricted to E)).

The own-right rejection happens before processing the owner's conclusion S.
Consequently that conclusion cannot satisfy its own checkpoint requirement.
It may clear the requirements of older, external owners after this discharge.

These constructors keep every source rule node and every physical premise
slot. They add no proof node merely to record a bit.

## 3. Exactness and unique annotation

**Theorem.** For a fixed literal ghost-rule tree, fixed correctly routed owner
assignment, and fixed compatible owner colouring, there is at most one debt
annotation satisfying the local laws. For a closed source at an empty-stack
root, such an annotation exists exactly when every right-assigned leaf has
the Lang Definition-5 checkpoint on its path to the owner, including the
leaf sequent and excluding the owner's conclusion. Hence closed P_A^debt trees biject the same pairs
(Definition-5 certificate, compatible owner colouring) as the earlier
top-down P_A presentation.

**Proof.** The leaf debts are prescribed. Every ordinary output debt is a
specified function of child debts. At an owner, output debt is also specified
once its admissibility test succeeds. Thus structural induction proves
uniqueness.

For existence and the checkpoint criterion, maintain the invariant that an
external owner belongs to the output debt exactly when some right-assigned
leaf for that owner below the current boundary has seen no empty-succedent
node along its path through the subtree. A right leaf creates precisely that
obligation. Branching takes the union of such leaf sets, represented by OR.
An empty source conclusion lies on every path passing through the node and
therefore clears all those obligations. At an owner the paths of its own
right leaves terminate: they are all successful precisely when its own entry
is absent before clearing at the owner's conclusion. Removing the owner
then leaves exactly the external obligations. This proves the invariant and
equivalence to the specified path condition by induction. The colour and
routing tests are the unchanged local tests of the previous grammar. QED.

This adds no multiplicity to certificate counts. Different debt assignments
are not independent choices on a closed decorated source; there is one or
none. Unused owners still contribute their colour choices at owner nodes,
and different physical leaf assignments remain distinct labels.

## 4. Open fragments and full CK cuts

A zero-node edge of state (S,E,d) is an assumed open module with exactly that
boundary obligation. Its debt can be any declared subset of external RIGHT
owners. An open tree's output debt is uniquely determined once its literal
rule/assignment/colour labels and the debts at all its open inputs are fixed,
provided every internal owner test succeeds.
Not every abstract hole type is realised by a closed positive module. For
example, a realised positive module with empty source succedent always has
empty output debt after its root's processing. Zero-node edges are formal
assumptions, not extra source sequent occurrences that themselves perform
checkpoint clearing; a cache entry must supply an actually realised type.

Cutting a closed decorated source exposes its already computed local states.
Each detached component and each hole in the remainder retains the same
(S,E,d) interface on its side of the seam. Cutting again does not recompute
the external scope as empty or replace the debt by a top-down checkpoint bit.
Thus arbitrary full positive-node cuts and nested cut flags remain locally
typed. A replacement with the same boundary type has the same external
pending obligations, even if it has different numbers of assigned leaves.

Let I be these debt states, B the compatible local constructors, and E' their
physical premise slots. The diagram I<-E'->B->I is again finitary. Its full
P-tree bialgebra, connected quotient H=B_P/(e_i-1), typed remainder coaction,
McBride context types, and Green/Faà di Bruno identities follow exactly as in
`polynomial_bridge.md`. The state type e_i remains distinct in the comodule.
Only standalone trivial coefficient factors become the algebraic unit.

## 5. Exact alignment with the canonical compiler

For state (S,E,d), Theorem C4's canonical compiled antecedent adds:

* one WEM formula for each atom in A;
* one marked negated colour for each LEFT owner in E;
* one marked double-negated colour for each RIGHT owner in E;
* one marked raw colour for each RIGHT owner belonging to d.

This now depends on precisely the P_A^debt state. Ordinary inference union and
empty-node clearing are the compiler's padding/replay and negation-conversion
steps. The owner constructor's own-right test is the compiler's precondition
for using the two own principal formulas in disjunction-left. Older external
debt is processed only afterward. Therefore the polynomial grammar and the
canonical compiler use the same seam type; no conversion between unrelated
bit meanings is being assumed.

This is an interface-alignment theorem, not a statement that the compiler is
a Hopf morphism. Its expanded LJ macros contain additional positive vertices
and hence additional CK cuts. Full expansion-fibre accounting remains separate.
It also does not identify the canonical compiler's padded W/C cost with the
cost of the more provenance-sensitive marked compiler.

## 6. Relationship with the top-down presentation

The two bits have opposite information directions. At a boundary, `seen_i`
records a checkpoint on the ancestor side (strictly after owner, strictly
before the current node), while `d_i` records a pending descendant obligation
after processing the current node. For an external RIGHT owner, all its
assigned descendants satisfy the complete path condition exactly when

    d_i implies seen_i.

If d_i is false, every corresponding leaf already found a checkpoint inside
the fragment. If it is true, its pending leaves require the ancestor-side
checkpoint. This is a compatibility relation between the two interfaces,
not an equation between their bits.

For closed decorated sources both presentations give unique annotations of
the same certificate objects. Their arbitrary open-state types are different,
so no naive identity of the two open polynomial signatures or their Green
coefficients is claimed. P_A^debt is the preferable presentation when the
purpose is canonical compiled proof replacement; P_A^seen remains useful for
top-down certificate enumeration against an inherited path environment.
