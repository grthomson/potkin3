# Exact inverse geometry and finite residual for the typed CK coaction

11 October 2026. Addendum to carrier_audit.md. This theorem concerns the genuine typed coaction lambda=(q tensor id)Delta_B, not the ordinary untyped CK inverse relation and not only a fixed list of designated active holes.

## 1. Exact inverse-cut theorem

Use finite ordered rule trees with typed edge residues e_s as in the carrier audit. A remainder R is a forest of such trees, so even whole extracted components leave a typed root-edge component in R.

For each leaf-edge occurrence h of R, independently choose one of:

* leave that edge e_s unchanged;
* replace it with a positive typed tree T_h of output s (possibly itself containing open typed leaves).

Let T be the resulting assembled forest. Let P be the ordered list of all chosen positive T_h, in the left-to-right order of the leaf occurrences; unchanged edges contribute no component to P.

**Theorem.** The coefficient of P tensor R in lambda(T) is nonzero exactly when such a leaf assignment exists. With the material projection rho_M, the additional condition is that each positive T_h has all its rule vertices in L.

**Proof, forward.** A cut of a P-tree is a root-containing arity-preserving subtree R. Every leaf h of R roots an ideal subtree in T. If that ideal subtree is the trivial edge, h was an inherited open leaf. Otherwise it is precisely a positive extracted provider. The coproduct lists all ideal subtrees in leaf order; q removes exactly the trivial components. Thus T is recovered by the stated assignment and its surviving coefficient list is P. The argument is componentwise for forests.

**Proof, reverse.** Regard the displayed copy of R in the assembly T as a root subtree; all its retained rule vertices preserve their original ports. Its frontier ideal trees are exactly the chosen providers and the unchanged edges. Thus it is a legal typed CK cut, and applying q gives P tensor R. Material purity is checked independently on each positive ideal tree.

There are no arbitrary external gaps. Unlike ordinary connected CK, the uncollapsed right carrier records every original forest root as a positive tree or as a residue e_s. Consequently lambda(T) cannot have empty remainder unless T is the empty forest.

Whole-root extraction is included: for R=e_s, the possible T are e_s itself and every positive tree of output s. In the first case P=1; in the second P=(T). Under rho_M only pure positive trees are allowed.

## 2. Multiplicities, repeated leaves, and exact ports

In the free ordered model a fixed pair (T,R) determines at most one root-preserving arity-preserving subtree embedding. Starting at each root, retained rule labels and fixed port positions force every retained address. At every leaf address of R, the corresponding subtree of T is then forced. Therefore the assignment, cut, and coefficient P are all unique if they exist.

Repeated same-sort leaf edges are separate ordered occurrences. Filling the left versus right hole of r(e_s,e_s) with g produces r(g,e_s) versus r(e_s,g), two different sources. It does not create duplicate witnesses for one exact source/remainder. Filling both with identical g yields one cut with coefficient gg, preserving the two uses.

This coefficient-one statement is specific to the free planar carrier with exact residuals. Passing to commutative forests, quotienting contexts by premise permutations, or applying finite observers can collect several different witnesses and produce multiplicities. The recurrence below is Boolean and intentionally takes existence; it is not a multiplicity-preserving quotient. Native persistent origin names are a further refinement when one needs transport across sources.

For open sources, inherited leaves require no special exception. A positive provider may itself be open. Its inherited leaves remain inside that provider when detached; leaves inherited from R remain in the residual. There is no ability to choose a fictitious positive provider consisting solely of an edge.

## 3. Finite recognizers including open providers

Assume finitely many sorts and finitely many exact rule symbols. Let M be a finite monoid recognizing coefficient forests. To evaluate a positive typed tree before embedding it into M, use finite sorted states A_s, edge constants a_s, ranked rule transitions a_r, and maps i_s:A_s->M. For a positive tree t of output s, its coefficient summary is i_s(alpha_s(t)); a coefficient forest is summarized by the product of its positive-tree summaries. Edge constants are used *inside positive trees*, never as additional coefficient components.

Let the target source property have finite sorted tree states Q_s, constants z_s for e_s, and transitions b_r. An optional finite monoid N with maps j_s:Q_s->N recognizes source forests. This accommodates ordinary finite ranked tree/forest recognizers.

Compute, separately for every output sort s, the finite set

    E_s = {(i_s(alpha_s(t)), beta_s(t)) :
           t is positive, output s, and L-pure}.

Here L is the selected material rule profile, distinct from the finite coefficient monoid M. The computation starts with the paired edge constants (a_s,z_s), closes under simultaneous transitions of material rules, and marks whether the constructed term is positive. Every rule application is positive, including a nullary ground rule. Record the displayed E_s only for positive states; unfilled edges still participate as children. A finite least fixed point terminates. Store predecessor witnesses to synthesize an actual provider for every reached pair.

This is the essential extension beyond an observer defined only on complete proofs. Iterated coactions produce positive open providers, and E_s must include them. A complete-term observer cannot silently be applied to their holes.

## 4. Exact finite inverse recurrence

For a typed remainder tree R of output s, set

    U_s(R) = {(alpha_F(P), beta_s(T)) :
              coefficient of P tensor R in rho_L(T) is positive}.

The inverse-cut theorem gives exactly:

    U_s(e_s) = {(1_M,z_s)} union E_s,

    U_s(r(R_1,...,R_n))
      = {(m_1...m_n, b_r(q_1,...,q_n)) :
          (m_i,q_i) in U_{s_i}(R_i) for every i}.

For n=0 the result is {(1_M,b_r())}. A nullary retained rule has no fillable premise, so it admits no hidden grafting.

For forests, lift tree pairs by (m,q)->(m,j_s(q)), use coordinatewise monoid multiplication, and use the singleton identity {(1_M,1_N)} for the empty forest. There are no E factors inserted between forest components or around retained roots. Inherited edge components already supply their own leaf recurrence.

Proof is structural induction on R. Its leaf case is the whole-root endpoint together with identity filling; its rule step is exactly the independent provider assignment to the ordered frontier below that root. The forest case follows the preserved root-component positions. All provider choices are unbounded in size, but E_s is their exact finite simultaneous image, so no size bound enters the theorem.

Each U_s is a state in the finite powerset of M x Q_s. Rule transitions are the displayed finite operations. Thus the inverse relation has an effective finite recognizer.

## 5. Universal residual, decision, and counterexamples

Let F_A subset M recognize allowed coefficient forests and let F_C subset N recognize good assembled source forests. Accept a remainder state U iff

    for every (m,n) in U, m in F_A implies n in F_C.

This accepts precisely A backslash C for the rho_L action: every assembly whose entire extracted coefficient forest belongs to A satisfies C. It covers arbitrary correlated requirements on the ordered provider tuple to the extent represented by the chosen finite monoid. No independent-per-hole contract assumption is required.

A rejected state supplies an accepting coefficient summary and a bad source summary. Following the finite transition witnesses and stored E_s provider witnesses reconstructs an actual typed assembly violating the contract. Unreachable combinations cannot enter the recurrence, because E_s was computed from simultaneous states of the same provider and every subsequent combination follows an actual rule.

Boolean operations, emptiness, and finite-recognizer inclusion provide a decision procedure for implications between effectively constructed residual assertions. Exponential powerset growth is possible; no polynomial bound is asserted.

## 6. Difference from a fixed designated-hole residual

The lambda residual treats every leaf of R as potentially fillable, including existing open interfaces, and retains the option of leaving each unchanged. A fixed designated-hole contract can instead freeze some leaves, require filling at selected leaves, or restrict their individual providers. Those are different relations and can use analogous recurrences with different leaf clauses.

In particular, a fixed-hole checker does not by itself prove this lambda theorem; the inverse-cut correspondence does. Conversely, a lambda residual is not automatically the exact precondition for a client that freezes selected external assumptions. Its quantification domain is larger unless the assertion/leaf annotations enforce those choices.

## 7. Structural proof theory scope

This closes a genuine typed D4 carrier/recognizability gate: the residual uses the actual CK cut coaction on fixed-arity typed open rule trees and has exact finite witnesses. It is not yet a Cut-elimination theorem or an analytic object calculus derived from these assertions. A separately justified finite registry and logical safety property are needed to turn the compiler into an application.

## 8. Closed-source guards and exact weakest-precondition staging

If only complete assembled proofs are relevant, apply the full coaction residual to
`C = (not Complete) union Safe`. Completeness means absence of proof meta-holes,
not absence of object-language assumptions. It is a regular predicate: an edge
is incomplete and a rule is complete exactly when all its children are complete.
This guard ignores open sources without falsely asserting that restricting the
coaction to complete trees gives a closed coalgebra. Feasibility of at least one
complete admitted assembly must still be checked separately.

Write `A ▷ X` for the existential assertion action from positive coaction support,
and `WP_A(C)` for its right adjoint. Write `A ⋆ B` for coefficient languages
combined by the positive CK coproduct relation, NOT ordinary forest concatenation.
Coassociativity and positivity give

    (A ⋆ B) ▷ X = A ▷ (B ▷ X),
    WP_(A ⋆ B)(C) = WP_B(WP_A(C)).

The reversed order in the second equation follows by taking right adjoints.
This is a law of the full coaction assertion module. Complete-source guards can
be placed in C; independently restricting each intermediate domain requires a
new law and is not licensed by this equation. Finite recognizers are observers,
not a claim that their states themselves carry the coefficient Hopf structure.
