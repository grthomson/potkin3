# Adversarial review: mixed tensor–implication transfer

Date: 2026-10-10. Independent review of `bridge_completion.md`, `finite_modes_theorem.md`, and `tensor_carrier_extension.md`. This is a paper-level transfer review, not a formalization.

## Verdict

The island/core and finite-mode arguments have a credible transfer to unit-free, occurrence-linear tensor–implication. For a *native canonical normal representative*, the main missing obligation would be a complete mixed logical-shell observer with a suitable reifier. The revised theory avoids claiming this: its sparse record K stores exact material islands and the ordinary shell equivalence class. This is sufficient for the abstract core and finite-mode equality theorems, without claiming an effective full mixed canonicalization algorithm. Tensor components do **not** require extra input purity modes under the existing raw-substitution semantics. They require such treatment only if one changes the operation by reducing logical boundaries before observing the resulting material decomposition.

Do not present an executable beta normalizer, finite fixtures, or termination argument as proving completeness for beta/eta plus tensor commuting conversions. That is the genuinely separate mixed-calculus obligation.

## 1. Precise transfer hypotheses

Let the syntax extend the previous terms by ordered Pair and linear tensor elimination `Let P as (x,y) in Q`. Retain these conditions:

1. All selected material constructors have atomic conclusions; all material-origin holes have complete closed atomic interfaces. Ref, Pair, Let, Lam, and App are nonmaterial.
2. Every constructor and conversion uses each resource exactly once. There is no tensor unit, weakening, contraction, or implicit erasure.
3. Material occurrences, internal ports, and named holes remain rigid. Any logical comparison preserves the complete typed context and these marked occurrences.
4. There is a complete observer C for the *declared* mixed beta/eta and commuting-conversion theory. It must be stable under typed substitution and contexts and equivariant under fresh atomic-token renaming.
5. There is a deterministic linear representative R(C(s)) for abstracted shells. It preserves each atomic token and primitive occurrence exactly once. It is connected to s by conversions that preserve absence of selected-only material subtrees.

Under these hypotheses, extraction of maximal islands, shell abstraction, R(C), and restoration through atomic identity seals give the same core reconstruction and exact CK opening arguments as before. One may alternatively use a canonical graph as C, but a graph observer alone does not establish the claimed *native retract representative* without the stated reifier.

Hypothetical primitive discharge requires its own treatment in C/R; an ordinary proof-net theorem for constant symbols should not silently be applied to primitive constructors that bind assumptions.

## 2. Tensor-specific blocker checks

The shell has no pure selected-material subtree after every maximal island and bare origin hole is replaced by a positive Ref token.

For tensor beta

`Let Pair(M,N) as (x,y) in P -> P[M/x,N/y]`,

both M and N are shell subterms, so each contains a nonmaterial blocker. Their linear substitution cannot create a selected-only cone across either seam. A selected-only cone internal to M, N, or P would already contradict the shell invariant.

For tensor eta

`Let P as (x,y) in Pair(x,y) -> P`,

the retained P has tensor type and therefore cannot itself be a material tree or atomic material hole. No material cone is newly created.

In a valid commuting conversion moving a Let through a constructor, its bound resource uses remain explicit Refs in the body. Thus an affected primitive region containing one of these uses remains blocked. Unaffected sibling regions have exactly their old status. The same argument applies when the constructor is Lam/App, provided capture-avoidance and linear splitting conditions are stated. Exchange of independent Lets merely changes logical ancestry.

These checks establish safety of the generators; they do not by themselves establish that a chosen oriented rewrite system is convergent or complete.

**Stronger inventory proof.** In fact the invariant does not depend on the chosen normalization strategy. Every selected nullary primitive occurrence is itself a material cone, so every such occurrence lies in an abstracted maximal island. Every actual origin hole is likewise either inside an abstracted island or separately abstracted. Hence the shell has no selected nullary occurrence and no actual material-origin hole anywhere. Every finite selected-only tree must have leaves of one of those two kinds. A logical equivalence retaining the exact primitive and token occurrence inventory cannot introduce either kind, and therefore cannot introduce a material cone. This proves the required blocker property for any occurrence-faithful reifier equivalent to the shell, not just the displayed contractions. Positive Ref tokens must remain nonmaterial; they are not new material nullary constructors.

## 3. Compound inputs: no extra modes for raw substitution

Suppose z has tensor type A tensor B or implication type A implies B. Any well-typed filler P for z is root-impure because selected material constructors and material-origin holes have atomic conclusions. Replacing the Ref z by P cannot create a raw pure cone spanning the seam, irrespective of how many material islands lie in P. Those islands are abstracted separately; their surrounding mixed shell is inserted by ordinary typed substitution.

Consequently the previous expansion proof requires only pure/impure choices for **atomic entries of the actual outer free context**. Atomic leaves inside a compound type are not raw Ref occurrences at the substitution seam. The same finite formula `Sigma(t)=(Q(t_S))` over atomic outer entries remains appropriate if the mixed C/R hypotheses hold.

For example, z:A tensor B and `Let z as (x,y) in Pair(x,y)` should remain equivalent under every filler. Their equal shells and identical filler islands prove this directly. No independent material modes for the two type leaves are needed.

There is an important boundary: if “installation” is defined to normalize P or the surrounding Let before computing the actual material coaction, this is a different theorem. With selected nullaries delta:a and epsilon:b, the raw installed proof

`Let Pair(delta,epsilon) as (x,y) in r(x,y)`

has four material-cut terms (the subsets of its two leaf islands). Its principal reduct `r(delta,epsilon)` has five, including the new whole composite coefficient. Both arguments of r become pure only after logical reduction. A compound-input implementation must therefore not erase this distinction by describing its component exposure as ordinary substitution.

The warning in the prior tensor note about atomic components is a valid warning against that changed semantics, but not an obstruction to the raw-substitution finite-mode transfer.

## 4. What remains load-bearing CK structure

The top-degree reconstruction still needs complete maximal **tree** coefficients and exact hole-to-tree matching. It cannot be replaced by degree, leaf inventory, or endpoint counts. Corresponding residuals require actual antichain support, not merely equal ordinary shell identities.

When a formal atomic probe is replaced by a nonprimitive material implementation, its inner cuts and all newly spanning outer factors must be recomputed by the existing outer-antichain/unswallowed-inner-antichain bijection. Replacing a primitive generator by a composite coefficient is not a Hopf morphism. Tensor syntax does not alter this fact.

Nested opening uses the actual coaction equation. Refilling can change the cut coefficients; it is equality of the refilled equivalence classes that is stable, not a blanket claim that every refill is colinear over fixed unchanged coefficients.

## 5. Scope and rejection criteria

Reject a proposed mixed completion if it:

- proves only beta normalization while claiming full tensor commuting equality;
- uses proof-net graph equality without specifying primitive port labels and occurrence links;
- replaces raw substitution by beta-normalized installation without revising the material observer;
- allows arbitrary open holes while reusing the closed-island proof;
- claims an unrestricted full ordinary proof quotient over the original nonprimitive coefficients;
- assumes automatic polynomial canonicalization from termination alone;
- applies a nonhypothetical-constant coherence theorem to binding primitive rules without justification.

I find no tensor-specific counterexample to the old finite-mode, refill, or CK subcomodule proofs. The revised sparse-record theorem receives a PASS subject to its explicit interface and ordinary-equivalence assumptions. Shell coherence/reification remains an outstanding gate only for a further native canonical normalizer or effective unrestricted comparison algorithm; it is not a gate for the revised abstract mixed theorem.

## 6. Review of the revised sparse record and verification consequence

Replacing N by `K=(exact maximal islands, ordinary shell equivalence class with matched tokens)` removes the need for a reifier. The unique maximal-degree cut determines the full indexed islands and the ordinary class of the complete residual shell. Replacing its inherited cut-hole names by the matched abstraction tokens reconstructs exactly K. Conversely, an arbitrary internal material opening replaces islands by identical indexed pure residuals and substitutes their ordinary meanings into the same shell class. Thus equal records give equal full cofree profiles. This uses congruence of the *defined* mixed ordinary equivalence, not a claimed decision procedure for that equivalence.

Purity must still be retained separately in Q. The all-mode tuple must still be treated as a single basis label. Neither correction disappears merely because the shell coordinate is now a class instead of a syntax normal form.

I reviewed `verification_consequence.md`. Its finite-history transfer is sound under the stated signature theorem: each of its four action types preserves equality, and rigid forest marks pick corresponding actual residuals. Induction gives matching arbitrary finite histories in both directions. Its adaptive extension correctly restricts choices to matched observations. Subsequent extraction inside a detached factor is supported by literal factor equality; mixed staged extraction uses the full coaction law.

The verification note correctly limits bad-state nonreachability to the declared assembly observation transition system. It does not claim process-runtime deadlock freedom or memory safety without an adequate operational interpretation. It also correctly distinguishes universal signature certification by a paper theorem from finite portable instance checking. No additional blocker was found.

## 7. Final full-draft review

I subsequently read the complete `mixed_theory.md`, including its two-Hopf sequent comparison. Theorems 1 and 2, the triangular linear-kernel argument, hereditary record law, quotient comodule, and greatest-basis-equivalence proof pass review in the stated scope. In the maximality argument the separating unary material extension and nonzero complete endpoint are essential and are explicitly retained.

The sequent elaboration retains logical macros rather than substituting them away, which is necessary for exact material cones. Its tagged readback and the relative equation use distinct full source and target Hopf algebras and an isomorphism only between their realized material subalgebras. This is appropriately weaker than claiming a full Hopf map for elaboration. The passive-cell comparison retains its freshness and binder conditions, and explicitly excludes principal fusion and the unrestricted identity palette. No additional blocker was found.

The Barber discussion appropriately separates an ordinary-class mathematical theorem from implementing a complete comparison algorithm. I have not independently verified the external thesis's theorem numbering or complete binding-operator transcription; those claims require the separate source audit. The abstract record proofs do not rely on that external implementation claim.
