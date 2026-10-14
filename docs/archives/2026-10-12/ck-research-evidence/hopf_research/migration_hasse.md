# Multivariate CK transfer polynomials, Hasse composition, and a budgeted application

Original derivations, 12 October 2026. Companion to `migration_algebra.md`. Paper-level proofs, no Lean. Physical occurrence data and binder identity are retained throughout.

## 1. The physical-hole polynomial

Fix an exact typed multi-hole template C with finite physical hole set H. Fix a compatible interface signature s_h for each hole. Let the scalar/root weight of a filled subtree be a function of its independently computed interface. On this fixed signature fibre, every possible template-root weight is fixed even as the payload cut spectra vary.

For a template-node antichain S, let U(S) be the holes not masked by S. Let a(S;s) be the product of the weights of the filled template subtrees rooted at S. Define

    F_C^s(X)=Σ_S a(S;s)∏_{h∈U(S)}X_h.

Then F is multiaffine in the physical-hole variables. Distinct S with the same U contribute to the same coefficient by addition; they are not deduplicated. The installed spectrum theorem gives

    Q(C[P])=F_C^s((Q(P_h))_h)

whenever the independently checked payload signatures equal s.

This formulation is stronger than an anonymous tree polynomial: its coefficients retain exactly the ancestor masks and their actual interface obligations. It can be stored as a factorized circuit following the template rather than expanded into exponentially many monomials.

## 2. McBride frames interpret as affine spectrum transformers

For one hole, F_C^s(X)=A_C(s)+B_C X. Every frame of the typed zipper contributes the product of the unchanged sibling spectra to the slope. Composing frames multiplies these slopes, so B_C is their product over the spine.

Interface-changing edit P→P' gives

    Q(C[P'])−Q(C[P])
      = A_C(s')−A_C(s)+B_C(Q(P')−Q(P)).

The subtraction is in the integral coefficient ring. The underlying spectra remain nonnegative. In particular the derivative multiplier alone is complete exactly when s'=s. No context-blind source census can recover B_C, as the typed pair/lambda separator in §9 of the companion proves.

## 3. Exact simultaneous-edit law

For J⊆H, write ∂^[J]F for the mixed Hasse derivative (coefficient of ∏_{h∈J}Y_h in F(X+Y)). Because F is multiaffine,

    F(X+δ)=Σ_{J⊆H}(∂^[J]F)(X)∏_{h∈J}δ_h.

Proof. Expand every monomial ∏_{h∈U}(X_h+δ_h), selecting the edited term at exactly J⊆U. This is a bijection between expansion choices and pairs (U,J), preserving each coefficient. QED.

For signature-changing simultaneous edits, the correct exact identity is

    F^{s'}(X+δ)−F^s(X)
      = (F^{s'}(X)−F^s(X))
        + Σ_{∅≠J⊆H}(∂^[J]F^{s'})(X)∏_{h∈J}δ_h.       (1)

The first term is the ancestor-interface correction. Using old-signature derivatives without an additional cross correction is generally wrong. Formula (1) fixes the updated signature before expanding the payload changes.

The higher mixed terms have a direct frontier meaning: they count cuts simultaneously descending into all holes in J. If an ancestor choice masks any edited hole, it cannot contribute to that mixed derivative. Thus the derivative is a simultaneous-reuse sensitivity, not an arbitrary calculus analogy.

## 4. Why copying introduces genuine higher derivatives

Suppose π:H→I tells which source payload supplies each physical hole. If all copies have the same interpreted interface/renaming action, substitute X_h=X_{π(h)}. The resulting polynomial G_C(X_i)=F_C(X_{π(h)}) has degree at most |π^{-1}(i)| in source parameter X_i.

For one source copied m times the finite update becomes

    G(X+δ)=Σ_{k=0}^m D^[k]G(X)δ^k.

D^[k] is the k-th Hasse derivative, defined by coefficient extraction, so no k! division or characteristic-zero assumption is required. The coefficient of δ^k is obtained by choosing k distinct physical occurrences before forgetting their common source label. This is the exact occurrence-count mechanism behind binomial and Faà di Bruno coefficients.

If clone-local binder identities differ, identification is not automatic. Let ρ_h be the action renaming internal binder/resource identities while fixing genuinely shared exterior identities. Then the installed expression is

    F_C^s((ρ_h(Q(P_{π(h)})))_h).

The maps ρ_h preserve addition and multiplication of the resource algebra, so an edit is propagated by replacing δ_h with ρ_h(δ_{π(h)}). If the observation does not identify those renamings, this is a polynomial expression with semilinear renaming operators, not an ordinary polynomial in a single anonymous scalar variable. Only an explicitly equivariant/alpha-invariant observation permits collapsing it to powers.

The names chosen for fresh binders are administrative; the partition into shared and fresh coordinates is semantic. Alpha-renaming the complete construction consistently preserves its interpretation up to the corresponding resource-name isomorphism.

## 5. Exact multivariate Hasse chain law

Let G_h(X) be the transfer polynomial of the inner template installed at outer physical hole h, all on fixed compatible interface fibres. Staged filling gives the composite polynomial F(G_h(X)). For a multi-index α of input edits,

    D^[α](F∘G)(X)
      = Σ_{J⊆H}(∂^[J]F)(G(X))
          Σ_{(β_h)_{h∈J}: β_h≠0, Σβ_h=α}
               ∏_{h∈J}D^[β_h]G_h(X).                   (2)

For α=0 the empty-J term is F(G(X)); for nonzero α, only nonempty J contribute.

Proof. Put H_h(T)=G_h(X+T)−G_h(X), which has zero constant term. Multiaffinity gives F(G+H)=Σ_J∂^[J]F(G)∏_{h∈J}H_h. Expand each H_h by its nonzero Hasse coefficients and extract T^α. The displayed inner sum is exactly the family of distributions of the input edit marks among active outer physical holes. QED.

There is an independent physical-hole proof. Every final edited position has a unique outer hole h and a unique position in its inner template. An expansion choice records which outer holes are used and which inner edits occur in each. The address map concatenates those two positions; its inverse splits at the template boundary. Selected ancestor masks remove an entire fibre rather than choosing arbitrary invisible edits in it. This is the same bijection as the installed cut-flag law, now interpreted by coefficients.

After identifying copied-source variables, formula (2) becomes a Hasse/Faà di Bruno law with the appropriate occurrence multiplicities. It does not assume that the primitive-to-macro expansion is a Hopf morphism. It is a compatibility law between CK extraction and typed substitution.

## 6. A budgeted closure-externalization analysis

The spectrum can drive an independently stated optimization problem. Mark which rooted subterms are certified externalizable tasks. Certification may require an exact output type, a portable closure interface, and preservation of the session controller. It is a predicate on candidates, not a modification of the CK coproduct.

Give an eligible module U a nonnegative transfer cost c(U) and a saved-work benefit b(U). For a cut C, cost and benefit add over its factors. Define

    Opt_T(k)=max { Σ_{U∈C}b(U) : C a full CK frontier,
                   all U certified, Σ_{U∈C}c(U)≤k }.

The empty cut has benefit zero. Set the root weight to zero when its module lacks a certificate; this filters the *observation* of the full coproduct. It does not claim that certified frontiers form a subcoalgebra.

THEOREM (budget recurrence).

    Opt_T(k)=max( root option if certified and c(T)≤k,
                  max_{k₁+…+kₙ≤k} Σᵢ Opt_{Tᵢ}(kᵢ) ).

Proof. Partition physical cuts into root-selected versus root-unselected. In the latter case the child frontiers and their additive budgets are independent. These are exactly the two alternatives of the CK recurrence evaluated in a budget-indexed max-plus coefficient algebra. QED.

This theorem assumes that the stated certificates compose independently under exact closure capture. If certificate validity includes shared global constraints, replace the scalar multiplication with a boundary-matching kernel before optimizing; a product of unrelated Booleans is insufficient. Shared resource cost likewise requires retaining the identity-set monoid before cost evaluation.

### Nontrivial concrete benchmark

Use the fully typed 35-node cross reduct of the companion. A candidate is a rooted subterm containing no session constructor: sequential process tasks may be externalized, while channel-session controllers remain in place. This excludes the trivial choice of exporting the whole closed session at zero interface cost. Charge one unit for each exported task whose interface requires b. Give each exported task the synthetic benefit `number of syntax nodes − 2`, modeling two units of per-task setup overhead; ignore negative-benefit choices. These costs are a declared analysis model, not measured runtime costs.

The four maximal process tasks have sizes 7,9,7,9. The unchanged two are b-free, with total benefit 12. The adapted tasks have benefits 5 and 7 and each requires b. Exact optimization gives:

| b-dependent task budget | Optimal saved-work score | Selected maximal tasks |
|---|---:|---|
| 0 | 12 | the two unchanged tasks |
| 1 | 19 | unchanged tasks and the larger adapted task |
| 2 | 24 | all four tasks |

The DP also considers all smaller simultaneous frontiers; the values are not obtained by assuming maximal tasks optimal. This example gives a concrete use for both CK extraction and the transformed closure interface: a local migration certificate supports exact resource-constrained reuse/offload planning, and zipper/Hasse updates can maintain it when message implementations change.

No operational scheduler, runtime speedup, or code-generation correctness theorem is claimed. The mathematical query is precise and independent of the algebra; the coproduct supplies its exhaustive decomposition and compositional implementation.

## 7. Audit of the actual cross step

The canonical fixture satisfies more than equal endpoint typing:

* a is declared active; no claim is made that its displayed nonvalue messages activate it automatically.
* each process has one displayed a occurrence, hence it is rightmost in its process.
* the sender/receiver roles are A→B and B→A, as required by Lin.
* x:X and y:Y are exactly the locally bound free dependencies of u=z x and v=y k; z,k and the wrappers w,r remain public.
* b is fresh, with roles X→Y and Y→X; substituted arguments have the required types.
* fresh copied lambda and inner session binders are renamed consistently. The two occurrences of the outer session identity b remain shared, with their distinct endpoint roles.
* the source's contextual substitution intentionally reconnects captured variables; it is not capture-avoiding substitution under an arbitrary renamed source context.

The executable checker independently checks the ordinary/channel type derivations and free interfaces. It does not encode the source's entire reduction relation; the above matching to its explicit schematic rule is the paper-level reduction certificate. The project-native CK/proof encoding remains a separate bridge.
