# A substitution-stable material semantics, and the exact obstruction to full proof identity

Research continuation, 10 October 2026. This advances the two active targets in `CK_PROJECT_TARGET_REGISTER.md`: complete the normalization/permutation comparison, and connect it to an independently specified logical carrier with substantive CK structure. It continues the morning checkpoint rather than replacing its history. General results are paper proofs with independent adversarial reviews; the accompanying Python checks are finite corroboration, not mechanization.

## 1. The outcome

There are two connected results.

**Positive:** a finite, computable material-mode signature gives a compositional refinement of ordinary proof identity. It is stable under all jointly typed implementations of free assumptions, ordinary proof contexts, actual material-hole refilling, and every subsequent CK extraction flag. It retains the original nonprimitive material Hopf coefficients. Under explicitly stated future-extension assumptions, its equality is the greatest **basis equivalence** with these properties that refines ordinary beta/eta identity. It resolves the previously exposed Cut-Cut and logical-passenger comparison in the declared implicational sequent fragment.

**Negative, and sharp:** the entire original IMLL palette includes identity/principal Cut elimination. A coaction identifying all atomic beta instances, with nonzero complete endpoints, can descend through a coefficient Hopf map only if that map kills every realizable material tree with a positive-arity root. The surviving universal quotient retains only the nullary-leaf catalogue. Thus the original full proof identity and faithful nonprimitive material CK decomposition cannot both be retained by that descent. This is a theorem about the requirements, not another failed choice of normalizer.

The positive result consequently provides a precise refinement and a forgetful map to ordinary proof identity. It does not claim that the finer equivalence is ordinary proof equivalence itself. The existing August theorem about an occurrence observer is not contradicted: occurrences and actual pure-material CK subtrees are different observations.

## 2. Exact native setting

The completed main proof concerns occurrence-linear implicational natural deduction with Ref, abstraction, application, and actual finite-arity atomic primitive rules. Primitive rules may have explicitly indexed hypothetical atomic discharges. Contexts and routes are linear; no resource is copied or erased. The corresponding sequent fragment has Ax, implication Right/Left, Gentzen Cut, and those primitive rules.

A selected material subtree contains only selected primitive vertices. Such a subtree has empty free context: a free or discharged reference would be a nonmaterial vertex. Actual material-origin holes therefore have closed atomic interfaces. They retain their full type, occurrence support and persistent seam; they are zero-vertex vacancies, never positive CK generators. Arbitrary opaque vacancies with hidden passive assumptions are outside this theorem.

Detached forests use the explicitly declared **commutative forest observation**. Native premise order, internal tree shape, physical occurrences and routed holes remain exact. The theorem is not literal invariance of a planar traversal tuple. Future extensions add fresh rules while preserving the material status of every existing label; promoting an old unselected occurrence to material is a different problem.

Let `rho` be the actual material CK coaction and `nf` ordinary unrestricted linear beta/eta normalization, retaining complete named holes. The latter is an observer, not a colinear map on arbitrary material proofs.

## 3. A sparse canonical realization of the old CK observer core

The September record already contains the residual observer-core construction

\[
\Phi(t)=(\mathrm{id}_H\otimes\mathrm{nf})\rho(t).
\]

The new work supplies an explicit native representative for its equality.

Take every maximal pure material subtree of `t`, together with each inherited hole not contained in such a subtree. Replace these disjoint **material islands** by fresh atomic opaque tokens. Fully beta/eta-normalize the remaining logical shell. Restore each island `m` behind the ordinary nonmaterial identity detour

\[
\operatorname{Seal}(m)=(\lambda x.x)m.
\]

Call the resulting native term `N(t)`. Tokens are administrative devices, not new primitive axioms. The mathematical proof uses fresh Ref parameters; the implementation uses equivalent fresh inert atomic placeholders during unrestricted shell normalization.

**Sparse-core theorem.** The algorithm is terminating, unique modulo coherent logical alpha, idempotent, preserves ordinary normal identity, and satisfies

\[
\rho N=(\mathrm{id}_H\otimes N)\rho,
\qquad
\Phi(t)=\Phi(u)\iff N(t)=N(u).
\]

Every actual opening has the same detached material forest and a correspondingly normalized complete remainder. This holds for composite factors and all nested extraction flags.

The key invariant is that the abstracted shell has no pure selected-material cone. Linear beta/eta cannot create one while its atomic opaque tokens remain. All material cuts therefore stay inside the retained islands. Opening an island leaves its punctured material tree or complete root vacancy in the same shell slot.

For reconstruction, the unique cut of greatest total material degree extracts all maximal nonempty islands. Its full forest coefficient, together with the normalized right-hand hole shell, reconstructs `N(t)`. The maximum-cut fact is an October 6 antecedent; the new statement identifies this reconstruction with the concrete normalized observer core. A triangular argument over maximal material degree also establishes the corresponding equality of linear kernels for `N` and `Phi`.

The representative has linear size, although the explicit cut polynomial may have exponentially many terms. This is an exact representation result, not a claim that every CK computation becomes polynomial.

There is a necessary further refinement. `N(m)=N(Id(m))`, but a selected material context `r[-]` distinguishes them. Define

\[
Q(t)=\begin{cases}t,&t\text{ is pure material, including a bare origin hole},\\N(t),&\text{otherwise}.\end{cases}
\]

This adds the root-purity information, remains colinear and idempotent, and is stable under ordinary whole-proof context insertion. It still fails free-input substitution: `x` and `Id(x)` have equal `Q`, while substituting a pure material `d` gives different `Q(d)` and `Q(Id(d))`. The finite modes below resolve that defect.

## 4. Finite modes characterize all future implementations

For each atomic free input occurrence `x_i:a_i`, reserve a distinctly marked formal selected nullary probe `alpha_i:a_i`. For every subset `S` of the atomic inputs, substitute its probes and leave the other inputs as references. Define the complete correlated signature

\[
\Sigma(t)=\left(Q\bigl(t[\alpha_i/x_i:i\in S]\bigr)\right)_{S\subseteq I_{\mathrm{at}}}.
\]

Compound inputs have no pure-material mode because material rules and permitted holes have atomic outputs. Every coordinate retains its actual complete interface. Probe identities belong to a disjoint tagged namespace, so they cannot collide with native occurrences.

**Finite implementation theorem.** For same-interface terms,

\[
\Sigma(t)=\Sigma(u)
\iff
Q(t\sigma)=Q(u\sigma)
\quad\text{for every jointly typed linear substitution }\sigma
\]

in the declared formal/future-extension universe.

For sufficiency, classify each supplied proof as pure or impure. Pure proofs expand the matching probe leaves inside the exact material-island templates. Impure proofs cannot create a pure cone across the insertion boundary; their own islands and normalized opaque shells are inserted once. Equality of the retained templates and ordinary beta/eta substitution congruence give equality after this arbitrary implementation. A subsequent implementation of the fillers' free resources is handled by reclassifying the final composed fillers, not by assuming their original purity persists.

Necessity tests the finitely many probe substitutions themselves. There are `2^a` entries for `a` atomic free occurrences. Each entry has polynomial construction cost and linear output size under the stated native representation, giving `O(2^a poly(n))` comparison with explicit type/interface costs included. For fixed `a`, this avoids enumerating the full exponential family of material cuts. It is not a general proof-net complexity result.

**Actual material-hole refilling needs no further mode coordinates.** A material-origin hole is already part of an exactly retained island template. Filling it with a pure proof expands that template; filling it with an impure proof splits the same template identically on both sides. Existing exterior nonmaterial blockers survive. This differs fundamentally from replacing a free Ref by a pure proof, which can create a previously absent material region. The theorem covers simultaneous and successive complete hole fillings.

**Hereditary CK theorem.** Equal signatures have matching actual antichain cuts with the same full forest coefficients, and their exact remainders again have equal signatures. To prove this, select the same rigid original forest coefficient in every probe mode. A new probe-spanning cone cannot impersonate it because it contains fresh probe identities. Coefficient separation gives equality of each corresponding residual signature. Actual coassociativity then gives every nested flag. The newly created holes can subsequently be filled by the preceding refill theorem.

Therefore the vector space on **whole-signature equivalence classes** is a material comodule with well-defined typed implementation and refill operations. One must not replace it with the kernel of a direct sum of separately linearized modes: that can lose cross-mode correlations through signed cancellation.

## 5. The precise maximality and semantic qualification

Consider basis equivalences that preserve complete interfaces and ordinary beta/eta identity, admit the original actual material coaction with nonzero residual basis classes, and are stable under typed contexts, substitutions and admitted fresh-symbol material extensions.

**Maximality theorem.** In an extension universe admitting the required selected nullary probes and fresh unary material testing contexts, `Sigma` equality is the greatest such basis equivalence.

Any such equivalence must preserve `Phi`, hence the reconstructed `N`. A remaining purity mismatch is separated by a fresh material context `r[-]`: its composite root coefficient exists only on the pure side, and its complete endpoint is nonzero. Thus it must preserve `Q`. Substitution stability applied to all pure probe modes forces equality of `Sigma`. Conversely the preceding theorems establish each required stability for signature equality.

This concretely realizes the older conditional contextual/filling-core programme. It is not a greatest-arbitrary-linear-kernel claim, and it is not proof-relevant adequacy for all GGP semantic morphisms.

Formal probes are not automatically conservative extensions: adding a nullary proof of `p` can make `p` derivable. The complete theorem explicitly permits those extensions. For a fixed base or a restricted/nonmonotone extension policy, signature equality remains a sufficient implementation-independent certificate; completeness must be restricted to **jointly admitted complete-judgment modes**, with their witnesses established. A failure in an unrealizable formal mode is not silently an operational counterexample in that fixed base.

The existing relative shadow-witness naturalisation remains applicable: compose its actual material-comodule map with the new signature classifier. The ordinary support-operation readout is preserved, while the signature retains the material refinements that support truth forgets. No canonical witness selection from a truth-valued support assertion is introduced.

## 6. Where the full CK/Faà di Bruno structure is necessary

Replacing a formal primitive probe by a composite material proof is **not a Hopf morphism**. The probe has primitive coproduct, while the supplied tree has proper internal cuts. A substitution argument that simply maps a probe coefficient to its payload misses those terms.

The actual expansion uses the following exact partition of cuts of a material template `T[P_i]`:

1. Choose an antichain of old **nonprobe** vertices of `T`.
2. Every supplied proof beneath one of those selected vertices is swallowed whole into that detached outer factor; it contributes no independently selected inner cut.
3. In every uncovered supplied proof, choose an arbitrary actual inner antichain, including empty and whole-root choices where defined.
4. Retain the complete expanded outer factors, all detached inner factors, and the exact routed remainder.

Every expanded cut has one and only one such decomposition. It retains composite factors spanning several supplied proofs and excludes incompatible nested selections. The law multiplies over independent islands; actual CK coassociativity supplies its successive-extraction coherence. Impure filling first splits the known template into its resulting pure islands, whose actual cuts are then treated in the same way.

This is the Faà di Bruno content needed to transport the finite symbolic certificate to real implementations. The outer–inner law is an antecedent; its concrete use here establishes the finite universal criterion, rather than supplying a new abstract identity.

The implementation checks 64 pure-template expansions with 1,791 exact antichain terms, including zero-vertex supplied vacancies. A primitive probe has two pointed cut terms; replacing it by a binary material tree produces five, including the genuine internal two-leaf cut. The checker reconstructs those additional terms by the outer/inner rule.

A separate lifting obstruction strengthens the earlier nonprimitive example: a typed comparison can pass every primitive-leaf extraction square and still have no full material-colinear extension preserving the nonzero support adapter. The missing coefficient `s(a,b)` would force that extension to annihilate its valid residual operation. Thus primitive tests cannot substitute for the retained composite coefficients.

The indispensable content is the complete nonprimitive cut/residual structure and its substitution/coassociativity laws. An equally informative typed antichain formalism can encode the same mathematics. This work does not establish an exclusive need for Hopf notation, an antipode-based speedup, or a new antipode application.

## 7. The actual sequent comparison and the full-identity obstruction

The recovered August palette is single-conclusion IMLL with fusion/tensor and implication, linear multiset contexts, Gentzen Cut, both principal reductions, nonprincipal Cut permutations, Cut-Cut reassociations and identity cells. Its stated Theorem 5.18 concerns the occurrence observer `Upsilon_B^occ`, not the free pure-material CK coaction.

For the implicational subfragment, the continuation gives a faithful origin-tagged sequent-to-ND elaboration `E`, with separately checked source judgments and readback. There are **two** full native rooted-proof Hopf algebras, `H_SC` and `H_ND`. Their realized material subalgebras are related by a genuine graded typed Hopf isomorphism `alpha`, preserving material rule, route, discharge and seam data. The exact comparison is

\[
\rho_{\mathrm{ND}}E=(\alpha\otimes E)\rho_{\mathrm{SC}}.
\]

`E` is not a Hopf map on the whole native logical algebras: logical macros add interior cut positions. The theorem uses the material subalgebras and their proof comodules, not an unidentified single algebra for two calculi.

The composite `Sigma E` is invariant under the six explicitly generated passive families: primitive passenger, implication Right passenger, both implication Left premises, dependent Cut-Cut reassociation and independent Cut-Cut exchange. The equation must hold under the finite input modes, not merely before later filling. Twelve direct signature comparisons pass, alongside native source cut/readback checks and nested contexts. The executable sequent translation currently covers nonhypothetical primitives; its hypothetical-discharge extension is a paper induction, while separate ND/shadow clients test hypothetical discharge. The former Cut-Cut counterexample is now identified by the canonical comparison.

For the entire original palette, let `q` identify all ordinary atomic beta instances and actual residual instances, with nonzero complete endpoint holes. Suppose a Hopf map `pi:H→K` makes the material coaction descend. For any realizable positive-arity material tree `T=r(T_1,...,T_n)`, insert the identity detour at one child: `D′=r(T_1,...,(lambda x.x)T_j,...,T_n)`. Its reduction to `T` is directly an identity cell under a material context, so belongs to the recovered palette without assuming an extra primitive-passenger conversion. The only new material factor after that reduction is the whole `T`; every inherited sector cancels after `q`. Hence

\[
0=\pi(T)\otimes q(\square_J),
\qquad\text{so}\qquad\pi(T)=0.
\]

The same argument applies to actual punctured residuals. These positive-arity-root trees generate a Hopf ideal: every proper right CK remainder retains that root and belongs to the ideal. The quotient is the polynomial Hopf algebra on realized marked nullary leaves. Conversely its leaf coaction does respect full linear beta/eta. This makes the loss sharp.

Accordingly, full `D_lin` descent with faithful nonprimitive material coefficients is impossible under these hypotheses. The old occurrence theorem remains valid and different. The new positive result supplies a maximal compositional refinement with an ordinary-normal-form readout; it does not identify that refinement with the full historical palette or the separate classical MLL+Mix fixed-net class-sum subalgebra.

A supporting tensor-only prototype gives an explicit canonical observer and checked tensor beta/eta/commuting examples. It does not establish a complete mixed tensor–implication implementation. That remaining extension should be pursued for the refined carrier, not as an attempt to overturn the full-palette no-go.

## 8. Practical result, evidence and next obligation

The practical check now concerns two complete open proof operations, rather than only a selected normalization step. Equality of their finite signatures certifies that every admitted future implementation has matching normalized material observations; every actual extraction and subsequent refill remains comparable, including nonprimitive module operations. No exhaustive enumeration of every future proof is required.

A differing coordinate is a finite formal diagnostic. Its normalized maximal material forest and named-hole shell locate the discrepancy; a pure/impure-only discrepancy has the explicit unary-material testing context. In a restricted actual base, a diagnostic becomes an operational counterexample only after its probe mode is jointly realized. These are proof-module assembly and observation guarantees, not a new CP runtime progress/deadlock theorem.

Evidence includes:

- Sparse normalization: 4,228 generated terms, 16,916 material residual states and 60,042 actual cut terms.
- Free-input refinement: 1,340 implementation/coaction checks, including open and compound fillers; 180 two-stage comparisons covering 927 flags.
- Independent extraction/refill challenge: 1,724 equal pairs, 3,505 actual batches, 9,226 joint closed refills, and additional typed stress probes. More than 1,400 batches open nonprimitive islands.
- A separate adversary: 218 exact one-term no-go defects, 744 substitution probes, and 3,464 actual-hole refill probes.
- Native sequent translation, exact coefficient checks, formal-marker collision regression and the explicit Faà di Bruno expansion check.

The archive includes all scripts, detailed proof notes, exact result files and a reproduction runner. It also includes the earlier baseline client sources needed by the new tests. The external Racket and Lean repositories were not changed.

The novelty audit credits the September core/profile framework, October 6 maximal-cut decoder, October 9 exact substitution defect, and established guarded/explicit-substitution theory. The credible increment is the **concrete finite complete criterion and canonical realization**, the uniform typed implementation/refill theorem, the explicit sequent comparison, and the universal forced-loss boundary. No exact earlier combined theorem was identified in the targeted audit; publication priority is not established.

The next principal task is now a full mixed tensor–implication realization of this **refined** compositional carrier, with native source generators and complete interfaces, followed by one integration into the existing verification implementation. The original request for unchanged nonprimitive CK descent through all identity/principal cells has been resolved negatively and sharply; it should no longer remain an open promise in the target register.
