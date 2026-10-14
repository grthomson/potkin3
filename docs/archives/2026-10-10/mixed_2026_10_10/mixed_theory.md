# Mixed tensor–implication completion by sparse material records

Date: 2026-10-10. Paper theorem. This document extends the actual material CK result to the mixed unit-free intuitionistic multiplicative calculus. It deliberately separates the mathematical construction from the independently implemented bounded checker and from a general-purpose logical equality implementation.

## 1. Exact scope and the change of representation

Types are atoms, `A ⊗ B` and `A ⊸ B`. Native terms have indexed linear Ref, Lam, App, Pair, tensor elimination `Let M as (x,y) in N`, and fixed primitive atomic rules. Explicit Gentzen Cut may be represented by one-use substitution syntax or its Lam/App macro. Contexts are multisets of individually indexed resources; tensor ports and primitive ports are ordered and remain distinct. There are no units, exponentials, weakening or contraction.

The old material profile selects primitive rules, not logical rules or Ref. Pure material cones, actual antichain cuts, occurrence labels, complete closed atomic origin holes, and the commutative product of detached trees are exactly those of the preceding continuation. Existing symbols cannot change selected status under extension. A pure material cone is closed, because a free input would require a Ref vertex. Rules with intrinsic atomic discharge are allowed in the structural theorem: a genuinely used discharged input supplies a Ref blocker, so no pure cone contains such an input use.

Let `≡L` be the declared ordinary mixed logical equality: implication and tensor beta/eta, the usual capture-free linear commuting conversions and Cut composition, all closed under typed contexts and substitution. Primitive operation identities, ordered ports and actual origin-hole names are rigid. No equations on the primitive operations themselves are imposed.

The new representative is a **sparse island record**, not a claimed new convergent orientation of mixed term rewriting. This removes a needless dependence on a particular canonical native sequentialization.

## 2. The record K

For a native term t, collect its maximal nonempty pure material cones `m_i`. Add each original bare material-origin hole outside these cones as a zero-vertex island. Replace each island with a fresh atomic Ref token `z_i` carrying its complete output type and its rigid origin correspondence. The result is the typed shell `S_t`.

Define

`K(t) = (the exact indexed island payloads m_i, the ordinary shell class [S_t]_L)`.

The record includes the complete outer context and result type, the token-to-origin bijection, all old bare-hole identities, and every hole internal to an island payload. Token spelling is immaterial only under the indicated coherent renaming. No island is represented merely by its size or list of labels. A zero-vertex payload is the actual named origin hole.

Define the purity-refined record `Q*(t)=(pure(t),K(t))`. If t is pure, K already determines its whole raw indexed tree, including a possible zero-vertex whole-hole case. Consequently equality of Q* in the pure case is literal equality of the raw material payload.

This is finite data plus one ordinary logical equality class. Equality can be represented by a canonical ordinary-shell observer when such an observer is installed; Sections 3–7 need only the congruence laws of `≡L` and therefore do not assume a new normalization algorithm.

## 3. Exact equality with the actual CK observer core

Let P be the free vector space on native proofs and actual residual states. Let V have the ordinary complete residual classes `[t]_L` as its basis. Write

`Φ_L = (id_H ⊗ [-]_L) ρ : P → H ⊗ V`.

**Theorem 1.** For native t,u at the same complete interface,

`K(t)=K(u)  iff  Φ_L(t)=Φ_L(u)`.

**Forward proof.** Every actual material cut lies inside the recorded maximal material islands. Equal K records give a bijection between all these cuts, retaining each detached indexed forest and each named opening. For any corresponding cut I, replace each shell token by its residual island `m_i/I_i`, including its whole-opening hole if appropriate. These substitutions yield the original residual t/I and u/I. Their shells are ordinarily equal and ordinary equality is a typed congruence, so `[t/I]_L=[u/I]_L`. This proves equality term by term, with exact multiplicities. This proof does not normalize a material cone and does not assume normalization preserves raw purity.

**Reverse proof.** Grade forests by positive material vertex count. There is exactly one greatest-degree cut: cut every maximal nonempty material island at its root. Its coefficient is their full indexed product. A proper internal cut omits at least the island root and has smaller degree. The ordinary right factor retains the complete named holes for the simultaneously opened islands and all inherited bare holes. Every hole is still used exactly once, by linearity. Relabel these closed hole constants as fresh atomic free tokens: logical equations remain valid under this rigid signature renaming. The right factor then supplies precisely `[S_t]_L`; the coefficient and hole origins supply the matching full payloads. Thus the greatest-degree term reconstructs K. With no positive islands the empty cut supplies the degree-zero case. ∎

Linearizing K by using distinct complete records as basis vectors gives `ker K = ker Φ_L`. This requires more than basis injectivity: in a finite linear relation select the largest island degree; distinct K records at that degree have distinct reconstructing greatest-degree monomials. Their coefficients vanish separately, then descend in degree. The familiar cofree-core theorem follows from actual CK coassociativity, and Theorem 1 gives its sparse concrete realization for the mixed language.

**Hereditary record law.** Opening a supported batch changes only the payload entries `m_i → m_i/I_i`; its token shell is unchanged. Whole-opened islands are retained as zero-vertex named-hole payloads. Hence equal K records have equal residual records at every corresponding actual cut. The same is true of Q*: an impure raw host keeps its nonmaterial vertex, whereas opening a pure host leaves a pure payload. This supplies the descended actual CK coaction directly on record classes, with the original full H as coefficients.

## 4. Why compound inputs do not need extra purity modes

Classify an implementation by its **raw** root purity before logical normalization. Every compound-typed implementation is impure, because selected material rules and origin holes have atomic conclusions. Replacing a free Ref with an impure implementation cannot create a pure cone spanning that seam. It may insert its own internal pure islands, but its nonmaterial syntax separates them from surrounding material ancestors.

Tensor beta can erase a Pair/Let boundary during logical normalization. That does not invalidate this argument: maximal material islands are extracted from the raw substituted proof first, and only the resulting opaque shell is compared modulo logical equality. The shell class can forget that administrative boundary without retroactively merging the island payloads.

For example, with `z:p⊗q`, compare

`t = Let z as (x,y) in r(x,y)`

`u = Let z as (x,y) in r(Id(x),y)`.

Both have no pure positive island and equal ordinary shells, so Q*(t)=Q*(u). There are no atomic entries in their free context. Substituting `Pair(δ,ε)` for z gives equal Q* records: δ and ε are separate recorded islands; r's arguments still contain its bound Ref occurrences, and the enclosing Let remains in the raw term. If one instead normalizes the raw substituted proofs before computing materiality, one obtains `r(δ,ε)` and `r(Id(δ),ε)` at an intermediate stage and risks declaring a spurious counterexample. That is a different observer. Under complete ordinary normalization both reduce further, but neither intermediate or final material decomposition defines our raw CK coaction.

Compound ports therefore require no Boolean modes for their atomic components in this theorem. Such modes might be appropriate for a different observer that explicitly opens/deconstructs ports as an operation before material extraction; that operation must be separately declared, not silently added.

## 5. Finite universal signature and proof

For each atomic free assumption `x_i:a_i`, reserve a fresh selected nullary probe `α_i:a_i`, with disjoint physical occurrence and symbol identities. For each subset S of the atomic free assumptions, let `t_S=t[α_i/x_i : i∈S]`. Set

`Σ*(t)=(Q*(t_S))_S`.

The complete tuple is a single basis label. It has `2^a` entries when a free assumptions are atomic. This is not an identification of its linear kernel with the intersection of separate coordinate kernels.

**Theorem 2.** In the declared future-extension universe admitting these joint probes,

`Σ*(t)=Σ*(u)` iff `Q*(tσ)=Q*(uσ)` for every jointly typed, resource-disjoint raw implementation σ.

**Proof.** Given σ, let S select the atomic ports whose final implementations are pure. The maximal material islands of `t_S` are exact material templates containing those probe vertices. Expand them by the corresponding pure payloads. Every other free Ref is outside every island; its impure implementation adds its own maximal material islands and opaque shell without creating a spanning pure island. This description is entirely syntactic and holds for Pair/Let as well as Lam/App. Equal starting Q* records therefore produce the same expanded/supplemented island payloads. Their outer shell classes agree by ordinary typed substitution congruence. Their raw root-purity flags agree: an impure substitution cannot remove the raw blocker, and the pure case starts with identical trees. Hence the outputs have equal Q*. Conversely the finitely many formal probe substitutions are among the permitted σ. ∎

Further substitution is included: classify the final composed implementations afresh, rather than preserving an earlier purity classification. Thus Σ* equality is stable under all subsequent typed substitution. Ordinary context closure follows by the same seam argument, distinguishing pure arguments (literally identical) and impure arguments (unable to create a spanning island). A binding context is allowed with exact capture and resource side conditions.

Actual origin-hole refilling is separate from free-input substitution. In equal records, corresponding holes occur in identical island templates or as matching zero-vertex islands. A pure refill enlarges equal templates; an impure refill splits equal templates in exactly the same manner. Replace the affected token slots by these identical split-template shells. Ordinary shell congruence yields equal Q* records. This holds simultaneously, and after final free-input modes, proving Σ* refill stability. Fixed closed complete slots remain closed; permitting extra free input resources is a different declared operation.

## 6. Actual comodule closure and greatest basis equivalence

Equal Σ* records identify the same original material islands. Each original cut stays an actual cut after every probe substitution, because its closed factor contains no free input. Newly spanning cones contain a fresh probe identity and cannot counterfeit an old rigid forest coefficient. Q* hereditary opening therefore applies at the corresponding original cut in every mode. Opening a closed original factor commutes with the free-input probe substitution. Consequently the two residuals have equal Σ* signatures.

The span of equal-Σ* basis differences is a material subcomodule. Its quotient has the full original indexed CK coefficient Hopf algebra. Coassociativity gives all supported nested extraction flags; the refill lemma applies to their newly created complete holes. No primitive-only replacement of the coefficient algebra is made.

Suppose E is a basis equivalence preserving complete judgments and ordinary mixed logical identity, admitting this actual descended coaction with nonzero endpoint residual classes, and closed under typed contexts, substitutions and the stated fresh material extensions. Then E implies equality of Φ_L, hence K by Theorem 1. A purity mismatch is separated by the fresh selected unary material context r[-]: a pure input yields a whole composite material coefficient unavailable for an impure input. Therefore E implies Q*. Applying each admitted probe substitution gives Σ*. Conversely the preceding results establish all these properties for Σ*. Thus Σ* is the greatest basis equivalence with these properties, subject to the same explicit extension-richness and nonzero-endpoint assumptions as the implicational result.

In a fixed or nonmonotone base, unrestricted formal probes need not be jointly admitted. Σ* equality remains sufficient; necessity and maximality require the corresponding jointly admitted complete-judgment probes and unary separating context. Adding α:p is not a conservative logical extension merely because it is a useful formal test.

## 7. Faà di Bruno content and the continuing no-go

Nothing in the mixed completion replaces a nullary probe by a composite coefficient through a Hopf morphism. For a pure island template T with probe leaves α_i replaced by pure P_i, the actual cuts are uniquely parametrized by an antichain of old nonprobe vertices and independent inner cuts in each P_i not swallowed by a selected old ancestor. A selected old ancestor carries the whole expanded subtree, possibly spanning multiple supplied implementations. Swallowed payloads cannot contribute independent inner cuts. This is the prior exact typed Faà di Bruno antichain substitution law, now used by the mixed universal-signature theorem. It multiplies over islands and remains coherent for nested flags by CK coassociativity.

The full ordinary-identity obstruction survives unchanged: the mixed calculus contains the implicational counterexample. Identifying all ordinary atomic beta reductions while keeping nonzero complete endpoints forces a compatible coefficient Hopf morphism to annihilate every realized positive-arity material tree. Tensor does not repair that loss. Σ* gives a compositional refinement of mixed ordinary identity, not descent of the unchanged CK observation through the full ordinary quotient.

## 8. Constructive logical equality module and exact dependency

Primary antecedent: Andrew Barber, *Linear Type Theories, Semantics and Action Calculi* (1997), <https://era.ed.ac.uk/bitstream/handle/1842/392/ECS-LFCS-97-371.pdf>. Chapters 4 and 7 treat operator signatures and higher-order extensions; Chapter 9, Theorem 9 and Lemma 9.4.14 give relational normalization and an equality criterion; Corollary 9.4 gives decidability for ILL(C). These are existing logical-equality results, not new CK claims.

The required application is an explicitly rigid signature instance: use a separate operator symbol for each physical primitive occurrence, its ordered premises and its specified intrinsic bound inputs. The linear context is the whole context; no unrestricted resource use is admitted. Lam/App and Pair/Let are the higher-order multiplicative constructors. Each token is a distinct linear free atom; named origin holes can equivalently be distinct nullary rigid symbols. Administrative alpha-renaming may not rename physical primitive or origin identities. Keep every primitive free of added equations. This records all data forgotten by unlabelled proof nets.

For a concrete implementation, translate each token shell into that relational syntax, perform the stated normalizations, and decide the remaining vestigial equality retaining the rigid labels. A canonical record label can be chosen by finite canonical naming/permutation enumeration of the resulting finite relation, with externally indexed ports fixed. If a native witness is needed, the source's relations-to-terms construction supplies one; a least-choice convention may make it deterministic. K and the proofs above do not require that witness or a new native rewrite theorem.

The exact operator-schema transcription, relation normalization and vestigial equality procedure must be implemented and checked before describing the current Python NbE checker as a complete implementation of this published algorithm. Intrinsic binding operators require the direct operator signature route; treating all of them as unannotated first-order graph nodes is insufficient. No new polynomial complexity bound for the mixed implementation is claimed here. The unconditional mathematical record theorem is independent of these implementation tasks; effectiveness follows when the declared ordinary equality is instantiated by this standard rigid-signature linear type theory.

## 9. Native mixed sequent comparison: two Hopf algebras

Let `H_SC` and `H_ND` be the distinct full native rooted-proof Hopf algebras for the single-conclusion mixed sequent and natural-deduction presentations. Their selected material subalgebras are `H_SC,B` and `H_ND,B`. Relabel a selected primitive application together with its ordered premise ports, physical identity, intrinsic discharge tokens and complete seams. On realized material trees this defines a graded typed Hopf isomorphism `α:H_SC,B→H_ND,B`: roots, admissible antichains, forests and opened remainders correspond exactly. The native logical constructors outside these subalgebras differ.

Define origin-tagged raw elaboration E recursively. Ax becomes Ref; implication right becomes Lam; tensor right becomes Pair. Tensor left, from a premise using the two indexed assumptions x:A and y:B, becomes `Let z as (x,y) in E(premise)` at the original principal assumption z:A⊗B. Implication left installs the application of the indexed principal function to the elaborated argument into the unique active assumption of the elaborated continuation; represent that installation with its explicit one-use Cut macro, retaining the source-origin tags. Gentzen Cut becomes `(λx.E(continuation)) E(provider)`. Primitive rules map to the matching primitive node with unchanged premise/discharge routing. These tagged macros provide raw readback to the source derivation; forgetting tags may identify administrative syntax.

Each introduced positive macro vertex is logical or Ref. Thus elaboration neither creates a selected cone across a logical source boundary nor destroys a cone entirely inside a primitive source subtree. With corresponding exact hole signatures,

`ρ_ND E = (α ⊗ E) ρ_SC`.

This is a relative material-comodule comparison using two Hopf algebras. E is not asserted to be a full Hopf map: its logical macros have new internal ordinary CK cuts. Neither the full ND nor SC Hopf algebra is replaced by the material subalgebra.

The mixed signature comparison `Σ* E` accepts the declared passive cells: Cut through either tensor-right premise; Cut through the tensor-left continuation or its passive provider route when presented as elimination; Cut through implication right and either implication-left premise; primitive passengers through the unique active premise; and dependent/independent Cut–Cut reassociations. In every well-typed instance the free active Ref, or the surviving logical constructor, prevents a spanning pure cone on both sides. The maximal islands agree as exact indexed trees. Their token shells are ordinary substitution/commuting equivalents. This remains true after every final atomic probe substitution, so all finite coordinates agree. Bindings and source freshness conditions are part of the equations, not omitted side conditions.

The statement does not include a blanket principal or identity-cell descent. In particular

`Let Pair(δ,ε) as (x,y) in r(x,y)  →  r(δ,ε)`

creates the composite material coefficient on the right, and `x ≡L Id(x)` is separated by the pure-input probe mode. Those distinctions are required by the sharp no-go theorem. Thus the comparison reaches the full mixed **refined** carrier while retaining the proved obstruction to quotienting by the original unrestricted linear palette.

## 10. Deliverable status

The mixed structural completion, universal finite criterion, actual-hole refill law, comodule theorem and greatest-basis-equivalence comparison above are paper proofs. They retain full tensor–implication interaction and arbitrary compound free inputs. The separate checker supplies finite corroboration in its stated nonhypothetical executable fragment. Neither that checker nor this document is proof-assistant mechanization. The incremental contribution is the material-record realization and uniform CK-sensitive refinement in the mixed setting; ordinary mixed normalization and the abstract cofree construction are antecedents.
