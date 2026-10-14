# CK extraction spectra for closure migration

Status: original paper-level theorems and proofs plus finite executable checks, 12 October 2026. No Lean theorem, proof-equivalence quotient, native material-eligibility adapter, or claimed new global normalization result. Source: Aschieri–Ciabattoni–Genco, *On the concurrent computational content of intermediate logics*, author manuscript `literature_followup/concurrency.txt`, pp.14–17, especially Example 3.3. The paper supplies the reduction; all extraction-spectrum calculations below are ours.

## 1. A precise observable with an independent operational meaning

Use exact ordered term trees, retaining node kind, type, and rigid binder identity. For the operational fixture, channel application ch(a,u) is one unary node carrying a as a reference in its label: λL does not admit a standalone channel term. Ordinary application remains binary. Bound identities are globally distinct; public free variables have separately tagged identities. A lambda binder binds its child; a session binder binds all its process children. Copies rename binders declared inside the copied region and their references consistently. References to binders outside the copied region remain shared unless the enclosing region is also copied. Any installed payload must respect the stated capture/interface convention.

For a subtree U let D(U) be its typed external dependency interface: the free ordinary-variable and channel identities of U, with their types and roles. A leaf whose binder is above the root of U contributes an obligation. A binder inside U discharges its own references. Public inputs can either remain in D or be removed by an explicitly specified available-environment filter. D is an exact finite set of identities, not just a set of types.

An extraction frontier is an antichain of positive node addresses, including the empty frontier and the singleton whole-root frontier. Its factors are the complete subtrees at the selected addresses. They may be open; the full closed term need not have any free variables. This is the all-endpoint rooted-tree CK cut convention. It is not the assertion that every node is material-eligible in POTKIN3.

The operational question is: **what dependencies can simultaneous extraction expose, and with which physical-frontier multiplicities?** A single frontier is scope checking. The entire spectrum and its composition under session copying are the target here.

## 2. The coefficient algebra distinguishes two resource policies

Let M be a commutative monoid of resource observations and A=ℕ[M] its monoid semiring. Choose an observation d(U)∈M derived from D(U).

* Separate closure allocation: M is the free commutative monoid of typed dependency identities, and d(U) is the bag containing each needed identity once. Extracting two factors requiring the same identity counts two closure slots.
* Shared environment acquisition: M is the finite-set union monoid of typed identities. Monomials satisfy x_a²=x_a; extracting two factors requiring the same identity records one shared environment requirement. Coefficients still count both physical cuts—idempotence is in resource multiplication, not in addition.
* Full interface bundles: one generator for each finite typed D(U) records which dependencies occur together in a single closure. This retains more information than the first two choices.

Define

    Q_T = Σ_{C an addressed CK frontier of T} ∏_{v∈C} [d(T|v)].

The empty frontier contributes 1. Equal observable monomials add their multiplicities; no cut witnesses are deduplicated.

THEOREM 1 (CK semantics). On the rooted-tree Hopf algebra H over ℤ with exact typed decorations, let φ(T)=[d(T)], extended multiplicatively to forests, and ζ(T)=1, also extended multiplicatively. Then Q=φ*ζ, where convolution uses the CK coproduct with pruning forest first and remainder second. The ℕ-valued formula embeds in ℤ[M].

Proof. A CK coproduct summand is P_C⊗R_C. Applying φ⊗ζ gives precisely the product of the selected factors' observations. The full-root summand T⊗1 and empty-frontier summand 1⊗T give the stated endpoints. QED.

Do not infer that the globally well-typed closed terms form a Hopf subalgebra: cutting exposes open terms. The ambient algebraic carrier permits raw decorated trees with omitted premise slots after cutting; slot labels retain the original child positions, and dependency attributes remain total on those partial trees. Fixed-signature legal terms form the independently typed source slice, not a claimed closed Hopf subalgebra. Evaluating the remainder by ζ is a scalar observation, not identifying a typed Box with the coefficient unit in the proof-state carrier. A native proof/interface carrier comparison is still needed.

THEOREM 2 (exact recurrence). For a positive root r with children T₁,…,Tₖ,

    Q_{r(T₁,…,Tₖ)} = [d(r(T₁,…,Tₖ))] + ∏ᵢ Q_{Tᵢ}.

Proof. An antichain either contains the root, excluding every other address, or omits the root and restricts independently to an antichain in each child. This is a disjoint bijection, retaining addresses. QED.

The paired attribute (D,Q), rather than Q alone, is compositional. D is computed by taking the union of child interfaces and node-local references, then discharging the identities bound over each child. The root monomial uses that computed D. This requires no retention of the whole proof inside a semantic interface.

### Honest antipode specialization

Over ℤ[M], φ=Q*(ζ∘S), so one can recover local module contributions from an all-frontier census by convolution inversion. In this particular ζ specialization it collapses to the elementary subtraction

    φ(T)=Q_T−∏ᵢQ_{Tᵢ}.

This is a valid antipode interpretation, but should not be advertised as a difficult new antipode application. Negative intermediate coefficients are algebraic inclusion–exclusion, not negative operational obligations. The substantive result below is the spectrum's nonlinear transformation law.

## 3. Exact installed-macro expansion, including ancestor masking

Let C be a finite exact tree template with designated zero-node holes H, each with a matching payload P_h. Different physical holes may receive equal payload trees. C[P] is the filled tree. Let V(C) denote its positive template nodes.

For an antichain S⊆V(C), write H_S for holes with no selected template ancestor. Let C_v[P] be the filled subtree rooted at selected v. Then

    Q_{C[P]} = Σ_{S⊆V(C) an antichain}
                  (∏_{v∈S}[d(C_v[P])]) · (∏_{h∈H_S} Q_{P_h}).       (★)

THEOREM 3. Formula (★) is exact, including occurrence multiplicities and all endpoint cases.

Proof. Given a global cut, its selected positive template nodes form S. A hole below S is swallowed by the selected ancestor, so it carries no independent payload cut. At every unmasked hole, restrict the global cut to the installed payload; this is an arbitrary cut of P_h. Conversely these data select S together with the prefixed selected addresses of each surviving payload cut. Prefix incomparability is automatic inside a payload, between different holes, and between unmasked holes and S. These maps are inverse because every installed node is uniquely either a positive template node or a node inside one designated physical payload. Observations multiply over precisely the same selected subtrees. QED.

The selected ancestor weights in (★) may depend on the payload interfaces. They are not fixed coefficients unless the interface values are fixed. For free dependencies, that dependence is explicit:

    D(C_v[P]) = D_template(v) ∪ ⋃_{h below v}(D(P_h) \ B_C(v,h)),

where B_C(v,h) is the set of binder identities declared on the template path from v to h, and D_template(v) consists of the template's own references not discharged in that template subtree. Node-local binding scopes must be respected in defining the path set. This formula follows by classifying free references as template-local or belonging to one payload.

Thus a migration macro can be compiled as an expression in paired payload summaries (D(P_h),Q(P_h)). It need not revisit the payload trees to recompute every extraction frontier. This is a concrete compositional analysis benefit; no asymptotic superiority over all attribute-grammar implementations is claimed.

## 4. Copying is polynomial; physical equality does not identify occurrences

For a positive binary node f with two physical copies of P,

    Q_{f(P,P)}=[d(f(P,P))]+Q_P².

For P the variable leaf b and observation 'one obligation if b is free', Q_P=1+z and Q_f=z+(1+z)²=1+3z+z². The coefficient 3 distinguishes selecting the whole f-tree, only the left leaf, and only the right leaf. The two-leaf frontier contributes z².

If clone-local binders are renamed by ρ₁,ρ₂, the correct formula instead uses ρ₁(Q_P)ρ₂(Q_P). Shared external identities stay shared. Identifying both clones first can change an environment-union monomial x_{x₁}x_{x₂} into x_x and incorrectly predict one environment slot instead of two.

Ancestor masking is not optional: multiplying payload spectra counts cuts inside a payload even when a selected macro ancestor swallows it. Formula (★) excludes exactly those choices. Conversely merely replacing a primitive operation by its macro and assuming a Hopf morphism misses the new cuts internal to that macro. Neither shortcut is used here.

## 5. Coherence of two successive macro expansions

Suppose every outer hole h is filled by a template C_h with inner holes j, then by payloads P_{h,j}. There are two calculations: flatten all templates and apply (★), or first apply (★) to each C_h[P_h] and then apply it to the outer template.

THEOREM 4 (staged installed-spectrum coherence). The two expressions evaluate to the same polynomial, with a coefficient-preserving bijection of their summands.

Proof. A cut of the final tree has a unique highest selected layer at each root-to-leaf path. Record its selected outer-template nodes. Where no outer selected ancestor masks a hole, record selected inner-template nodes. Where neither layer masks an inner hole, record its payload cut. These three-layer records are exactly the data indexed by either parenthesization. Address prefixes compose associatively. If an outer node is selected, the entire inner record is absent, not an arbitrary discarded choice. Consequently no multiplicity is introduced by masked selections. Each corresponding selected factor is the same final subtree; dependency interface gluing is associative union with exact scope discharge, so coefficients coincide. QED.

This is a genuine installed-decomposition/copying coherence statement, not a global reduction confluence theorem. If two operational reductions overlap and produce different target terms, this theorem does not assert their spectra agree. It applies to two presentations of the same staged installation, and to sequential operational certificates whose exact output is known.

The McBride connection is precise: one-hole source contexts are instances of the derivative/context construction. Multi-hole templates and staged filling provide the substitution operation. Repeated providers give the polynomial powers and the cut-fibre expansion. A global Faà di Bruno Green-function identity would additionally require a specified aggregate and local-finiteness/symmetry conventions; it is not asserted here.

## 6. Actual Lin closure-migration reduction

The source's Example 3.3 has the schematic rule

    C[a u] ∥ₐ D[a v]
      → (C[v[b⟨x⟩/y]] ∥ₐ D[a v]) ∥ᵦ (C[a u] ∥ₐ D[u[b⟨y⟩/x]]),

where x are free variables of u bound in C, y those of v bound in D, b is fresh and correctly typed, and the paper's activity/rightmost-occurrence conditions hold. Copies have fresh internal binder identities. The tuples and their projections follow the source's exact typed substitution convention.

This contains two copies of each process context, one original and one adapted occurrence of each message, and fresh closure-reconnection syntax. Apply (★) to the exact expanded macro after exposing the variable-replacement positions in u and v. No assertion of primitive-to-macro coalgebra compatibility is needed.

For a fresh b let d_b(U)=1 if b is free in U, otherwise 0, and take A=ℕ[z]. Then

    Q_T(z)=Σ_C z^{number of extracted factors with a free b requirement}.

THEOREM 5 (exact fresh-channel width). Assume b occurs nowhere in the source and the substitution replaces every captured-variable occurrence by a term containing exactly one reference to b. Let N be the number of captured-variable occurrences replaced in the two adapted messages. For the full positive-node extraction carrier,

    deg Q_reduct(z)=N.

Proof. There are exactly N b-referencing channel-application nodes in the reduct. Any factor with a free b requirement contains at least one such node. Factors of an antichain are disjoint, giving at most N. Conversely choose all N inserted b-application subtrees as separate factors. They are pairwise incomparable because they replace distinct variable leaves and their argument tuples contain no b. Each exposes b, giving degree N. If N=0 the nonempty polynomial has degree zero. The session's outer b binder makes the whole reduct debt-free, but does not invalidate these open extracted factors. QED.

For tuple substitution implemented by projections, count the actual inserted b references rather than distinct variable names. If adapters share a single let-bound b application, N changes accordingly; the representation is part of the theorem.

For an arbitrary explicitly specified eligible-root predicate E, the exact recurrence becomes

    Q^E_T = 1_E(T)[d(T)] + ∏ᵢQ^E_{Tᵢ},

where the first term is absent when the root is ineligible. The degree=N theorem need not survive. The eligibility predicate must apply to each physical node in the actual installed source; if it depends on ancestry, carry that inherited state through the recursion. The native material predicate and its change under installation require their own existing bridge; logical roots must not silently be declared material.

## 7. An independently typed coefficient fixture

The displayed bare Example 3.3 term suggests the useful shape

    a(λx.a(z x) ∥ λy.⟨y,a(y k)⟩).

We do not presume this bare illustrative term has a common simple result type on both branches. Instead add explicit common-result wrappers, giving

    a(w(λx.a(z x)) ∥ r(λy.⟨y,a(y k)⟩)).

Let A,B,X,K,E be atomic types, Y=K→B, and take

    z:X→A, k:K,
    w:(X→B)→E,
    r:(Y→(Y∧A))→E.

In the left branch a:A→B; in the right a:B→A. Bind x:X,y:Y. Both branches have type E. Declare a active and its unique occurrences rightmost, so the schematic cross step applies.

The reduct is

    b(a₁(w(λx₁.(b x₁) k) ∥ r(λy₁.⟨y₁,a₁(y₁ k)⟩))
      ∥ a₂(w(λx₂.a₂(z x₂)) ∥ r(λy₂.⟨y₂,z(b y₂)⟩))).

The first outer branch uses b:X→Y and the second b:Y→X. Both remain E. All source/copy binders are distinct, and a₁,a₂ are the renamed session channels. The global free interface is precisely w,r,z,k in both terms. An executable independent type checker confirms these derivations for this fixture.

Application is binary; lambda and channel application are unary; pairing and session are binary; ordinary variable references are positive nullary nodes. Channel references are labels of channel-application nodes, not standalone positive leaves. These choices are explicit and affect numerical cut counts.

Under full positive-node eligibility:

    Q_source(z)=436,
    Q_reduct(z)=1+(232+262z)(240+256z)
               =55681+122272z+67072z².

There are 245,025 physical extraction frontiers in the target. Exactly 55,681 expose no b-dependent factor, 122,272 expose one, and 67,072 expose two. This is a census of possible extraction plans, not the number of simultaneous network communications. The source has no b references and 436 frontiers. The whole target has no free b despite its many open b-dependent factors.

`check_migration.py` computes these polynomials and checks this fixture's ordinary/channel typing and exact free interface. It also cross-checks the recurrence against explicit antichain enumeration on 570 small terms. This is executable finite evidence, not Lean and not a replacement for Theorems 1–5.

The results JSON also retains an earlier raw proof-style encoding of the bare source, yielding 289 and 9217+37056z+37249z². That earlier numerical fixture is not the certified operational instance: it has standalone channel-reference leaves and does not enforce common branch result types. It is retained only as an audit trail. The 436/245025 fixture above is the relevant operational benchmark.

## 8. Practical consequences and D1–D6

* **D2:** a local communication certificate propagates the exact spectrum through copying, inserted adapters and masking. It distinguishes original message occurrences from adapted clones.
* **D5:** a fragment closed under 'at most k simultaneously extracted reconnection requirements' has an exact local check deg Q≤k. The all-node case gives the captured-occurrence threshold N≤k for one fresh channel. This is a structural analysis property of extraction, not a claim about simultaneously executed network sends.
* **D4:** the cross-reduction macro can carry this certificate alongside a higher-level-rule/analytic-calculus translation. Composing certified installations does not require enumerating all frontiers again.
* **D1:** connect the concrete scope/interface certificate to independently typed reduction and then to the relevant proof-theoretic Cut obligation. That connection is not established merely by Q.
* **D3:** copying and fresh scope extension are handled explicitly; arbitrary formula-context weakening remains a separate assumption.
* **D6:** the term/proof or hypersequent translation must preserve the intended extraction interfaces or supply a comparison correspondence. The different internal cuts of macro expansions are accounted for, not assumed away.

These theorems use the CK coproduct positively as an exact spectrum semantics and composition discipline. An ordinary dynamic program can implement the same recurrence; this is an implementation of the algebra, not evidence against its utility. The remaining meaningful work is the native typed-carrier bridge and certificate transfer to the actual analytic proof transformations. No claim is made that CK alone proves the cited calculus's normalization or solves its first-order eigenvariable extension.

## 9. A stronger positive connection: derivatives are needed for closure adaptation

Whole-payload installation is compositional in (D,Q), but **substituting inside a message is not determined by that summary**. This is a concrete reason to add McBride context data rather than merely invoke its name.

Take x,g:A and a fresh unused lambda variable h:H. Let

    P₁ = ⟨x, λh.g⟩,
    P₂ = ⟨g, λh.x⟩.

Both have type A∧(H→A), the same free interface {x:A,g:A}, the same rule/variable occurrence inventory, one captured occurrence of x, and the same fresh-b spectrum Q=7. Let R=b y:A, where b:B→A and y:B. Under the canonical unary channel-application encoding, Q_R=2+z. Actual substitution yields

    Q_{P₁[R/x]}=6+4z,
    Q_{P₂[R/x]}=4+5z.

Proof by recurrence: Q_g=2 and Q_{λh.g}=3. The two hole contexts, when the inserted R has b free and h absent, have transfer polynomials

    F₁(X)=z+3X,
    F₂(X)=3z+2X.

Substitute X=2+z. The results differ although the source summaries, even strengthened with captured-occurrence count, agree. This example uses actual typed lambda/pair syntax; no invented unary operator is needed.

The repair is constructive. For an exact one-hole context C[-], there are functions A_C(s) and a coefficient B_C such that

    Q_{C[P]} = A_C(D(P)) + B_C Q_P,

where B_C is the product of Q for the sibling regions encountered along the root-to-hole path. A_C accounts for all cuts selecting an ancestor of the hole, with their actual interface-dependent weights. Both follow by induction along the path. This is the algebraic interpretation of the McBride zipper: each frame contributes its siblings and the ancestor alternative.

Consequently a same-interface edit has the exact update

    Q_{C[P_new]}−Q_{C[P_old]}=B_C(Q_new−Q_old).

For an interface-changing closure adaptation the exact formula is

    ΔQ_outer = A_C(D_new)−A_C(D_old)+B_C ΔQ_payload.

In the displayed example B₁=3 and B₂=2. The before-adaptation ancestor contributions are 1 and 3, while after adaptation they are z and 3z. This identifies exactly the information lost by the source census and exactly the two pieces required to repair the update: a position/context derivative and the ancestor-interface correction.

For multiple variable occurrences, compile a multiaffine polynomial in their distinct physical-hole summaries. Substituting the same adapter for several occurrences identifies those parameters and produces powers. If copied adapter environments differ by renaming, apply those renamings before identification. Staged substitution of these transfer polynomials is Theorem 4. An arithmetic circuit can retain the factorized form without expanding every coefficient.

This is the most promising incremental-analysis theorem in this note: **a closure-migration step can reuse the unchanged-message/sibling spectra, but it must update through the typed variable-position contexts.** Keeping only free variables and a whole-message census cannot do that. The derivative and CK observations therefore have distinct, cooperating roles.

## 10. Shared resources must not be converted to independent scalar counts

In the typed fixture, the z exponent counts **separate extracted factors requiring b**, not fresh channels. If the requested observable is the number of distinct fresh session identities required by a frontier, use z²=z. Its spectrum becomes

    55681 + 189344 z.

There is at most one fresh session identity, despite up to two separately extracted b-dependent factors. Endpoint types/roles should remain in the full interface even when this particular resource abstraction forgets them.

More generally, retain a dependency-set monomial [U]. The total number of assignments from q possible values to all dependencies of one frontier is q^{|U|}. Applying [U]↦q^{|U|} after forming the spectrum gives a useful linear census. But this map is NOT a semiring morphism from the union-monoid algebra: [U]²=[U], while q^{|U|}q^{|U|} generally differs from q^{|U|}. Independent multiplication of scalar assignment counts would silently freshen shared exterior variables. For joint logical validity or correlated probabilistic interpretation, use a matching kernel over boundary assignments, with diagonal identification of shared identities, before scalar evaluation.

This limitation does not invalidate Q=φ*ζ valued in the resource monoid algebra. It specifies where character semantics ends and boundary matching must enter. Clone-local binders and shared exterior identities require different maps, even if their types agree.

## 11. The derivative separator survives an actual full cross reduction

The context example can be embedded in two complete, independently typed Lin cross reductions. This is stronger than distinguishing anonymous trees.

Let U=A∧(H→A). Take public variables

    g:A, w:(A→V)→E, r:(V→U)→E.

Set P₁=⟨x,λh.g⟩ and P₂=⟨g,λh.x⟩ as before, and form

    T_i = a(w(λx:A.a^{U→V} P_i) ∥ r(λy:V.a^{V→U} y)).

Each branch has result E. The sole displayed a in each branch is rightmost; declare a active. The captured sender dependencies are exactly x:A, and the captured receiver dependency is y:V. The fresh b channel therefore has roles A→V and V→A.

Both sources have 14 positive nodes under the canonical channel syntax, the same constructor, variable-name/type, and connective-rule type-instance multiplicities, the same captured-variable multiplicities, the same whole free interface, and the same extraction polynomial

    Q_{T₁}=Q_{T₂}=172.

Their cross reducts have the common shape

    b(a₁(w(λx₁.b x₁) ∥ r(λy₁.a₁ y₁))
      ∥ a₂(w(λx₂.a₂ P_i[x₂/x]) ∥ r(λy₂.P_i[b y₂/x]))),

with fresh copied h binders. Both targets have type E, 29 nodes, the same constructor/connective-type-instance inventory and two inserted b applications. But the exact spectra differ:

    Q_{T₁'}=1+(36+46z)(228+210z)
           =8209+18048z+9660z²,

    Q_{T₂'}=1+(36+46z)(152+248z)
           =5473+15920z+11408z².

These formulas follow from the two context transfer polynomials z+3X and 3z+2X. They are also checked by the executable type/spectrum implementation. Thus **neither the source inventory, capture multiplicity, nor even the entire source b-spectrum determines the transformed extraction spectrum**. Position-sensitive context derivatives supply the missing information.

This is not a claim of equal exact native occurrence registries if those registries retain full scoped environments, or that a complete binding-incidence graph could not distinguish the sources: either can retain the missing information. The point is a constructive abstraction improvement. The compact source census must be supplemented with the specific context-transfer certificate, and that certificate predicts the nonlinear target spectrum without rescanning every extraction plan. The first version admits 8,209 b-independent target frontiers, the second only 5,473, despite identical coarse source analyses. Both still have maximum b-factor width two, so retaining the full spectrum is strictly stronger than retaining just its maximum degree.
