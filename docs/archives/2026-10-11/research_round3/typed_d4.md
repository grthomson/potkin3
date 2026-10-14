# Typed D4: exact regular filling contracts and CK frontier queries

Working theorem note, 11 October 2026. This extends Round 2's ordinary inverse-cut recognizer to a **different, explicitly typed relation**: exact filling of recorded slots. It does not silently identify this action with the ordinary CK convolution. The elementary automata construction is standard in character; the prospective project contribution is the combined logical instance and CK frontier application, not a claim to invent regular tree substitution.

## 1. Carrier and scope

Fix a finite set S of exact interface sorts and a finite ranked, sorted signature Σ. Every rule r has an ordered list of input sorts (s1,...,sk) and one output sort s. A complete derivation is a well-sorted finite Σ-term. A context is such a term with some leaves replaced by distinct typed holes □s. Holes are ordered by planar traversal. Native slots remain present when a premise subtree is extracted.

The mathematical claim applies to a calculus only after proving that its native checker is represented by this signature. Global channel freshness, discharge, equality constraints, or joint resource conditions are not automatically local sorts. A finite exact rule-instance registry is a genuine restriction, not a presentation of all unbounded formulas or contexts of a full sequent calculus. If a further finite-state checker suffices for the desired native condition, take a product with it; if not, the theorem does not establish exact native recognizability.

For complete term T and any prefix-free vertex set c, extraction gives an ordered tuple P_c of complete subtrees and a context R_c with corresponding typed holes. An empty c gives R=T; selecting the root gives one bare typed hole. Nonroot c are ordinary proper CK edge cuts. Root selection is a **pointed context convention**, not a claim that the Hopf algebra unit is a typed hole.

## 2. Finite observations

A complete-provider observer consists of finite sets U_s and transitions u_r:∏U_si→U_s. A finite monoid M and maps η_s:U_s→M recognize a language A of ordered provider tuples by

    (P1,...,Pm)∈A iff η(α(P1)) ... η(α(Pm)) ∈ F_A.

This covers usual recognizable forest languages using their horizontal monoid. The state product retains order and can express joint restrictions across holes. A family of independent allowed-provider languages is only a special case.

The target property C has finite sorted states Q_s, transitions q_r:∏Q_si→Q_s, and accepting sets F_s. Let β be its evaluation. Simultaneous reachable pairs

    E_s = {(α(P),β(P)): P complete of sort s}

are obtained as the least sorted family closed under the simultaneous transitions (u_r,q_r), starting from nullary rules. This fixed point is finite and exact by induction on terms. Store a constructor witness per new state. Uninhabited sorts have E_s=∅.

## 3. Exact residual theorem

For context R of output sort s define

    V(R) = {(ηα(P1)...ηα(Pm), β(R[P1,...,Pm])):
             Pi complete of the sort of hole i} ⊆ M×Q_s.

The following finite recursion computes V exactly:

    V(□s) = {(η_s(u),q):(u,q)∈E_s};
    V(r(R1,...,Rk)) = {
       (m1...mk, q_r(q1,...,qk)) : (mi,qi)∈V(Ri) for every i }.

For k=0 the result is {(1_M,q_r())}. Thus a closed context has exactly {(1_M,β(R))}.

**Theorem.** The contexts R such that every compatible provider tuple from A yields a filled proof in C are recognized by this finite sorted algebra, accepting precisely

    V(R)∩(F_A×(Q_s\F_s)) = ∅.

**Proof.** At a hole the fixed point describes exactly all complete typed providers. At a rule node, each filling uniquely splits across its ordered child contexts. Their provider words concatenate in child order, and the target observer follows its rule transition. Conversely any choice of child witnesses gives a well-sorted parent filling. Structural induction proves the recurrence's exact semantic equation. The displayed acceptance condition is then literally universal implication. No assumption of independent acceptance per hole is used. QED.

At most 2^(|M||Q_s|) states of sort s are required. This is an unbounded-tree theorem; it is not bounded term enumeration. State explosion remains possible. The reachable-pair fixed point can provide a concrete violating tuple whenever the acceptance condition fails; contextual recursive witnesses reconstruct the assembly.

### Nonvacuity is a separate question

When no tuple in A can fill R, its universal contract holds vacuously. A useful provider protocol can require also

    V(R)∩(F_A×Q_s) ≠ ∅.

Do not silently turn universal validity into feasible installation. The same finite state decides both conditions.

### Why Round 2's inverse recurrence cannot simply be reused

There are no arbitrary E factors before or after a retained root: those represented independently detached whole components in ordinary CK inverse assembly. Nor can a fixed nullary rule grow children to consume new material. A context's exact holes prescribe the number, sorts, and positions of providers. For r(□s), all providers go into that recorded slot; for a closed nullary term there are zero provider slots. The typed-hole theorem is a corrected application gate, not a notational specialization of unranked grafting.

## 4. Compiling the residual into an all-frontiers CK analyzer

Let D_s be any finite observer of typed contexts, with root transition d_r and hole state h_s. In particular take D_s=2^(M×Q_s) and d_r from Section 3. For a complete term T define two finite sets:

    Z(T) = {d(R_c(T)): c any vertex antichain, root allowed},
    Zproper(T) = {d(R_c(T)): c any vertex antichain excluding root}.

Then

    Zproper(r(T1,...,Tk)) = {d_r(z1,...,zk): zi∈Z(Ti)},
    Z(r(T1,...,Tk)) = Zproper(r(T1,...,Tk)) ∪ {h_s}.

For a nullary term the first equation supplies the sole uncut term state. The h_s alternative selects the entire subtree and prevents descendant choices: it is exactly the antichain condition. Induction proves equality, not merely overapproximation.

Consequently one can decide, over unbounded complete proofs in this finite registry, whether some or every proper CK frontier has a remainder satisfying the universal correlated filling contract. This runs bottom-up without enumerating exponentially many frontiers explicitly, though the finite state space itself may be large. For existential failure, carry one chosen antichain for each state; combine it with Section 3's violating provider witnesses. The resulting counterexample contains a native source proof, a concrete admissible cut, exact typed hole placements, a provider tuple satisfying A, and a filled proof rejected by C.

Material restrictions on the *original* extracted subtrees can also be tracked: augment each frontier state with a finite provider-word observer, combining by ordered product at a retained node, and using the complete-subtree observer at the root-selected alternative. This is the typed version of CK's product/grafting cut recursion. It allows the question to concern, for example, only frontiers composed of designated material rules.

**Important:** this analyzer observes the positive combinatorial CK cut relation, before collecting equal algebraic tensors. It does not assert that its finite states are a Hopf quotient, that booleanization preserves coefficients, or that signed antipode cancellation eliminates counterexamples.

## 5. Staging and the already-established masking theorem

For an outer context R and inner contexts N_i at its holes, evaluating V(R[N_i]) directly gives the same result as substituting the finite relations V(N_i) into the expression computed for R. This follows from structural substitution and associative multiplication in M. The resulting provider word is the planar concatenation of the N_i leaf-provider words, and β is computed by the same composed native transitions.

This does NOT authorize testing each inner context against an independently chosen marginal language. A correlated global A can couple providers belonging to different N_i. Exact staging must retain the monoid contribution m alongside the target state q, or propagate an equivalent relational contract. Projecting away m before outer composition can admit tuples excluded by A or lose its obligations.

For CK extraction, the project already proved the more specific witness theorem: cuts of R[N_i] are uniquely an outer antichain plus pointed inner antichains at unmasked holes; selecting an ancestor in R swallows the complete installed N_i below it. The finite recurrence in Section 4 respects that masking by making root-selection and descendant-selection alternatives mutually exclusive. Therefore staged CK frontier analysis agrees with direct analysis whenever the complete-subtree summary required by a masked outer selection is retained. This is an application of the existing theorem, not a new simultaneous-opening theorem.

## 6. What is and is not substantive CK work

The finite inverse filling contract by itself is ordinary typed context/automata mathematics. CK contributes when the question quantifies over **all compatible antichain frontiers** of an actual derivation, when decomposition witnesses must be retained, and when analyses are transported through nested installations using the masking law. The root-selected alternative and its exclusion of nested cuts are necessary: treating arbitrary independent vertex selections as a cut gives false frontiers.

The result is still a method for analyzing proof syntax. To conclude a useful fact about structural proof theory, instantiate C with an independently justified proof property—e.g. a natural rule-side-condition invariant or a bounded fragment known to admit a normalization procedure—and prove what acceptance entails. An ancestry toy property or a height budget alone does not discharge that application obligation.

No Cut-elimination result, no semantic process-safety result, no use of the antipode, and no novelty beyond standard automata constructions is asserted here. The useful candidate is the combined frontier-contract compiler and a defensible logical instance supplied separately.

## 7. Endpoint and carrier audit

Three objects must remain distinct:

1. A bare typed hole □s is an identity for typed filling, and there is one for each exact interface.
2. The empty forest 1 is the single monoidal unit of ordinary CK.
3. A positive open residual retains actual rule vertices, exact slots, and any pre-existing holes.

A polynomial/P-tree bialgebra can retain residue group-likes; a reduced connected Hopf presentation can identify appropriate residue classes with 1. Either requires a precise construction before claiming that the context action is literally a coaction of that Hopf algebra. The proof above needs neither identification: it uses occurrence-level cuts and their exact pointed residual contexts. Ordinary CK's whole-root term T⊗1 can be represented separately as a cut witness with external typed identity adapter, but 1 must not become a proof of every interface.

The recovered 1 October ledger's L0 takes positive open trees as generators and formal empty endpoints. Its finite cut-chain argument should be audited against the exact address/hole equivalence of the intended native carrier; this note neither refutes nor silently assumes it. The current D4 theorem remains valid as a finite sorted context-action theorem independently of that audit.

## 8. Recovery comparison

Read: research_round2/regular_residual_theorem.md; research_round2/d4_addendum.md; recovered/CK_FORMAL_PROOF_LEDGER_2026-10-01.md (L0,T2,T3,T4); recovered/CK_HIGHER_ORDER_PROOF_AND_NOVELTY_AUDIT_2026-10-05.md; recovered/CK_PROOF_EQUIVALENCE_AND_JOINT_REPLACEMENT_2026-10-08.md.

Old work already supplies typed extraction/refilling, correlated contracts, masking, and simultaneous-opening bijections. New relative to those notes is only the explicit finite recognizer/compiler for universal **regular correlated provider** contracts and its systematic nesting inside the CK-frontier observer. Publication novelty is not established. Native applicability still depends on the finite exact checker and an independently useful target predicate.

## 9. DFA presentation and a natural proof-theoretic instance

The implementation uses an equivalent, sometimes smaller formulation. Let W be the states of a DFA recognizing admissible provider words, and let each provider-observation letter act on W. A context summary is a relation

    V_DFA(R) ⊆ W × Q_s × W,

recording initial provider-word state, resulting target-proof observation, and final provider-word state. At a hole insert every realized provider letter/target-state pair. At a rule, concatenate the child relations through intermediate DFA states and apply the native target transition. Accept the universal contract when no triple starts at the initial DFA state, ends at a provider-accepting state, and has a target-rejecting middle state. Taking M to be the DFA transition monoid gives Section 3; neither construction requires independent provider sets.

### Demand-vector instance (conditional on the separate normalization lemma)

The accompanying natural-application work studies a precise positive exponential term fragment with variables, a pure constant a:p, a counted material operation g:p→p, an uncounted opaque binary operation m:p,p→p, tensor pairing, promotion (!), and let !x=P in Q. The binary operation permits arbitrarily large duplication demand at a fixed output type p. Every local judgment Γ⊢A is an exact sort; Γ records the unrestricted variables and their types. A complete proof tree may have assumptions in Γ; 'complete' here means no meta-holes, not an empty object-language context.

Its independent semantic lemma assigns the affine demand vector

    D(t)=(c(t),(d_y(t))_{y∈Γ})

such that the number of g occurrences in the normal form after closed substitution is

    c(t) + Σ_y d_y(t) · count_g(NF(U_y)).

At let !x=P in Q, the components satisfy

    c = c(Q) + d_x(Q)c(P),
    d_y = d_y(Q) + d_x(Q)d_y(P).

This records surviving occurrences in the normal form, not evaluation steps or runtime cost. A discarded argument can contain arbitrarily many g occurrences while contributing zero to the final normal form.

For fixed B≥0, clipping each component to {0,...,B,B+1} is exact for the predicate count_g(NF(t))≤B: capped addition and multiplication are a semiring quotient of the nonnegative integers. In particular 0·(B+1)=0. For exact finite Γ and finitely many rule instances, this gives a finite sorted target observer β. The unbounded result applies to proof trees over that registry, not merely to trees up to the executable search depth.

Section 3 now synthesizes the exact condition on a typed open proof skeleton ensuring the normalized result stays within budget under every permitted provider tuple. At the two-hole skeleton let !x=□P in □Q, the condition includes the genuine joint relation

    c(Q)+d_x(Q)c(P) ≤ B

when the outer context is empty. Independent provider guarantees generally lose precision: the acceptable cost of P depends on the consumer's duplication coefficient. Across a fixed host's possible extraction frontiers, Section 4 computes precisely which CK antichains admit this universal contract, respecting the actual position of the nonlinear constructor.

The logical theorem is the separately proved normalization/demand lemma. The CK theorem is the extraction-frontier compiler and its compatibility with typed nested filling. Their combination yields a proof-normal-form resource certificate; it is not a general theorem of Cut elimination for added structural rules. The fragment excludes any constructor whose demand behavior has not been established by the normalization lemma. A finite exact registry can bound available formulas or variable interfaces while allowing arbitrarily large derivations built from those instances.

### Refined carrier bridge from the independent audit

The carrier audit supplies a concrete algebraic construction suitable for these statements. Let B be the planar sorted P-tree bialgebra retaining the degree-zero trivial edge e_s at each sort. Its cut coproduct retains a full pruned frontier: every leaf edge of the retained subtree contributes its ideal upper subtree, including a compulsory e_s at an already empty input. These trivial contributions are not independent choices. Let q:B→H identify every e_s with 1, obtaining the reduced connected CK-type Hopf algebra. Then

    λ=(q⊗id)Δ_B : B→H⊗B

is a counital coaction. It has λ(e_s)=1⊗e_s and whole-tree term q(T)⊗e_out, preserving the typed identity on the residual side. This supplies a genuine CK material coaction without declaring every typed identity to be the ordinary algebra unit. See carrier_audit.md for proof and source boundary.

The material factor q erases compulsory trivial-edge factors, leaving the ordered positive selected-subtree tuple used by the finite analyzer. For closed syntax trees the residual holes are precisely the newly cut positions. For an already open host, however, residual holes can be inherited or newly cut, and equal sorts alone do not distinguish them. Exact refilling or staged provider allocation must retain the cut's occurrence-address witness, or explicitly mark inherited versus fresh holes in the context alphabet. A collected coefficient tensor alone is not enough. The theorem in Sections 3–4 starts with a complete syntax tree and so avoids this ambiguity; its staged extension keeps the existing address witnesses.


### Concrete finite registry strengthened by the natural-application worker

A particularly small exact instance needs the closed sorts p and !p and the consumer sort x:p⊢p. Closed providers are built with a, g, m, promotion, and closed lets; open consumers use x,a,g,m and no nested open let. The closed-let constructor has premise sorts ⊢!p and x:p⊢p and conclusion ⊢p. Thus there is no covert appeal to infinitely many context sorts. Open consumers m(x,x), m(m(x,x),x), etc. have unbounded demand while remaining in the same judgment. Nested closed lets can repeatedly duplicate material while retaining output p. This exact finite registry already supports the nonlinear joint contract. More expressive contexts or connectives require their own checker and observer proof.

### Query discipline: source material and replacement policy are separate

A cut's original material tuple P_c and its future replacement tuples play different roles. Let A_old select frontiers by properties of what is currently extracted, and let A_new constrain permitted replacements. Build the residual recognizer using A_new; track a separate finite word action for A_old in the cut recursion. Reusing one language for both is a valid special case but is not forced by the theorem. For example, migration may deliberately replace material outside the new policy, so requiring P_c∈A_new would exclude the very repair frontiers sought.

Likewise, a universal guarantee has two possible scopes: 'every allowed replacement for this fixed cut' and 'every cut selected by A_old has that guarantee'. Section 3 proves the first; the set-of-states CK recursion decides the second. Neither implies that arbitrary cut-free fragments or arbitrary added rule bases satisfy the property.
