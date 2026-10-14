# Full typed cut packets and the context-coaction cocycle

12 October 2026. Original formulation and proofs for the present programme. This lifts the scalar extraction-polynomial law to full pruning/remainder data. It reuses the underlying native-style cut/filling geometry; it is not a claim that the already reported installed-cut bijection is newly discovered. The proposed advance is its operator/cocycle organization and its use as the precise compatibility law for analytic-rule and closure-migration macros.

No Lean theorem or native P-tree equivalence is claimed. The indexed signature and normalized coefficient/remainder distinction are the ones described in `polynomial_bridge.md`.

## 1. Typed states stay separate from coefficients

Fix a finitary indexed polynomial signature. An operation b has output colour i and a finite ordered family of input colours. Let T_i be its finite open trees with root colour i, including the zero-node interface tree Box_i. All-hole substitution requires exact matching colours.

Let M_i be the free abelian group on T_i. Distinct Box_i are distinct state basis elements. In particular a typed interface is not the coefficient unit.

Let H be the normalized coefficient algebra of positive P-tree forests: isolated identity-edge factors are sent to 1, while internal typed edges and their incidence remain in positive generators. Let q send a positive open tree to its coefficient generator, and Box_i to 1. This reduction occurs only in H. The rooted state module M still distinguishes all Box_i.

A full branch cut of t has:

* an addressed antichain of selected positive subtree roots, including possibly the whole root;
* an ordered packet of selected positive subtrees, using physical address order;
* the literal remainder with each selected subtree replaced by its own typed Box;
* the matching from each selected factor to its newly created remainder hole.

Inherited interface leaves are not extra selected factors. Box_i has one identity cut with empty packet and remainder Box_i. A positive t has a whole-root cut with packet [t] and remainder Box_root(t).

Define

    δ(t)=Σ_c q(P_c)⊗R_c ∈ H⊗M_root(t).

The full packet remains the primary indexing object. Tensor coefficients can merge equal observed summands, but never erase their multiplicities. The normalized P-tree construction provides the coefficient coproduct; the state coaction identity is justified by full cut-flag reindexing. A separate native implementation bridge remains necessary.

## 2. Exact one-hole packet bijection

Let C[-]:T_j→T_i be a typed one-hole context. Its hole lies at depth d. Enumerate the spine nodes from outer root toward the hole as v₀,…,v_{d−1}. At spine depth k, the distinguished child continues toward the hole and the other premise slots contain fixed sibling trees S_{k,l}.

Write C_{≥k}[P] for the complete filled subtree rooted at v_k. The prefix C_{<k} is the one-hole context above v_k; its hole has colour root(C_{≥k}[P]).

THEOREM 1 (full indexed packet equivalence).

    Cut(C[P]) ≅
      (Cut(P) × ∏_{all k,l} Cut(S_{k,l}))
      ⊔ Σ_{k=0}^{d−1} ∏_{r<k,l} Cut(S_{r,l}).             (3)

The first summand consists of cuts selecting no spine node. In the k-th second summand, v_k is the unique selected spine node. The products over empty families are singletons. If d=0 this reduces to Cut(P).

**Forward map.** A cut can select at most one spine node, since those nodes form a chain. If none is selected, restrict it independently to P and each sibling region. If v_k is selected, its subtree contains the entire remaining spine, the payload, and all deeper siblings. No cut choices exist inside those swallowed regions. At each strict ancestor v_r, r<k, restrict the remaining selections to its side siblings.

**Inverse map and full packet data.** In the first case prefix every payload/sibling cut address by its physical placement in C. Put its remainder in that position, leaving the spine nodes intact. The pruning packet is the merged list in global physical-address order, not an arbitrary concatenation in index order. The original relative addresses uniquely determine this merge and the factor-to-hole matching.

In the k-th second case select v_k itself and prefix the chosen ancestor-sibling cuts. The selected factor at v_k is literally C_{≥k}[P]. Replace it in the remainder by Box_root(C≥k[P]); replace each cut ancestor sibling by its own literal remainder. The resulting remainder is C_{<k}^{R_s}[Box]. Merge the ancestor-sibling packets with this one factor in the original ordered slots.

All selected addresses are incomparable. Every reconstructed factor is the original whole subtree at that address; every replacement Box has the same root colour. The two maps undo each other, preserve physical packets and their matching, and do not introduce choices hidden inside a selected ancestor. QED.

This theorem retains substantially more information than the scalar spectrum: both the literal remainder and the payload's location inside an ancestor-selected factor are preserved.

## 3. The coaction transport operator and ancestor term

Let G_C:M_j→M_i be the linear extension of P↦C[P].

Define L_C:H⊗M_j→H⊗M_i by summing over independent full cuts of **all** fixed side siblings. On a basis element h⊗R, a sibling-cut family contributes

    (h · ∏_{k,l} q(P_{k,l})) ⊗ C^{R_{k,l}}[R].

Thus L_C carries an already decomposed payload through the context while forbidding a cut at any spine node. Slot order and the typed grafting are preserved in the state; the coefficient forest multiplication is commutative only after the addressed packet theorem has justified the merge.

Define A_C:M_j→H⊗M_i by summing the second class of (3). At depth k and for a family of cuts in the strict-ancestor siblings, its contribution at P is

    (q(C_{≥k}[P]) · ∏_{r<k,l}q(P_{r,l}))
      ⊗ C_{<k}^{R_{r,l}}[Box_root(C≥k[P])].

Every term depends linearly on the basis payload P after extension. No cuts of P or deeper sibling regions appear in this term.

COROLLARY 2 (full context-coaction identity).

    δ ∘ G_C = L_C ∘ δ + A_C.                              (4)

Proof. Apply q to the pruning packet of the disjoint bijection (3), retaining its state remainder. QED.

The term A_C is exactly the correction that an assumed context/Hopf morphism would miss. It contains the payload inside newly selectable ancestor factors. For a unary rule frame b with no siblings, (4) reads

    δ(b(P)) = q(b(P))⊗Box_i + (id⊗b)δ(P).

This is the typed state version of the rooted-grafting cocycle form. With siblings, their full coproducts occur in L_C. One must not erase the typed Box_i in the state coordinate to turn this into an untyped identity.

## 4. A genuine context-composition cocycle

For contexts C:T_j→T_i and D:T_k→T_j, write CD[P]=C[D[P]]. Their spines concatenate.

THEOREM 3.

    G_CD = G_C G_D,
    L_CD = L_C L_D,
    A_CD = L_C A_D + A_C G_D.                             (5)

Proof. The first equation is typed substitution associativity. The no-spine cuts for CD are exactly independent cuts in the side siblings of both spines, establishing the second with the same literal remainder and packet matching. A selected spine node of CD lies either in C or in D. If in C, its selected factor swallows D[P], giving A_C G_D. If in D, no spine node of C is selected; its sibling cuts transport the D-ancestor packet by L_C, giving L_C A_D. These are disjoint, exhaustive alternatives. QED.

This admits an exact block-triangular representation:

    R_C = [[L_C, A_C],
           [  0, G_C]]

acting from (H⊗M_j)⊕M_j to (H⊗M_i)⊕M_i. Equation (5) says R_CD=R_C R_D. The identity context has L=id, G=id, A=0. The graph of δ is preserved:

    R_C(δP,P)=(δ(C[P]),C[P]).

Thus typed contexts act on a tree together with its full extraction certificate. The upper-right entry is a precise cocycle for this action. This does not assert a new theorem about arbitrary interacting Hopf algebras; it is an independently proved structure that gives the dictionary's rule/cocycle entry a concrete role in the current project.

## 5. The scalar derivative is a specialization, not an analogy

Let φ:H→A be a multiplicative coefficient observation and let ε_state(R)=1 on every state basis tree. Applying φ⊗ε_state to δ(P) gives Q(P). Applying the same observation to L_C(h⊗R) gives

    (∏_{all sibling regions}Q(S_{k,l})) · φ(h),

independent of the particular R. Hence the scalar image of L_C is multiplication by B_C, the product of sibling spectra. The scalar image of A_C(P) is exactly the ancestor contribution A_C(s_P), provided the root-weight observation factors through the supplied interface signature s.

Consequently (4) becomes

    Q(C[P])=B_C Q(P)+A_C(s_P).

The context derivative and ancestor-interface correction used in the actual Lin separator are therefore images of the full typed packet identity. They are not separate heuristic decorations of the CK recurrence.

The composition law becomes the affine chain law with correctly transported signatures. If an interface changes, A_C changes; that dependence cannot be discarded merely because the cut position remains the same.

## 6. Full multi-hole macro compatibility

For a template C with physical holes H, choose a template-node antichain S. Let U(S) be its unmasked holes, and let M(S)=H\U(S). Every masked hole lies below exactly one selected template node.

There is a full packet assembly map Γ_{C,S} which receives:

* the actual payload P_h at each masked hole h∈M(S);
* a complete payload cut packet (P^cut_h,R_h) at each unmasked hole h∈U(S).

It constructs the selected template factors by installing the masked payloads into the selected ancestor subtrees, joins their pruning packets with the unmasked payload-pruning packets in physical order, and constructs the remainder by filling the surviving template holes with R_h. Selected template roots are replaced by the correct typed Boxes. Inherited interface edges remain in the remainder.

The resulting exact equivalence is

    Cut(C[P]) ≅ Σ_{S a template-node antichain}
                       ∏_{h∈U(S)}Cut(P_h),               (6)

with full factor/remainder interpretation supplied by Γ. The masked P_h are fixed input data, not extra choices.

After linearization this gives the universal macro identity

    δ G_C(P_h) = Σ_S Γ_{C,S}((P_h)_{masked},(δP_h)_{unmasked}). (7)

It is a mixed expansion: an unmasked payload is decomposed, while a masked payload stays intact inside a larger coefficient factor. Formula (7), rather than δG=(G⊗G)δ, is the correct general compatibility law for expansion of a primitive operation into a proof macro.

For nested templates, both parenthesizations of (7) classify the same final cut by the layer containing its first selected node on each path. The packet factors, root-to-hole matchings and literal remainders agree under address-prefix associativity. This proves three-layer installation/cut compatibility before scalar observation. It classifies one final cut through syntax layers; the general iterated-coproduct cut-flag bijection is a distinct coassociativity obligation, provided elsewhere by the full P-tree construction. Observing (7) gives the multiaffine polynomial and Hasse chain laws in `migration_hasse.md`.

## 7. Literal copying versus mixtures of possible source proofs

A macro can use one literal payload P at several physical holes, with specified fresh renamings ρ_h. Formula (6) independently chooses a cut in each installed copy ρ_h(P), so the scalar expression contains ∏_hρ_h(Q(P)). This is the legitimate origin of powers Q(P)^m when the observation identifies the renamings.

However, a formal linear combination of alternative source proofs u=Σ a_t t represents a different object. Copying a single sampled/selected source requires the basis diagonal t↦t⊗t, extended linearly. It does not independently select one t for each copy. In particular

    Σ_t a_t Q(t)^m

is generally not

    (Σ_t a_t Q(t))^m.

The first correlates source choice; the second permits mixed source choices across copies. Independent cuts of one fixed copied source are correct; independent replacement of a shared source proof by different alternatives is not. This distinction is separate from—and compatible with—the shared-versus-fresh boundary-variable distinction.

## 8. What should be mechanized

The native report already supplies much of the one-stage installed-cut machinery. Do not implement a second competing cut syntax. The additional targets are:

1. Express the full indexed equivalence (3) using existing native addresses, branch cuts, positive packets, and typed remainder constructors.
2. Derive L_C and A_C by finite-sum reindexing; retain ordered packet evidence before projecting to commutative forest coefficients.
3. Prove the three equations (5) from the exact native context-composition/leaf-flattening law.
4. Instantiate coefficient observations only afterward, deriving the derivative and migration calculations as corollaries.
5. For the analytic-rule compiler, use (7) as its macro certificate. An atomic-to-synthetic expansion adds real ancestor/internal cuts, so a Hopf-morphism instance is neither needed nor presumed.

The mathematical additions here are the precise full-state macro law and its context-cocycle packaging. The computational payoff remains the independently defined analytic/migration certificate analysis, not the existence of another generic tree coproduct.

## 9. The counit gives a direct compositional certificate-update action

The block representation has an even sharper formulation. Let e_i=ε_H⊗id:M_H,i=H⊗M_i→M_i. Two identities hold:

    e_i L_C = G_C e_j,
    e_i A_C = 0.

For the first, applying ε_H kills every positive pruning factor, so only the unique empty cut in every sibling survives, leaving the original sibling tree in the remainder. For the second, every ancestor-selected term has a positive selected spine factor, so its coefficient has positive degree.

Define

    K_C = L_C + A_C e_j : H⊗M_j→H⊗M_i.

THEOREM 4 (direct context action).

    K_CD=K_C K_D,
    e_i K_C=G_C e_j,
    δ G_C=K_C δ.

Proof. Expand K_C K_D. The term A_C e_j A_D e_k vanishes; use e_j L_D=G_D e_k in the other cross term. Equation (5) then gives K_CD. The counit equation follows from the two displayed identities. Finally e_jδ=id_M by the state-coaction counit law, so K_Cδ=L_Cδ+A_C=δG_C. QED.

This shows why the counit is operationally relevant in the full certificate update. In δ(P), exactly the empty payload cut contributes 1⊗P. Applying e extracts that intact payload once, to construct the additional ancestor-selected factors. It suppresses all other payload-cut summands, preventing their decompositions from being spuriously counted inside an ancestor that swallowed them.

K_C is generally not H-linear, and the theorem does not call G_C a comodule morphism with the unchanged coefficient action. It is a separately constructed context action on the full extraction-certificate space. Its precise correction is what makes δ natural for this action. This is a stronger compositional statement than a scalar recurrence and uses the coefficient counit without collapsing typed state interfaces.

## 10. The whole typed context operad acts on extraction certificates

The direct lift extends to a template C with any finite physical hole family. With the notation of (7), define on arbitrary inputs z_h∈H⊗M_h

    K_C((z_h)) = Σ_S Γ_{C,S}((e_h z_h)_{masked},(z_h)_{unmasked}). (12)

All maps are multilinear in the distinct physical slots. The counit recovers intact payload state in exactly those slots masked by a selected template ancestor.

THEOREM 5 (linear-template lifting).

    e K_C((z_h)) = G_C((e_h z_h)),
    K_{C[D_h]} = K_C ∘ (⊗_h K_{D_h}),
    δ G_C = K_C ∘ (⊗_h δ).                              (13)

Proof of the first identity: e kills every term with a selected positive template factor, so only the empty-template selection remains. It then applies ε to each input coefficient, yielding G_C((e z_h)).

For composition, expand (12) for the outer template. At an outer masked hole, the first identity for its inner template recovers that entire inner filled state; no internal cut choice survives. At an unmasked outer hole, expand K_D into its own template selection and payload choices. These are exactly the nested presentations of one final template-node antichain. The full packet and literal remainder agree under slot/address composition. The unit one-hole interface template acts as identity. This proves composition on arbitrary tensor inputs, not only those already of the form δ(P).

For the third identity, apply (12) to δ(P_h), use e_hδ=id, and apply the full packet formula (7). QED.

Consequently the typed operad of linear open-proof templates has a representation by the lifted multilinear operators K_C on the extraction-certificate spaces H⊗M. The coaction δ intertwines the original proof operations G_C with these lifted operations. This is an explicitly defined operadic compatibility structure, not an appeal to an unspecified 'interacting Hopf algebra' theorem.

For a single rule b with input basis tensors h_i⊗R_i, the lifted operation has the particularly transparent form

    K_b(⊗_i(h_i⊗R_i))
      = (∏_i h_i)⊗b(R_i)
        + (∏_i ε(h_i)) q(b(R_i))⊗Box_out(b).

The first term keeps the rule in the remainder. The second selects the whole rule-rooted subtree and is enabled only when all incoming coefficient packets are empty. Iterating these lifted rule operations computes the complete extraction certificate. Existing native branch-cut bijections can establish this before installing tensor/Hopf typeclasses.

Certified copying/deletion is then a separate structural wiring layer on physical slots, as described in `macro_defect.md` §9. This preserves the distinction between linear operadic composition and substructural admissibility while placing both inside one explicit CK-based analysis framework.
