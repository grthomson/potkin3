# Positive cut defects for linear analytic-rule compilers

12 October 2026. Paper-level construction and proofs, no Lean. This is a proposed full compatibility theorem for D4's primitive-to-analytic-macro expansion. It replaces an unwarranted Hopf-morphism claim by an explicit, positive and compositional correction.

## 1. Compiler hypotheses

Let P and Q be typed polynomial rule signatures. Work with their exact open trees, physical premise slots and typed interface states; no proof-equivalence quotient is assumed. Fix a map on boundary colours.

For every exact source operation b, choose one target open macro M_b satisfying:

1. Its output colour is the translated output colour of b.
2. It has exactly one designated hole for each physical source premise slot, with the translated input colour, and no unaccounted open inputs. A source with repeated premise formulas still has separate physical slots.
3. Each designated hole occurs exactly once. Thus this is a linear macro compiler on proof operations, not a copying or deleting rewrite.
4. The macro has at least one positive node, so its output root is a genuine node distinct from every installed premise root.
5. Choices and any freshness renamings are consistent under recursive installation and restriction to a source subtree. One implementation is to give source occurrences stable origin tags, and name each introduced binder by its source origin and local macro address. Then translating a detached subtree uses the same fresh identities as its installed translation. If names are generated from a new local root instead, retain the explicit renaming isomorphism and do not claim literal equality. Origin addresses/seams are retained. All scope/interface adapters needed for the chosen boundary colours are part of the compiler specification, not inferred from endpoint typing alone.

Extend recursively to τ on open source trees, taking Box_i to Box_{τi}. At a node b, fill M_b with the translations of its premise subtrees. Extend τ multiplicatively to forests to obtain an algebra map f:H_P→H_Q on normalized coefficient algebras, and linearly on rooted states to obtain g:M_P→M_Q. The unit and endpoint reductions are respected; typed Boxes remain distinct in M.

These assumptions fit a compiler of a synthetic rule into its fixed derivation with one use of each physical premise. They do not automatically fit cut reduction with copying. Nonlinear rewrites use the occurrence-sensitive installed-template law instead.

## 2. Aligned cuts are exactly source cuts

In τ(t), mark the root of each installed macro instance as the seam corresponding to its source node. Positivity and linearity imply an injective map from source node addresses to seam addresses, preserving and reflecting strict ancestor order. Proof is by induction: different premise slots install into different incomparable macro holes, and each installed premise root lies strictly below the macro's positive root.

Call a target cut aligned when every selected positive root is a seam. The empty and whole-root cuts are aligned. Interface identity cases are handled separately by the unique cut of Box.

THEOREM 1. Source cuts are in bijection with aligned target cuts, preserving the full pruning packet, literal translated remainder, factor-to-hole matching, and multiplicity.

Proof. Send each selected source address to its seam address. Ancestor incomparability is preserved and reflected, so this is a bijection of antichains. The detached target subtree at that seam is the literal translation of the detached source subtree. Replacing it with a typed Box commutes with recursive macro expansion, since the compiler is linear in that premise slot and sends source Box to translated Box. Thus the target remainder is the translation of the source remainder. Original slot incidence determines the packet correspondence; target physical traversal may order slots differently from the source, in which case retain the explicit induced matching rather than assert identical left-to-right list order. QED.

No premise-order-preservation assumption is needed for the commutative forest tensor identity below. If a native theorem requires identical ordered packets, add order-preserving hole placement or retain the induced permutation explicitly.

## 3. The defect is positive despite its subtraction notation

Let Δ_P,Δ_Q be coefficient coproducts and δ_P,δ_Q the rooted state coactions. Define

    D = Δ_Q f − (f⊗f)Δ_P,
    E = δ_Q g − (f⊗g)δ_P.

These expressions are written over abelian groups, but Theorem 1 proves that both differences are positive cut sums on each basis source forest/tree:

* D(t) sums exactly target cuts having at least one selected root that is not a source seam, with both coordinates interpreted in H_Q.
* E(t) sums the same additional cuts while retaining the literal target remainder in M_Q.

The target full coproduct/coaction is therefore the transported source decomposition plus the exact family of newly introduced macro-internal extraction interfaces. The complement includes mixed cuts selecting both seams and nonseam roots; it is not limited to cuts entirely inside one macro.

For a source forest, aligned means aligned in each component. Multiplicative extension and distributivity give the corresponding positive complement: at least one component contributes a nonaligned cut. D need not be multiplicative; its forest rule contains the expected mixed terms.

A nonzero D or E is not a failed compiler. It records precisely why a proof macro generally is not a Hopf morphism. Those new interfaces are the additional relative obligations the compiler must analyze.

## 4. Compiler composition has an exact positive correction law

Let a second compiler σ:Q→R satisfy the same hypotheses. Write its coefficient/state maps as u,v and its defects as D_σ,E_σ. The composite maps are uf,vg.

THEOREM 2.

    D_{στ} = D_σ f + (u⊗u)D_τ,
    E_{στ} = E_σ g + (u⊗v)E_τ.                          (8)

Proof by algebra: insert and subtract (u⊗u)Δ_Q f, respectively (u⊗v)δ_Q g, and collect the two defects. Proof by cut indices: a target cut is either nonaligned with the latest σ macro seams, or aligned with σ but its corresponding Q-cut is nonaligned with the earlier τ seams. These cases are disjoint and exhaustive. Their factors and remainders give precisely the displayed terms. QED.

Thus the positivity of the correction is preserved under staged compilation. A previously computed correction can be transported and combined with the interfaces introduced by the next compiler; there is no need to pretend the previous expansion preserved every cut.

## 5. Coassociativity imposes a precise defect identity

THEOREM 3 (coefficient coherence).

    (Δ_Q⊗id)D + (D⊗f)Δ_P
      = (id⊗Δ_Q)D + (f⊗D)Δ_P.                         (9)

Proof. Substitute Δ_Q f=(f⊗f)Δ_P+D into

    (Δ_Q⊗id)Δ_Q f=(id⊗Δ_Q)Δ_Q f.

Both sides contain (f⊗f⊗f) applied to the two parenthesizations of the source coproduct. Source coassociativity identifies those terms; cancel them. The four remaining terms give (9). QED.

This identity is a target theorem for the correction map itself. It states how decomposing a newly exposed interface interacts with an earlier source decomposition. We do not use the undefined phrase 'Hochschild cocycle' as a substitute for the displayed equation.

For rooted states, the two defects interact:

THEOREM 4 (mixed coaction coherence).

    (Δ_Q⊗id)E + (D⊗g)δ_P
      = (id⊗δ_Q)E + (f⊗E)δ_P.                        (10)

Proof. Expand the target coaction identity

    (Δ_Q⊗id)δ_Q g=(id⊗δ_Q)δ_Q g

using δ_Q g=(f⊗g)δ_P+E and Δ_Q f=(f⊗f)Δ_P+D. The transported source coaction identity cancels the common terms, leaving (10). QED.

The coefficient defect D cannot generally be omitted from (10). Omitting it would silently reinstate the blocked assumption that f is a coalgebra morphism. The typed state coordinates—including Box colours—remain untouched by this calculation.

## 6. A small explicit nonzero defect

Take a source unary constructor b and a target unary macro a(c([-])). Let p be a source payload and let x=τ(p). The compiled tree is a(c(x)). Consider the additional target cut selecting the internal c(x) root. It contributes

    q(c(x)) ⊗ a(Box)

to E(b(p)). This root is not a source seam: the b seam is the a root, and payload seams lie inside x. The corresponding source cut does not exist. It is a concrete positive defect term, not an axiom-level failure of the construction.

Further target cuts can occur inside the translated payload. Those are already represented by the payload's recursively compiled defects. The full one-hole law in `context_coaction.md` organizes both contributions and their literal remainders.

## 7. Relation to the constructive programme

This gives D4 a precise comparison structure for analytic rule expansion:

* the source cut obligations have exact aligned images;
* the compiler exposes a positive, explicitly indexed additional family;
* those corrections compose by (8);
* their iterated decompositions satisfy (9)–(10).

An interface-valued certificate interpretation can be applied to these full tensors. D1's remaining proof-theoretic task is to show that the independently defined Cut/revival obligations are satisfied on the transported part and on the added interfaces. The algebra does not establish that logical theorem merely by counting cuts.

D5 can ask whether a certified interface fragment is closed under the compiler's added interfaces. The possible extra interfaces are now concrete data, rather than an undifferentiated failure of compatibility. D6 can compare two presentations using their compiler maps and correction laws even when neither direction is a Hopf morphism.

The new relative object is the pair (f,D), or (f,g,D,E) with typed states, together with its proved composition/coherence laws. It is a workable replacement for the earlier overly strong compatibility demand. It should be instantiated on one actual positive linear analytic macro before any broad library abstraction is built.

## 8. The positivity assumptions are necessary: two exact counterexamples

Take one boundary colour, a nullary source rule c and a unary source rule b. Write Box for the typed zero-node state.

### Erasing a positive source node

Let τ(c)=c and let the b macro be the bare hole, so τ(b(P))=τ(P). This violates positivity. The source state coaction is

    δ(b(c))=q(b(c))⊗Box + 1⊗b(c) + q(c)⊗b(Box).

Its transported value is

    q(c)⊗Box + 1⊗c + q(c)⊗Box,

whereas δ(τ(b(c)))=δ(c)=q(c)⊗Box+1⊗c. Therefore

    E(b(c))=−q(c)⊗Box.

The two source roots collapse onto one target root, so the aligned-cut injection fails and the correction is not positive.

### Copying a physical premise

Instead let τ(b(P))=f(τ(P),τ(P)), where f is a target binary rule, and τ(c)=c. This violates linearity. The transported source child cut contributes

    q(c)⊗f(Box,Box).

But the target cut that exposes both copies contributes

    q(c)²⊗f(Box,Box),

and its one-copy cuts have remainders f(Box,c) and f(c,Box). Thus E(b(c)) contains the negative coefficient

    −q(c)⊗f(Box,Box),

alongside positive terms. There is no target physical cut producing the transported source summand. Copying needs the physical-hole/diagonal law of `context_coaction.md`, not the positive-linear-compiler theorem.

These examples explain why linear analytic-rule expansion and nonlinear operational normalization are complementary but distinct avenues. Their compatibility laws share the same full cut machinery, while their compiler assumptions must remain separate.

## 9. Polarization combines the two avenues without conflating their hypotheses

A finite copying macro can be presented by a linear physical-hole template C with hole set H, a source-premise set I, a provider map π:H→I, and compatible fresh renamings ρ_h. Its action on literal source providers is

    (P_i)_{i∈I} ↦ C[(ρ_h(P_{π(h)}))_{h∈H}].

This factors into two different operations:

1. A structural wiring step copies or omits providers according to π, with the prescribed binder renamings.
2. A positive linear macro fills each resulting physical hole exactly once.

The positive defect theorem applies to the second layer. The full installed-cut/Hasse law applies to the first layer's independent extraction choices in copied providers. If a source provider is unused, that is an explicit deletion, not a disappeared term in a supposed coalgebra morphism. If a provider is copied, its physical cut choices remain separate even though its syntax is shared.

This factorization is always a syntactic presentation of a finite template. Its logical admissibility is a separate obligation: a substructural base need not support the contraction or weakening represented by π. Copies, deletions, scope renamings and any formula-context lifts must carry their actual structural certificates. Thus D2 and D3 provide the admitted wiring operations; D4 supplies the linear analytic macros; D1 and D5 test the resulting cut/interface obligations; D6 compares whole certified presentations.

No Grossman–Larson replacement of the CK carrier is involved. The rooted-cut Hopf/coaction structure remains the decomposition structure. Typed substitution and certified structural wiring act on it by the explicit compatibility and correction laws above.

## 10. A genuine Hopf consequence: correcting antipode transport

The defect also determines the failure of antipode naturality. This is distinct from merely rebranding the extraction recurrence.

Assume H_P,H_Q are the connected normalized Hopf algebras above. The positive compiler algebra map f preserves counits. Let S_P,S_Q be their antipodes, and let *_P denote convolution on Hom(H_P,H_Q) using Δ_P and target multiplication μ_Q. Define

    K = μ_Q (S_Q⊗id) D.

THEOREM 5.

    S_Q f = f S_P − K *_P (f S_P).                     (11)

Proof. Apply μ_Q(S_Q⊗id) to Δ_Q f=(f⊗f)Δ_P+D. The target antipode identity and counit preservation give

    (S_Q f) *_P f = ηε_P − K.

Because f is an algebra map, f S_P is the two-sided convolution inverse of f. Convolve the displayed equation on the right with f S_P and use associativity. This gives (11). QED.

There is also the symmetric left equation using K'=μ_Q(id⊗S_Q)D. No commutativity assumption is needed for the displayed order of the convolution factors.

For any target character χ:H_Q→A, applying χ to (11) compares two actual operations: target Möbius/antipode inversion after expanding the proof, versus source inversion before expansion and then translation. The extra-interface defect supplies the exact signed correction. Thus an analytic macro compiler need not commute with hierarchical inclusion–exclusion, but the discrepancy is computable from the same D already required for cut compatibility.

This is an algebraic theorem, not yet a demonstrated runtime or proof-search application of the antipode. Its justified role is to make future relative-core/Möbius calculations transport correctly across the compiler. It should not be substituted for the concrete derivative/closure-analysis applications already established.

For completeness, the forest defect has the exact multiplicative rule. Put F=(f⊗f)Δ_P. Then

    D(xy)=D(x)F(y)+F(x)D(y)+D(x)D(y).

It follows by expanding (F+D)(x)(F+D)(y) and subtracting F(xy). The quadratic term represents frontiers with newly introduced nonaligned cuts in both forest components; omitting it would lose simultaneous extra-interface obligations.

### Minimal checked sign example

Let a be a primitive nullary source tree, and compile it to the two-node target tree b(c), with c nullary and b unary. The sole additional proper cut gives

    D(a)=q(c)⊗q(b(Box)).

Since c is primitive, S_Q(c)=−c, hence K(a)=−q(c)q(b(Box)). Source primitiveness and K(1)=0 reduce (11) to

    S_Q(f(a))=−q(b(c))+q(c)q(b(Box)),
    f(S_P(a))=−q(b(c)).

The correction is positive in this minimal case, although antipode corrections need not be positive in general. A character sends the discrepancy to χ(c)χ(b(Box)), giving the exact additional inclusion–exclusion term arising from the interface introduced by the macro. This sign calculation agrees directly with the target antipode recursion.

## 11. Exact classification of when a linear macro compiler can be Hopf

Under the hypotheses of §1, assume the source carrier contains the open corolla of every admitted source operation: one positive root node with typed Boxes in all premise slots. Work over ℤ with the full positive-node cut carrier.

THEOREM 6. The following are equivalent:

1. f is a coalgebra morphism (equivalently here, the unital/counital algebra compiler is a Hopf morphism).
2. D=0 on every source tree.
3. Every admitted operation macro M_b has exactly one positive target node.

Proof. (1) and (2) are the definition of D. If every macro has one positive node, every positive node of every compiled tree is a source seam. The aligned-cut bijection exhausts all target cuts, so D=0.

Conversely suppose some M_b has at least two positive nodes. Apply the compiler to b's source corolla. Its coefficient tree is primitive: the only positive-node frontiers are empty and the whole root. Its image is M_b filled with identity Boxes. Choose any nonroot positive node of that macro. The cut at that node has a positive detached factor and a positive remainder containing the macro root. It is a nonaligned proper cut, giving a nonzero term of D on the source corolla. All defect coefficients are nonnegative integers and the normalized positive tree tensors form a free basis, so the term cannot cancel. Hence D≠0. QED.

Thus a genuine expansion that introduces internal proof steps cannot satisfy the naïve full CK Hopf-morphism demand. The positive defect is not optional bookkeeping: it is exactly the structure such an expansion needs. The only morphism case is a one-node reinterpretation of each admitted rule, possibly with the declared slot permutation and boundary translation.

This classification is for the full open-tree carrier. It does not automatically hold after restricting to closed proofs without source corollas, filtering to native material-eligible cuts, or quotienting by proof equations that identify tensor basis elements. Those are additional problems. In particular, a material observer could hide an extra logical cut without turning the full compiler into a Hopf morphism.

### Well-foundedness of the antipode correction

Every cut contributing to D(t) is proper: the empty and whole-root cuts are always aligned. Therefore its pruning forest has strictly fewer positive target nodes than τ(t), since the remainder retains at least the target root. The target antipodes used inside K(t)=μ(S_Q⊗id)D(t) are consequently applied only to strictly smaller newly exposed forests.

Formula (11) is thus compatible with a well-founded incremental inversion procedure: reuse the transported source inversion and supply target inversions on the smaller extra-interface factors. It is not a circular request for S_Q(τ(t)) itself. Repeated factors may be memoized. This gives a concrete recursion/verification strategy, while any asymptotic speedup over ordinary target antipode computation remains a separate empirical or complexity claim.
