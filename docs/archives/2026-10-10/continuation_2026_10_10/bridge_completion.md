# Sparse material-island normalization and the CK observer core

Date: 2026-10-10. Working theorem with explicit native domain; independent review and executable validation are being carried out separately. No claim of equality with the older classical MLL+Mix class-sum carrier is made.

## 1. The completion problem and the precise new claim

The previously proved N_push normalizer respects the declared primitive-Cut passenger family but fails dependent Cut-Cut reassociation (`research_2026_10_10/cut_cut_gate.md`). Merely adding inward Cut propagation through logical applications does not repair convergence: with a free F:p→q and pure material delta:p,

    (lambda x:p. F x) delta

can eta-reduce to `F delta` or propagate to `F ((lambda x:p.x) delta)`. Those are different blocked normal forms for the naive extension. This is a failure of that orientation, not a no-go theorem for the underlying material-balanced equations.

We instead give an explicit sparse normal representative N_island. It is unique, idempotent, and strictly colinear for the actual material CK coaction. It respects primitive and logical Cut passengers and dependent/independent Cut-Cut reassociation. Its equality is precisely the old cofree observer-core equality `(id tensor nf)rho`, rather than a newly asserted generic kernel theorem. Thus it computes a potentially exponential decomposition polynomial through a linear-size native representative.

The resulting equality is a specified comodule equality, **not** an unrestricted contextual or operadic congruence. The distinction is essential for the base-extension/Faa di Bruno interface.

## 2. Native domain and conventions

Use the same occurrence-linear, unit-free implicational natural-deduction terms as the preceding proofs: Ref, implication introduction and elimination, and arbitrary finite-arity old atomic primitive applications. An old primitive has atomic premise conclusions and atomic conclusion, may discharge specified indexed atomic assumptions in its individual premises, and combines the remaining contexts linearly. Nullary primitives introduce no free resources. Primitive occurrences and intrinsic discharge tokens remain indexed; logical alpha and purely administrative logical occurrence names are identified coherently.

Fix a selected material subprofile of primitive symbols. Ref and logical vertices are never selected. A nonempty pure material cone is a rooted subtree all of whose positive vertices are selected primitive applications. Every such cone is closed: Ref is unselected, nullary primitives add no passive resources, and the primitive context operation only unions and discharges premise contexts. In particular a cone cannot contain an actual intrinsic-discharge use without its nonmaterial Ref vertex.

The residual domain contains only complete terms and their iterated actual material openings. A material-origin hole has its full named atomic interface and empty free context. Arbitrary holes concealing passive inputs are excluded. A hole is allowed as a zero-positive-vertex pure residual, but it is not a new positive material coefficient. Its inherited identity and type are retained.

Use the native CK material coaction rho whose terms are actual admissible antichain cuts, including the ordinary whole-material-root endpoint when applicable. The left forest observer is commutative; the internal order and names of all premise ports and right residual holes remain exact. A detached cone coefficient retains the full primitive tree and its occurrence labels. Coefficient equality is not primitive-count equality. The material Hopf algebra H retains its CK coproduct and grafting cocycle. The arguments below apply to this established coaction and its endpoint convention, not to a new leaf-cut surrogate.

Let nf be ordinary unrestricted implication beta/eta normalization on these linear terms with fixed typed hole constants and primitive constructors. It is unique up to coherent logical alpha. This standard logical map is intentionally used only on a material-abstracted shell or as an observer; nf alone is not material-colinear on arbitrary native terms.

## 3. The algorithm

For a term t, let m_1,...,m_k be its maximal nonempty pure material cones. They are pairwise disjoint. Also include every inherited bare material-origin hole not already inside one of these cones as a zero-vertex island. Replace each island by a fresh atomic Ref token z_i of the same output type, with a distinct globally reserved identity. Call the resulting term S_t. The tokens are free in S_t; every other original context/binder is unchanged. A cone's closedness makes this replacement well typed.

Normalize the shell S_t fully by ordinary beta/eta. Each token occurs exactly once before and after normalization, by linearity. Then replace each token z_i by

    Seal(m_i) = (lambda u_i:a_i. u_i) m_i,

using fresh coherent administrative binders. Denote the result by N_island(t). Bare inherited holes are sealed by the same rule. The algorithm never normalizes inside m_i, changes a primitive occurrence, or forgets a named seam.

The abstraction tokens are implementation devices, not new object-language primitive axioms. The output is an ordinary native ND term. Its final seal is the existing nonmaterial identity payload, not a newly postulated material rule.

## 4. The no-material-shell lemma

S_t has no nonempty pure selected-material subtree: every maximal such subtree was abstracted, and every bare origin hole was abstracted as well. Every subterm therefore contains at least one nonmaterial positive vertex. This includes nullary unselected primitives as permanent blockers; they need not count as logical vertices.

This property is invariant under full linear beta/eta on S_t. In a beta step, the argument contains a nonmaterial vertex; replacing the unique Ref use by this argument cannot make a selected-only cone across the substituted boundary. Any selected-only subtree wholly inside the argument or continuation would have existed before. In an eta step, the retained function has compound type, so its root cannot be an atomic primitive or atomic hole. Thus it retains a positive logical/Ref blocker. Existing selected-only subtrees cannot appear elsewhere.

Consequently nf(S_t) still has no pure selected-material subtree. On restoring Seal(m_i), every selected ancestor outside an island remains blocked: a token has been replaced by a nonmaterial lambda/application shell. The maximal nonempty material cones of N_island(t) are exactly the original m_i, transported with their unchanged occurrence identities. Original zero-vertex inherited holes occur inside their seals.

This lemma is the reason ordinary full logical normalization is safe on the abstracted shell even though it is unsafe on the original proof.

## 5. Convergence, semantic identity and idempotence

The algorithm terminates and has a unique result. Island extraction is deterministic, token names are immaterial up to their explicit bijection, and full beta/eta normalization of the typed linear shell is confluent and terminating. Restoring indexed islands through canonical seals is deterministic up to coherent logical alpha.

The result has the same ordinary logical normal form:

    nf(N_island(t)) = nf(t).

Indeed each seal is an ordinary logical identity detour, and shell abstraction/restoration is typed substitution at closed atomic interfaces.

The map is idempotent. The maximal material islands of N_island(t) are still m_i. Abstracting them produces nf(S_t) with a logical identity wrapper around each token. Ordinary normalization removes those wrappers and returns nf(S_t). Restoring the seals therefore gives N_island(t) again.

An island representative need not be reachable from t by the earlier guarded reduction S: it can insert seals, even for a pure material input. This is an explicit canonical comparison target, not an unproved extension of the old oriented rewrite relation.

## 6. Exact material opening and CK colinearity

Every actual material cut of t occurs inside its maximal islands, because every eligible material subtree lies in a maximal pure material cone. For a cut I, opening it replaces each m_i by a pure residual m_i/I_i; if the island is wholly detached, that residual is its named hole. The maximal-island abstraction shell is therefore **exactly the same typed token shell** before and after opening. Empty residual islands are retained as named-hole islands rather than silently discarded.

By the no-material-shell lemma, the target N_island(t) has exactly the same eligible cones, now inside the same sealed islands. Thus I has a unique corresponding cut I' with the same detached coefficients, complete interfaces, occurrence labels and antichain relations, and

    N_island(t/I) = N_island(t)/I'.                         (1)

The equality uses coherent logical alpha only; all material and hole data are fixed. This also proves that N_island is well defined throughout nested residual states, not merely at the original whole host.

It follows term by term, including multiplicities and endpoints, that

    rho N_island = (id_H tensor N_island) rho.              (2)

For ordered forest tuples one must retain the corresponding transport permutation; equation (2) is stated for the declared commutative forest observer. Actual CK coassociativity then makes (1) coherent at every supported finite extraction flag. There is no replacement of composite material coefficients by their root or leaf counts.

## 7. An exact sparse realization of the old observer core

Let V be the free vector space of ordinary fully normalized open residual proofs, retaining their whole judgments and complete named-hole signatures. Define the established cofree lift

    Phi = (id_H tensor nf) rho : P -> H tensor V.

The cofree coaction is Delta_H tensor id_V. Coassociativity gives Phi colinearity; its kernel is the familiar greatest CK-stable subkernel of nf. Those abstract facts are antecedents in the September project record, not new claims here.

The new concrete statement is

    Phi(t) = Phi(u)  if and only if  N_island(t) = N_island(u).       (3)

The reverse implication follows from (2), nf N_island=nf, and hence Phi N_island=Phi.

For the forward implication, grade a detached forest by its total number of positive material vertices. Among all cut terms of rho(t), the unique maximal-degree term cuts **all maximal nonempty material islands simultaneously**. To attain the maximum, the root of every maximal island must be covered. It cannot be covered by an eligible ancestor outside that island, so that island itself must be selected. Any proper internal cut omits its root and has strictly smaller degree. Thus there is exactly one maximal-degree cut, with coefficient F_max=m_1...m_k. If there are no nonempty islands, this is the unique empty cut.

Its right coordinate in Phi(t) is nf of the whole proof with all those islands replaced by their named holes, while inherited holes remain named as before. Every such hole survives once by linearity. This is precisely the normal shell with token names replaced by their exact hole identities. The coefficient F_max supplies each island's complete indexed tree, and the hole names supply the bijection assigning it to its normalized slot. Restoring each as Seal(m_i), and sealing inherited holes, reconstructs N_island(t) uniquely. Equality of the two finite polynomials therefore gives equality of their reconstructed representatives. This argument requires full indexed forests and full named-hole signatures, not only forest degree.

Linearizing the normal map, ker N_island=ker Phi. Set-level injectivity alone would not suffice for this claim. The polynomial representatives are linearly independent by a triangular argument: in a finite linear relation, choose the greatest maximal material degree among the participating distinct normal classes. Their unique top-degree monomials are distinct, because each reconstructs its normal class as above. Lower-degree representatives cannot contribute there. Therefore every coefficient of a greatest-degree class vanishes, and descending induction proves independence. Thus the equal-normal-image carrier is canonically the concrete image of the old CK observer core. Equivalently, the seal representatives form a retract subcomodule of native proof terms under N_island. This is not just declaring a new quotient and reproving a generic kernel lemma; (3) supplies an explicit reconstruction and decision procedure for the existing observer equality.

## 8. Sparse size and the nonprimitive content

The output has linear size in the input. Island contents are retained once, shell normalization is linear and cannot duplicate a token or primitive, and one fixed-size seal is added per maximal island/inherited bare hole. Ordinary beta/eta contractions strictly reduce the shell's positive vertex count, so there are at most linearly many contractions; straightforward repeated syntax traversals give a polynomial implementation (quadratic apart from representation/canonicalization costs).

By contrast Phi(t) can have exponentially many terms. Take n independent closed material constants, each protected by a logical identity wrapper, and assemble them through a binary selected-material tree. Every material assembly ancestor contains a wrapper, so the constants are the maximal pure islands and every subset is an admissible antichain: 2^n terms. N_island gives a linear-size exact equality representative for this polynomial.

The construction does not discard nonprimitive information. If one island is a composite r(s(a,b),c), its entire coefficient survives, including all CK cuts inside s(a,b) and the resulting extraction flags. Replacing that island by another tree with the same primitive inventory can change the normal representative and its coaction. The reconstruction uses maximal **tree coefficients**, not a bag of rule symbols.

## 9. The declared permutation comparison

For each of the following well-typed, capture-free contextual equations, material cones lie entirely in exactly-once parameters, the two sides have the same maximal material islands with their complete identities, and their token shells are ordinary beta/eta-equivalent:

* nonprincipal Cut through an old primitive, routing the passive cut input through its unique active premise and preserving intrinsic discharge tokens;
* Cut through implication introduction, when the moved argument is fresh for the introduced binder;
* Cut through either implication-elimination premise, according to the unique free-variable route;
* dependent Cut-Cut reassociation `C_y(C_x(M,P),Q)=C_x(M,C_y(P,Q))`, with y absent from M;
* independent Cut-Cut exchange, with the corresponding disjoint-variable side conditions.

For example an explicit Cut wrapper contains its lambda/application vertices; moving it cannot make a selected-only cone across its boundary, and the reference use in the source active premise prevents that primitive cone from being pure before the move. Cut through a logical constructor keeps a logical blocker on both sides. The Cut-Cut equations merely rearrange these nonmaterial wrappers. Consequently abstracting the same maximal islands reduces each equation to the ordinary capture-free substitution equation on the shells. Full shell normalization identifies it, so N_island factors the explicitly generated permutation carrier.

This supplies the missing Cut-Cut comparison for that declared intuitionistic native presentation. It does not prove that every pair with the same N_island representative is generated by these permutations: the normal image also identifies safe logical normalization and identity detours. Nor does it equate this carrier with the classical unit-free MLL(+Mix,+fixed Cut) class-sum **subalgebra** in the historical record. A class-sum subalgebra and a quotient of individual ND witnesses are different constructions; their faithful comparison requires a separate theorem.

## 10. Context and substitution boundary

The image equality is not an arbitrary contextual congruence. A closed pure material m and its identity detour Id(m) have the same N_island image, Seal(m). But placing them in a selected unary primitive r gives different maximal islands:

    N_island(r(m)) = Seal(r(m)),
    N_island(r(Id(m))) = r(Seal(m)).

The former has a nonprimitive material coefficient r(m); the latter does not. Therefore unrestricted context compatibility would erase precisely the material assembly operation being tracked. Similarly a guarded-beta equation with a Ref argument need not remain safe when that free Ref is filled by a pure material proof.

Accordingly, the Faà di Bruno/base-extension composition theorem must use its actual transparency/joint-admission criterion at complete judgments. Equation (2) and its nested consequences do not manufacture an unrestricted operadic quotient. This limitation is a testable boundary, not a missing alpha convention.

Full unrestricted beta cannot be made a sound normalization of the original unchanged material coaction: r(Id(delta)) beta-reduces to r(delta) and creates the genuine composite material cone. Any stronger no-go involving a quotient Hopf map must state what material coefficients that map kills; it is not needed for the sparse realization theorem.

## 11. Verification status

The mathematical proof above is scoped to the stated linear implicational native calculus, selected primitive subprofile, exact occurrence interfaces and commutative forest observer. Independent implementation `island_seal.py` has checked 4,228 generated terms, 16,916 residual states and 60,042 actual cut terms, including idempotence, ordinary logical identity, exact CK colinearity and hereditary image. Four source-shadow naturalisation fixtures and the Cut-Cut/lambda/App/primitive gates pass; unsafe atomic material fusion remains distinguished. Independent paper review has checked the shell, residual and reconstruction arguments. The executable represents opaque shell tokens by globally fresh atomic hole constants rather than positive free Ref vertices. For the unrestricted shell beta/eta computation these representations agree: the fresh tokens are never a bound eta reference or a compound function head and each is substituted back exactly once. The paper no-material-shell invariant uses the positive Ref representation; the code does not claim that its zero-vertex token placeholders themselves satisfy that literal invariant. Finite tests corroborate the theorem but do not replace its convergence, reconstruction or carrier arguments. The standalone normal form is an algorithm, not proof-assistant mechanization.

## 12. Subsequent uniform completion and sharp no-go

`finite_modes_theorem.md` strengthens the sparse observer by retaining root purity and checking every pure/impure mode of the atomic free inputs. It proves finite completeness for all jointly typed substitutions, actual-hole refill stability, an actual material subcomodule theorem, and a greatest-basis-equivalence comparison under its explicit future-extension and nonzero-coefficient assumptions. The all-mode signature, not N alone, supplies the uniform implementation carrier. In particular it rejects the variable-identity equation that becomes unsafe after a pure filling.

`adversarial_completion.md` §§2–3 gives the complementary sharp obstruction: if a linear observation identifies full atomic beta and its actual residuals while preserving nonzero complete endpoint images, any coefficient Hopf morphism that makes its coaction descend annihilates every realized positive-arity-root material tree. The surviving universal coefficient quotient retains only marked nullary material leaves. That loss includes the nonprimitive trees and their nested flags needed by the project. The sparse/mode refinement therefore avoids a proved incompatibility, rather than claiming to make unrestricted ordinary normalization material-exact.
