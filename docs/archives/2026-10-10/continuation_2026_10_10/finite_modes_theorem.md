# A finite material-mode criterion for uniform substitution and CK compatibility

Date: 2026-10-10. Native theorem and proof; independently reviewed finite implementations are corroborating evidence, not proof-assistant mechanization.

## 1. Domain, observers and quantifiers

Retain exactly the occurrence-linear implicational native calculus, selected primitive material profile, complete indexed judgments, actual material-origin holes and commutative-forest CK coaction of `bridge_completion.md`. In particular, primitive applications may have positive arity and atomic hypothetical discharge; their resources are routed linearly. Material-origin holes have closed atomic interfaces. All substitutions below are capture-free, type-correct and jointly resource-disjoint, preserving each intrinsic discharge token. Material and hole occurrence identities are rigid; logical administrative names are compared up to coherent alpha.

Write N for the sparse island normalizer proved there, and let pure(t) mean that t is a selected-material tree or zero-positive-vertex material-origin hole. Define the purity-refined representative

    Q(t) = t,       if pure(t),
           N(t),    otherwise.

Its two output cases are disjoint: the first is pure, the second contains a nonmaterial positive vertex. Thus equality of Q is equivalently equality of N together with equality of root purity. Q preserves complete judgments and ordinary beta/eta normal identity, is idempotent, and is exactly hereditary under actual material opening. A pure term remains pure on opening; an impure term retains its nonmaterial vertex because material cuts cannot remove it. Consequently rho Q=(id tensor Q)rho.

The refinement is essential: N identifies m and Id(m), but the selected primitive context r[-] distinguishes them. Conversely Q still identifies Ref x and Id(Ref x), so Q alone is not stable under arbitrary implementation of a free input.

Let the complete free-assumption context of t be x_1:A_1,...,x_n:A_n. Put I_at={i | A_i is atomic}. Reserve one globally fresh, distinctly marked selected nullary material constant alpha_i:A_i for each i in I_at. These are formal probe rules with fresh occurrence identities. Material-profile extension adds such new symbols while preserving the selected/unselected status of every existing symbol. For S a subset of I_at, define

    t_S = t[alpha_i/x_i : i in S],
    Sigma(t) = ( Q(t_S) : S subseteq I_at ).                 (1)

The coordinates have their actual remaining complete judgments, so equality compares matching S and matching free/closed interface data. Unselected inputs remain Ref occurrences. Compound inputs have no pure mode: atomic primitive outputs and the permitted holes cannot have compound conclusion.

The profile has at most 2^|I_at| entries. The complete tuple is one canonical basis label for the equality carrier. We do not identify this quotient with the kernel of a map to a direct sum of coordinatewise vector spaces: different tuples can have linear rectangle dependencies there. This is a finite **formal material-extension** theorem: the probe rules must be admissible in the extension universe under discussion. Adding alpha:p can create a previously underivable p, so it must not be called a conservative logical extension. For a fixed base that forbids such extensions, (1) is a sufficient uniform criterion, but completeness or maximality requires restricting to jointly realizable pure modes and supplying witnesses. The unrestricted theorem below quantifies over the stated formal extension universe; it is also valid in an actual future-base semantics whose extensions admit these probes.

## 2. The exact expansion lemma

Fix arbitrary typed fillers P_i for some or all free inputs, with the required joint resource disjointness. Classify the final fillers by their actual root material purity. Let S consist of the atomic inputs with pure filler. For every remaining input its filler is impure, including every compound-typed filler. Inputs left unfilled are treated as Ref fillers and therefore impure.

Starting from t_S, its maximal pure islands are material templates containing the alpha_i at their indexed positions. Replace each alpha_i literally by its pure filler P_i. This preserves the surrounding island's purity and inserts the entire actual primitive tree, including all its internal ports. It may enlarge its coefficient degree; no coefficient is replaced merely by a primitive count.

Every remaining free Ref is outside every pure island. Replacing such a Ref by an impure filler cannot create a pure cone spanning the substitution seam. The filler can contribute its own maximal material islands, but a positive nonmaterial vertex separates all of them from the host's surrounding material ancestors. Thus the maximal material decomposition of the fully substituted term is obtained by (a) expanding the pure templates and (b) adding the maximal islands from the impure fillers.

On the opaque shell, step (b) is exactly ordinary capture-free linear substitution of the fillers' opaque shells. Ordinary beta/eta equality is stable under this substitution. The same token/interface matching, expanded material templates and normalized composite shell therefore reconstruct the same Q value whenever the starting Q(t_S) values agree. In the pure starting case the starting trees are literally equal, so expansion is immediate; a remaining free Ref cannot occur in that pure case. In the impure case, substituting impure fillers and expanding pure constants cannot remove every nonmaterial positive vertex, so the result stays in Q's impure branch.

**Expansion lemma.** If Q(t_S)=Q(u_S) for the purity mode determined by a particular jointly typed substitution sigma, then Q(t sigma)=Q(u sigma).

This is a structural statement about native trees and shells. It does **not** assert that alpha_i maps to P_i by a CK Hopf algebra morphism. A nullary probe is primitive, while a nonprimitive P_i has a reduced coproduct. Section 7 gives the necessary actual-cut expansion.

## 3. Finite completeness for all free-input implementations

For same-interface native terms t,u,

    Sigma(t)=Sigma(u)
      iff Q(t sigma)=Q(u sigma)
          for every jointly typed linear substitution sigma
          in the declared formal/future material-extension universe.       (2)

The forward implication is the expansion lemma, choosing the actual purity mode of each sigma. The reverse implication uses exactly the finitely many probe substitutions from (1), leaving unselected inputs as Ref terms.

Hence profile equality is stable under further typed substitution. To compare the profiles of t sigma and u sigma, take any probe mode tau of their remaining free resources. The composed fillers sigma;tau have definite final purity. Apply the forward implication of (2) to that composed substitution. This gives equality in every output coordinate, independently of whether a filler changed purity under tau.

This last step is why checking only the original input purity would be insufficient: a Ref-bearing filler may become pure after its own inputs are implemented. The finite criterion reclassifies the final composed fillers rather than assuming the first classification persists.

For example Ref x and Id(Ref x) agree in the empty mode but disagree in the pure alpha mode: Q(alpha)=alpha, whereas Q(Id(alpha))=Seal(alpha). Similarly `(lambda x.r(x))y` and `r(y)` are separated by the pure-y coordinate even though their original N and Q values agree.

## 4. Ordinary contexts and actual-hole filling

Q equality is stable under inserting equal complete terms into an ordinary well-typed one-hole syntax context. If both terms are pure, Q equality says their raw indexed trees are equal. If both are impure, neither can create a pure cone spanning its insertion seam; context islands and argument islands therefore combine as in the expansion lemma, and ordinary normalized-shell equality is a congruence. A context may bind an indicated free assumption, but must respect its exact identity and typing. Iterating gives the multi-hole case.

Together with (2), this implies contextual stability of Sigma: apply any final mode to the complete context, use (2) for the resulting partially implemented arguments, and then Q context congruence.

There is also a distinct filling operation at a named material-origin hole, which is not merely free-variable substitution. Suppose Q(t)=Q(u) and matching named origin holes are filled by the same jointly typed implementations. If t,u are pure then their raw trees agree. Otherwise they have identical indexed maximal material templates and the same normalized opaque shell. A hole inside a common pure template may receive a pure filler, enlarging that template, or an impure filler, **splitting** the template into smaller maximal pure islands. The split is determined by the same template, same hole positions and same supplied filler on both sides. All pre-existing outer nonmaterial blockers remain. The resulting outer opaque shell is obtained by substituting identical refined template shells into equal normalized shells; ordinary beta/eta congruence therefore gives equal Q values. Holes already outside a nonempty island are treated by the same zero-vertex template case.

This proves simultaneous actual-hole refill stability, including holes introduced by a preceding CK cut. It does not pretend that filling a hole cannot change material regions: impure filling can split them, and pure filling can make a larger material region. The same changes occur on both equivalent templates.

For Sigma equality, first choose the final free-input substitution/mode, use (2), then apply this hole-filling lemma. Where a supplied implementation itself has free resources, all final substitutions are taken jointly and with fresh, disjoint occurrence identities. Strict complete-judgment slots admit only the appropriate closed implementations; open-resource stress tests are a separately declared extension of the operation, not silently the same slot.

## 5. Actual CK subcomodule closure

Let t and u have equal Sigma profiles. Their empty-mode Q images agree, so their original maximal pure islands agree as indexed trees; if they are both pure this is literal equality. Every original actual admissible antichain I therefore has a corresponding antichain J with exactly the same detached forest, full interfaces and occurrence support.

Fix any pure-input mode S. The original forest remains a legitimate material cut after inserting the fresh probes: its components are closed and contain none of the free input occurrences. Moreover its rigid forest coefficient cannot be confused with a newly created seam-spanning cone, since every such new cone contains at least one fresh probe occurrence. Fresh probe IDs are absent from the original coefficient. With indexed roots and exact complete holes, coefficient separation therefore picks the corresponding original cut, not a new cut with the same coarse rule inventory.

From Q(t_S)=Q(u_S), use Q's termwise hereditary opening at those same original material supports. It gives

    Q((t_S)/I)=Q((u_S)/J).

Opening a closed original forest commutes with substitution into the remaining free Ref inputs, so this is

    Q((t/I)_S)=Q((u/J)_S).

It holds for every S. Thus Sigma(t/I)=Sigma(u/J), including their new named-hole signatures. Equality under subsequent filling of those new holes is supplied by Section 4.

Therefore the span of same-Sigma basis differences is a material subcomodule, and the actual CK coaction descends to the basis equivalence carrier defined by Sigma. The quotient coefficients remain the full original material Hopf algebra. Coassociativity transports the result to every supported extraction flag and ensures agreement of simultaneous and staged remainder formation. This proof uses rigid coefficient separation and actual cuts; ordinary logical normalization or root-purity truth alone does not yield it.

## 6. Universal comparison, with its precise scope

There are two levels of the maximality statement.

First, (2) says unconditionally that Sigma equality is exactly the substitution-universal refinement of the concrete observer Q in the declared extension universe. No semantic full-abstraction premise is needed for that claim.

Second, consider a basis equivalence E on these native terms which:

1. preserves complete judgments, named seams and ordinary beta/eta normal identity;
2. has a descended actual material coaction with the original indexed Hopf coefficients and nonzero distinct residual basis classes;
3. is stable under ordinary typed contexts, jointly typed substitutions, and the stated admissible future material extensions.

Then E is contained in Sigma equality. Indeed material-comodule stability together with ordinary nf equality forces equality of the old cofree profile Phi; the sparse reconstruction theorem in `bridge_completion.md` forces equality of N. A remaining purity mismatch is separated by a fresh selected unary material context r[-] admitted in the extension universe. If t is pure and u impure with N(t)=N(u), r(t) has the whole composite coefficient r(t), while r(u) has no pure cone containing the outer r. Its coaction coefficient against the complete endpoint hole is nonzero and cannot be supplied by a different indexed occurrence. Thus E cannot identify that pair. Hence E implies Q equality. Applying substitution and extension stability to every formal probe mode yields Sigma equality.

Conversely Sections 3–5 show that Sigma equality has the listed contextual, substitution and actual-material-comodule stability, and it preserves ordinary normal identity. Hole refill stability is included by Section 4. Thus Sigma is the greatest **basis equivalence** satisfying those requirements in the specified extension universe.

This is not a claim about arbitrary linear subspaces whose tensor coefficients can cancel, nor about quotient Hopf maps that deliberately kill composite material trees, nor about fixed-base semantics excluding the separating probes/contexts. The nonzero endpoint and original-coefficient hypotheses are essential. The result is also not equality with the classical MLL+Mix fixed-net class-sum subalgebra: the native intuitionistic carrier and that collective representation still require their separate comparison map.

## 7. The actual cut-expansion law: why Faà di Bruno data matter

Let T be a pure indexed material template with distinguished fresh nullary probe occurrences alpha_i, and replace each alpha_i by a pure material tree P_i at the exact matching interface. The following is a bijection onto the actual admissible CK antichains of the expanded tree T[P_i].

Choose an antichain A of **old nonprobe vertices** of T. For each probe lying below a chosen vertex v in A, the entire P_i is swallowed by that outer cut: no internal cut in P_i may be chosen. For each probe not lying below any vertex in A, independently choose an arbitrary admissible antichain B_i in P_i, including the empty antichain and its whole-root cut when applicable. The resulting expanded cut consists of the old vertices A together with these uncovered inner vertices B_i.

To invert the construction, partition an expanded cut into old nonprobe vertices and vertices belonging to inserted P_i. The old part is A. Admissibility excludes every inner choice under a selected old ancestor. All remaining inner choices are exactly the B_i. This is unique, retains exact ports and occurrence marks, and handles the whole-expanded-root case.

The detached forest is the product of the expanded outer subtrees `T_v[P_i]` for v in A and the detached inner forests from the uncovered B_i. Its remainder is obtained by opening the old selected subtrees and the uncovered inner cuts at their exact named interfaces. In particular an outer detached factor may span several supplied P_i. These spanning factors and the swallowed-inner exclusion are absent from any naive coefficient substitution alpha_i↦P_i in the old coproduct.

The construction multiplies over disjoint material islands. With an impure supplied proof, first use its actual maximal material decomposition and the splitting-template analysis of Section 4; then apply the same rule on each resulting pure component. Thus it accounts for both newly spanning material regions and independent internal extraction sectors.

This is the native typed Faà di Bruno/extraction substitution data required to lift the finite mode test to actual implementation certificates. It is not an assertion that arbitrary graft substitution is a Hopf morphism. CK coassociativity then gives the corresponding nested-cut/flag law, and the ancestral swallowed/unswallowed partition is retained at every stage. Positive-arity material coefficients do real work: replacing an atomic probe by a nonprimitive tree creates its full reduced coproduct and its possible composite outer factors, all of which the law records.

## 8. Relation to the recovered target and verification

The sparse algorithm realizes the previously abstract CK observer core. The finite modes strengthen it to a concrete criterion for uniform typed implementation, resolve the Ref-versus-pure-filler defect, and supply a basis-level maximal contextual/substitution-stable material-comodule carrier under the declared extension assumptions. All material-balanced Cut passengers and Cut-Cut reassociations whose equations remain valid under typed substitution consequently factor this carrier. A principal atomic beta equation that fuses a material region does not; the pure probe mode witnesses its failure.

Independent finite programs `material_modes.py` and related validation files check generated equalities, arbitrary pure/impure/compound substitutions, future composed modes, contexts, actual material coactions and extraction flags. Additional tests fill actual holes inside nonprimitive islands. The test counts and exact bounded scopes are recorded in their result files. These computations are regression evidence for the stated proofs; no proof assistant has checked the universal theorem, and publication priority for the concrete completion remains unresolved.
