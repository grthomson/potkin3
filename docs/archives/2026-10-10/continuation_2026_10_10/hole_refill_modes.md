# Actual material-hole refilling needs no additional purity modes

10 October 2026, continuation. Paper proof plus independent finite checks. This strengthens the current maximal-material-island normalization construction to actual closed CK holes. It is a congruence theorem for filling equality classes, not a claim that arbitrary filling is a fixed-coefficient comodule morphism.

## 1. Fixed domain

Use the current occurrence-linear atomic-material implicational syntax, exact native rule instances, and the full ordinary beta/eta normalizer of its logical shell. Primitive material applications have atomic premise/conclusion types and retain ordered input routes. Actual material-origin holes considered here have complete judgment empty⊢p, with p atomic, and keep their named ancestral seams. Hole occurrences are used once. The prior closed-island discipline ensures every maximal pure material region is closed, including a bare zero-vertex hole.

A positive logical or reference vertex is nonmaterial. A subtree is pure when every positive vertex is selected material; typed holes are pure but are not positive vertices. A filling theta assigns to each chosen hole an arbitrary **closed**, correctly typed proof of exactly its atomic conclusion, or a correctly typed fresh material-origin vacancy when studying partial/nested filling. Fillers can be material or nonmaterial, can contain arbitrary logical redexes, and can have many nonprimitive internal material islands. Their fresh positive occurrence marks and remaining seams are hygienically disjoint. The same filling with the same new provenance is used on both sides.

Let N be the previously constructed normalization that hides each maximal pure material island behind a fresh opaque atom, fully beta/eta-normalizes the shell, and restores every island inside a logical identity seal. Define Nhat(t)=t for a pure t and Nhat(t)=N(t) otherwise. Equality is coherent logical alpha equality while material vertices, hole identities and complete routes remain fixed.

The finite free-input signature Sigma compares Nhat after replacing any subset of free atomic Ref inputs with distinct formal pure material witnesses, leaving other free atomic inputs as Refs. This note does not add a purity-mode coordinate for actual material holes.

## 2. Island refinement lemma

**Lemma.** Raw filling of actual pure holes cannot create a pure island that crosses an old maximal-island boundary. The maximal islands of t[theta] are precisely the maximal islands found separately inside each old maximal island M after its expansion M[theta].

**Proof.** Every nonpure subtree of t contains a positive logical or Ref vertex. Such a vertex cannot belong to a pure hole. Filling replaces only a zero-vertex hole; it removes none of those positive blockers. Therefore every old nonpure subtree remains nonpure under raw filling. All new pure regions lie inside expansions of the old maximal pure regions, and maximality inside those expansions is maximality in the whole filled term. Conversely each such internally maximal region has no pure extension across its old boundary. This proves the exact region-by-region refinement. ∎

This statement concerns raw filling before logical normalization. Full beta/eta normalization may remove logical vertices later; the opaque-shell construction controls that separate phase.

The key asymmetry is genuine: replacing an actual pure hole can only retain or **split** an old material island. Substituting for a free Ref can remove a positive blocker and **merge** islands into a newly pure ancestor. The latter effect is why free-input modes were needed.

## 3. Recovery of the labelled shell

For an impure term t, write its island abstraction as S_t[kappa_M], with one fresh atomic opaque constant kappa_M at each maximal island M. Each constant carries the complete typed island label and occurs once. Let n denote ordinary beta/eta normalization on this shell.

The result Nhat(t) is n(S_t) with kappa_M replaced by Seal(M), where Seal(M) is a logical identity application to the exact pure M. This representation is recoverable from Nhat(t): the outer shell is beta-normal before restoration, so its only newly introduced beta redexes are the displayed seals. Material labels and seams identify the island payloads. Replacing those seals by fresh consistently labelled tokens recovers the normalized shell. Coherent alpha renaming affects only logical binders.

Accordingly Nhat(t)=Nhat(u), for impure t,u, gives the same normalized shell and the same exact labelled maximal islands, under the unique occurrence-respecting correspondence. A pure input has a pure Nhat image, whereas an impure input has an impure Nhat image; equality cannot mix the two cases. For two pure inputs, equality is simply exact equality of their retained material trees.

## 4. Hole-refill congruence theorem

**Theorem.** If Nhat(t)=Nhat(u), then for every hygienic simultaneous closed actual-hole filling theta,

Nhat(t[theta]) = Nhat(u[theta]).

No additional test for pure versus impure hole fillers is required.

**Proof.** The pure case is immediate because t=u as exact material templates. If t and u are impure, their old positive blockers persist under raw hole filling, so both filled terms remain impure before normalization.

By §3 their normalized opaque shells and exact island labels agree. Expand each common island label M by theta. Abstract its resulting maximal subislands, obtaining the same typed inner shell S_(M[theta]) and the same exact new island payloads on both sides. By §2, abstraction of the whole filled term is exactly substitution of these inner shells for the corresponding kappa_M constants in the original outer shell, with hygienic renaming of the new tokens. There are no extra cross-boundary islands to account for.

Ordinary beta/eta equality is a congruence for closed typed substitution. Hence equality of the original normalized shells implies equality after substituting these common inner shells and normalizing. Restoring the corresponding new payloads with seals gives identical Nhat images. This includes an impure filler with several material islands: its whole inner shell is substituted, not approximated by a single primitive. It also includes a pure filler or a remaining zero-vertex vacancy. ∎

The proof uses exact typed templates and ordinary beta/eta substitution, not a purported new Hopf substitution theorem. Its importance is that those exact templates are retained by the full material observer and survive the normalization construction.

## 5. The free-mode quotient is closed under actual hole filling

**Corollary.** If Sigma(t)=Sigma(u), then Sigma(t[theta])=Sigma(u[theta]) for every filling theta in §1.

Indeed theta is closed and fills only holes. Therefore it preserves the free-variable context and commutes, up to the stipulated hygiene, with every formal pure-mode substitution for free atomic Refs. Apply §4 separately to the corresponding equal Nhat row. Thus the required number of mode coordinates is determined by the free atomic inputs, not enlarged by the number of actual CK holes.

A sequence of partial fillings is handled inductively. If a filler itself contains fresh material-origin vacancies, those become the next actual holes and the theorem applies again. Simultaneous filling and sequential filling of disjoint ports have the same raw result by native substitution, and therefore the same normalized class.

## 6. Interaction with genuine nested cuts

The material-island normalization preserves the actual material coaction on its stated closed-island domain. Sigma contains the empty free-input mode, and its other rows likewise retain the actual marked material factors. A material cone has no free Ref input, so an already selected actual material factor is unaffected by formal free-input mode substitutions. Coefficient extraction therefore transports the matched original cuts to equality of the residual Sigma rows, with their full interfaces and ancestral supports.

Combined with §5, a matched actual residual may be refilled by arbitrary valid closed implementations without depending on its chosen presentation. Repeating this gives the desired hereditary cut/refill equality on supported nested states. The CK coproduct continues to distinguish whole nonprimitive providers from simultaneous cuts inside them, and coassociativity matches the two orders of those nested operations.

**Important limit.** This does not say that a fixed filling theta preserves the prefill coefficient forest, or that

rho(t[theta]) = (id tensor theta)rho(t).

That formula is generally false. For example, the pure tree s(square_p) has a whole material coefficient s(square_p). Filling square_p by the impure identity detour Id(delta_p) destroys that whole pure cone and introduces the filler’s internal material cuts. Pure filling by a nonprimitive proof instead expands material islands and can create new compatible cuts inside the expanded coefficient.

The proven statement is that **equal presentations yield equal evaluated normalized coactions after the same filling**, with the actual new cuts computed on the result. Pure expansions obey the established typed grafting/Faà di Bruno cut decomposition; impure fillings refine old islands as in §2. The old material labels and ancestral seam names must be rebased consistently to the new filler provenance. No claim preserves erased old provider identities after implementation replacement.

Thus the quotient supports well-defined native filling, but an unrestricted normalized class-sum cut/refill rectangle or Hopf algebra homomorphism of filling still requires its separate factorization argument.

## 7. Finite independent evidence

`hole_refill_modes.py` checks four independently specified pairs: a three-hole nonprimitive island under a logical application, separated material islands under a positive binary constructor, a pure-root case, and a bound logical shell. It fills all named holes jointly with five alternatives per port: a material leaf, its impure identity detour, a pure binary material proof, an impure binary proof with two separately sealed leaves, and a fresh zero-vertex vacancy.

All 280 simultaneous fillings pass Nhat equality, Sigma equality, and direct actual material-coaction comparison. There are 214 fillings with at least one impure implementation and 132 retaining a fresh nested vacancy. An independent region calculation verifies the island-refinement lemma on both presentations in all cases: 560 checks. No additional hole mode appears in the signature.

A separate agent's generated validation probes more pairs and actual cut-generated holes. Those results should be reported from that agent's own script, rather than merged into this script’s count. Finite checks corroborate the implementation; §§2–5 supply the general proof in the explicitly closed-hole domain.
