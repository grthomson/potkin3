# Independent completion audit

## Concrete canonical image

The independent `island_seal.py` implements the proposed maximal-material-island construction. It hides each maximal pure selected-material cone, including a hole-only cone, behind a fresh opaque atomic symbol; fully beta-eta normalizes the remaining typed occurrence-linear shell; and restores each symbol as the logical identity seal `(lambda x.x)m` around its unchanged material payload m.

All 4,228 generated typed terms passed: 16,916 iterated material residual states and 60,042 actual antichain terms. Checks cover idempotence, preservation of ordinary beta-eta proof identity, exact material forest coefficients with normalized right residuals, and hereditary stability of the normal image. Four actual shadow-I/E source naturalizations also pass, including the old hypothetical atomic discharge fixture. The concrete dependent Cut-Cut, lambda-passenger, general primitive-passenger and eta/App-push gates now have equal canonical images. Unsafe material fusion remains distinguished. These are finite executable checks, not a mechanized theorem.

The crucial proof invariant is that the opaque shell contains no positive pure selected-material cone: every atomic subterm has a Ref, a logical vertex, an opaque symbol, or another nonselected blocker. Full shell beta/eta cannot eliminate the final blocker without transporting an opaque symbol or another blocker. Opaque symbols must count as nonmaterial for this argument. Their restoration supplies actual logical seals. Material cuts occur entirely within unchanged payloads; a whole-payload cut replaces its opaque label by the corresponding hole label, which is restored as a sealed hole. Thus hole-only seals are essential to exact hereditary equality.

## Failure of naive rewrite completion

Adding inward Cut propagation through logical application to the old guarded normalizer is not confluent. For free F:p→q and pure delta:p,

`(lambda x:p.F x)delta`

eta-reduces to `F delta`, whereas inward App propagation yields `F((lambda x:p.x)delta)`. Both are normal under the proposed naive rules. The island construction resolves this peak by choosing a separate canonical image instead of assuming that the local rewrite extension converges.

## Exact contextual and substitution boundary

The canonical image is not automatically a representative of the same declared contextual sequent-equivalence class. A pure m maps to Seal(m). An unrestricted contextual equation `m=Seal(m)` is materially unsound: under a selected material envelope r, the term r(m) has a composite material cone and r(Seal(m)) does not. Accordingly N is not a congruence for all ordinary context fillings.

Refining to `Nhat(t)=t` for pure t (holes included) and `Nhat(t)=N(t)` otherwise fixes the most immediate pure-versus-impure context distinction, but it does NOT give an open-term substitution congruence. Let y:p be a free indexed input and r:p⇒q selected:

\[
 t=(\lambda x:p.r(x))y,\qquad u=r(y).
\]

Both terms are impure and have the same Nhat image r(y). Substitution y:=delta for a pure material proof gives

\[
 \widehat N(t[\delta/y])=r(\operatorname{Seal}(\delta)),\qquad
 \widehat N(u[\delta/y])=r(\delta).
\]

The latter is pure and the former impure, and their actual CK inventories differ by the composite r(delta) coefficient. Thus replacing equal closed implementations in a fixed external context must be distinguished from substituting arbitrary implementations into the free resource inputs of equal open terms. The latter is required for an unqualified operadic/Faà di Bruno congruence and remains unproved by the purity flag alone.

## Candidate finite open-resource refinement

A potentially substantive next construction records Nhat after every subset of atomic free inputs has been replaced by fresh formal pure material constants delta_y. Other free inputs remain Ref vertices; compound inputs cannot be pure in this presentation. For n atomic inputs this gives at most 2^n symbolic material-mode observations. The example above is separated by the mode in which y is pure.

This is a candidate, not a theorem. Its intended proof obligation is exact: equality of symbolic composite material coefficients must remain equality under arbitrary pure payload substitutions, including all internal cuts and newly spanning composites; impure payload substitution must preserve the shell comparison. The former is precisely where the actual typed CK/Faà di Bruno substitution law and jointly admitted complete resource witnesses must enter. A mere count of active modes or material vertices would not suffice. Formal constants require permitted free atomic base extension and must not be silently asserted to be inhabited in the original base.

## Executed mode refinement and proof obligations

`material_modes.py` implements the full finite symbolic signature. `material_modes_validation.py` generated 2,183 linear typed terms, retained 274 beta/eta pairs with equal mode signatures, and rejected 360 unequal pairs. It then checked 1,340 substitutions (including 656 open fillers and 450 compound-input substitutions), 274 logical application contexts, 126 material contexts, 70 hypothetical-discharge contexts, and 328 lambda-binder contexts. Every retained equality survived these probes. The script also tests source coaction terms directly after substitution and a bounded collection of two-stage actual extraction flags. Consult its JSON for final counters.

The promising sufficiency argument is by final filling, not by silently commuting Nhat with all substitutions. Fix a final legal simultaneous substitution sigma. Classify each atomic input x by whether sigma(x) is pure. The matching symbolic mode substitutes formal pure markers exactly at those x. A maximal pure island in this mode is an explicit indexed material tree template in those markers. Replacing the markers by their actual pure trees gives the actual maximal pure island after sigma, preserving its ownership and complete interfaces. At the other inputs, impure fillers remain blockers at the original source level; their own islands and logical shells can be inserted separately. Equality of the normalized token shells is stable under this typed linear shell substitution by ordinary beta/eta congruence. Restoring the expanded islands then gives equal Nhat images. To prove stability under subsequent open substitutions, classify the final composed fillers by the same argument; do not assume that an initially impure open filler remains impure after its own inputs are filled.

For the actual CK/Faà di Bruno claim, equality of templates is not merely equality of primitive inventories. Every formal leaf expansion introduces its internal cut structure and may allow composite cones spanning the template and the supplied payload. These are precisely actual tree cuts of the expanded typed material templates. Since equal templates and equal routed payloads expand to the same indexed trees, their entire cut families, coefficient multiplicities and nested extraction flags agree. A formal theorem should state the concrete expansion bijection and the jointly admitted complete judgments, not only a truth-valued support condition.

Necessity/operational maximality needs an extra admissibility qualification. Formal selected-material markers are not automatically available selected old-base rules. If the observation universe permits enlarging the selected material profile by fresh nullary generators, each symbolic mode is directly realizable. If it keeps the old selected base fixed, a pure mode might be uninhabited. In that case the all-modes signature remains a sufficient conservative refinement, but it can over-separate operationally; exactness must restrict to jointly admitted pure modes or prove that the required extensions are permitted. This is a genuine typed resource-witness condition.

## Sparse-core review correction

In the BES sparse-core theorem, injectivity of the set-valued polynomial encoding alone does not establish equality of the kernels of the linearized maps. The additional triangular argument does: in a finite linear relation among distinct canonical images, choose the greatest maximal detached-material degree. Each image at that degree has its unique all-maximal-islands cut, and this leading coefficient plus the fully normalized named-hole residual reconstructs the image. These leading monomials are distinct; lower-degree images cannot contribute. Their coefficients vanish, and descending induction finishes. This repair was communicated to the proof author.

## Independent audit of the new-hole/refill boundary

Free-input modes do not explicitly vary inherited CK holes. Nevertheless this boundary admits an additional argument, rather than a counterexample: **Nhat equality is stable under legal refill of existing actual closed holes.** In the pure case Nhat equality is literal equality of the indexed material trees. In the impure case it recovers the same maximal indexed material islands (including named holes), and the same normalized opaque shell. Refilling a hole cannot delete a positive logical or Ref vertex already outside those islands. Hence it cannot fuse across an old island boundary. It can expand a pure island or split it into several islands separated by an impure filler. The identical retained material template splits identically on both sides. Substitute the newly abstracted shell of that expanded/split island for its old opaque token; ordinary typed beta/eta congruence identifies the two outer shells. Their restored canonical images agree, and the original positive blocker keeps both whole terms impure.

For Sigma, apply this argument at each original free-input mode. Legal closed hole fillings commute with those free substitutions. Thus no separate exponential list of hole modes is needed merely for existing certified holes.

For the subcomodule/hereditary claim, fix an actual batch I. Each detached pure component is closed and contains no free Ref input. It therefore remains the same admissible component after every free-mode substitution. Equality of Nhat in that mode, followed by its exact material coaction identity, permits coefficient separation at the indexed detached forest. The material occurrence identities determine I, avoiding ambiguous unlabelled coefficient collisions. It follows that the corresponding right residuals have equal Nhat images in every mode, hence equal Sigma signatures. The new named holes introduced by I are now covered by the preceding refill lemma. Iteration follows by the genuine CK coaction/extraction-flag law. This argument explicitly addresses new holes; it does not infer refill stability from free-variable tests alone.

`hole_refill_challenge.py` independently probes all actual antichain batches of generated mode-equal beta/eta pairs and of nontrivial equal canonical-image pairs. It exercises joint pure-versus-identity-detour fillings, including holes inside nonprimitive islands whose impure refill splits the old island, and open/composite individual fillers. Closed joint fillings retain the actual empty-context slot judgment; open fillers are additional parametric stress tests that change the ambient context and are not silently treated as licensed certified fillers. Final counters are in `hole_refill_challenge_results.json`.

Re-review of BES `bridge_completion.md` confirms the sparse-core proof now includes the required triangular linear-independence repair. Its no-material-shell, exact-cut correspondence, and declared Cut-Cut/logical-passenger comparison remain sound in the stated indexed linear domain. The full historical class-sum subalgebra comparison and unrestricted principal-beta quotient are not consequences of these arguments.

## Final namespace and representation hardening

Formal pure-mode probes now use dedicated tagged UID and primitive-symbol classes, disjoint from the validated ordinary string UID namespace. The tag retains the indexed free-port label, so independent signature computations align without renaming any ordinary material occurrence. A source containing the formerly colliding ordinary UID `__formal_y` and rule name `formal_pure_y` is explicitly tested and retained unchanged.

The implementation's opaque island token is a fresh closed atomic `hole` node, whereas the proof can use a fresh nonmaterial Ref parameter in an extended context. This is an operational encoding difference, not a claim that a genuine material hole is positive/nonmaterial. Full beta/eta sees either encoding as an inert atomic parameter: it cannot occupy function position, be an eta-bound variable, or be captured by a fresh binder. Linearity retains every token once; restoration replaces all of them. The implementation performs no purity or CK coaction test on the temporary opaque shell. Thus the proof's no-material-shell lemma applies through the equivalent nonmaterial-parameter presentation, not by interpreting the temporary `hole` tag literally as a CK vertex.

The final `finite_modes_theorem.md` states the span of same-Sigma basis differences and the greatest basis equivalence, explicitly excluding arbitrary signed linear kernels. This incorporates the full-signature linearization caution; it does not identify the carrier with a direct sum of marginal mode kernels.
