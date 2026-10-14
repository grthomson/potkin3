# Final independent adversarial review

Reviewed 11 October 2026: `typed_coaction_inverse.md`, `carrier_audit.md`, `typed_coaction_inverse.py`, `natural_application.md`; also inspected the fixed-hole theorem, natural instantiation and contract-transfer note. This is a paper/code review, not Lean verification or a literature novelty certification.

## Verdicts

**PASS — typed carrier and inverse geometry.** The residue-sensitive bialgebra, quotient of standalone residue factors, and quotient-left coaction are compatible. Internal empty ports remain typed. In the free ordered exact-port carrier, a fixed source/remainder pair determines the retained address embedding and therefore its unique positive provider tuple. The inverse recurrence correctly treats a residual edge as either unchanged or replaced by one positive pure provider, including open providers. It introduces neither independent external forest gaps nor artificial cuts of already-empty leaves.

**PASS — finite recognizability, under the stated finite/local registry hypotheses.** Simultaneous source/provider observation saturation prevents spurious cross-pairings. The powerset recurrence is exact for all finite trees over the registry, not merely the enumerated sources. Counterexample witnesses are real typed assemblies. This depends on positive combinatorial support, not arbitrary signed linear combinations or cancellation in a finite-characteristic coefficient field.

**PASS — natural demand theorem in its restricted syntax.** Because the signature has no projection, inspection, higher-order application or recursive rewriting, each variable value contributes only through its total material count. The let induction gives the stated affine demand formula. Duplication and erasure are genuine. Full normal-form count is not an evaluation-cost bound.

**PASS — budget zero.** For B=0 the capped semiring is {0,1}, with OR as addition and AND as multiplication. One is simultaneously the multiplicative identity and overflow marker. There is no failure of the semiring quotient; zero times overflow is zero. Do not describe overflow as an absorbing element for multiplication.

**CONDITIONAL — natural instance versus the actual lambda inverse compiler.** The executed natural instance uses complete providers filling designated holes (`test_typed_natural.py`). The separately executed actual-coaction inverse instance uses g-depth and completeness (`typed_coaction_inverse.py`). Both pass, but they are different implementations. Do not report an executed combined lambda/demand checker. A paper-level bridge is straightforward: extend the finite demand observer to edge-bearing syntax using declared edge constants and a completeness bit, and accept incomplete sources automatically so the universal requirement concerns complete assembled proofs. For a complete source all residual leaves must then receive complete positive providers, recovering the fixed-hole contract. Observer values on incomplete sources are auxiliary; they are not asserted to equal normal-form semantics of an unfilled proof.

**CONDITIONAL — module weakest-precondition staging.** Let A*B be convolution defined by positive support of the coefficient coproduct, and let A act on remainder assertions by inverse coaction assembly. Coassociativity gives `(A*B) act X = A act (B act X)`. Hence `WP_(A*B)(C) = WP_B(WP_A(C))`, or equivalently `(A*B) backslash C = B backslash (A backslash C)`. The order reverses on taking right adjoints. This is a lawful module residual, not an internal residuated product on one proof carrier. Fixed-hole substitution staging is separately valid, but is not by itself a proof of this coaction-level identity.

**FAIL if asserted — unrestricted generalization.** No theorem here establishes full SELL normalization, new general Cut elimination, finite exact recognition of unrestricted native judgments, a natural-observer-preserving SELL repair compiler, or a Hopf quotient of the finite observer. The notes mostly disclaim these correctly.

## Executable checks rerun

- `check_carrier.py`: 381 forests, 1,524 coefficient-sensitive identities; half-erasure counterexample reproduced.
- `typed_coaction_inverse.py`: 150 sources, 404 coaction terms, 1,484 reconstructed inverse witnesses; open coefficients and typed edge endpoints retained.
- `check_natural_demand.py`: 1,000 normalization comparisons, 6,000 capped comparisons, 3,000 staged antichain checks, 48 joint contracts.
- `test_typed_natural.py`: 831 native-typed terms, 12,696 literal cuts, nonvacuous universal contract and actual bad-normal-form witness.
- Additional direct capped arithmetic comparisons for budgets 0 through 5, inputs 0 through 29, passed.

## Assessment of value

The mathematically defensible package is a typed CK coaction with an exact finite inverse-contract compiler, plus a normalization-aware fixed-hole/frontier application and an explicit path connecting their domains. The application is small but is a real proof property rather than label support or tree height. Its novelty remains the specific bridge and disciplined interface treatment; automata residuals, semiring demands and the quotient-comodule construction are established mechanisms. D4 with restricted D2 support and D5 contracts is a reasonable next target. D1 repair remains a separate comparison problem until observer preservation is proved.

## Follow-up integration review

The root subsequently supplied `test_coaction_normalization.py`, directly integrating the actual coaction with the natural demand observer. **Code inspection and executed integration now PASS**, superseding the earlier implementation-gap condition above. The imported coproduct and generation caches are cleared after replacing the registry; purity and sorting consult that new registry dynamically. The old example's observer and provider-state globals are not used. The integration independently saturates positive providers, including open ones, and propagates completeness conjunctively through every child, including providers which normalization will erase. Thus its implication guard correctly restricts the claim to complete assembled syntax. All registry constructors are selected in this instance, so the construction tests the full typed lambda coaction, a legitimate material profile. It does not test the separately restricted SELL material profile.

The initial duplicate runs were stopped because full coproduct enumeration on each synthesized large witness was unnecessarily exponential. The replacement `exact_frontier` matcher was independently inspected: it checks exact sorts, retained rules and arities; unchanged residual edges produce no factor; filled edges produce the whole positive source subtree; child traversal preserves order; comparison to the entire coefficient tuple and explicit purity checks complete validation. This validates an actual cut, not just a target observer state. Full coproduct enumeration remains on bounded forward sources and the final explicit counterexample. The completed result file reports **1,034 source trees, 5,609 forward coproduct terms, 95,961 inverse witness checks, and 39,370 complete-witness normalizations**. The nonvacuous contract and actual normalized cost-three violating assembly pass.

The SELL macro/material test was independently rerun successfully: **16 logical cases and 232 typed residual/refilling checks**, with exact selected-material record equality and different unrestricted cut counts in every case. Its material profile includes binary tensor introduction, so the check is not confined to primitive coefficient leaves. It does not establish normalization-observer compatibility of SELL repair.
