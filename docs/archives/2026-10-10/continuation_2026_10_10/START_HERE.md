# Reproduction and reading guide

Read `CK_SUBSTITUTION_STABLE_CORE_AND_FULL_IDENTITY_OBSTRUCTION_2026-10-10.md` first. The updated target register records the current conclusions and retains the earlier project history.

Extract the entire archive, preserving the sibling directories `continuation_2026_10_10` and `research_2026_10_10`. Run from the extracted root:

```sh
python3 continuation_2026_10_10/run_validation.py
```

Python 3.10 or later and its standard library suffice. The 13 checks write per-script logs and `validation_summary.json`; individual scripts also refresh their result JSON where applicable. Assertions are part of the checks: do not use Python's `-O` option. These are finite computational checks, not machine-checked proofs of the general theorems.

The baseline directory includes the earlier material bridge sources imported by the continuation. It is included for reproducibility, not as a newly established result.

## Proof map

- `bridge_completion.md`: sparse island core, purity refinement and normalization.
- `finite_modes_theorem.md`: universal finite modes, correlated basis quotient, maximality and exact extension assumptions.
- `carrier_comparison.md`: distinct sequent/ND native Hopf carriers and material comparison.
- `tensor_carrier_extension.md`: supporting tensor-only prototype, not full mixed syntax.
- `hole_refill_modes.md`, `hopf_consequence.md`: practical refill and nonprimitive lifting consequences.
- `adversarial_completion.md`, `independent_completion.md`: independent challenges and reviews.
- `novelty_completion.md`: project and published antecedents, precise candidate increment and priority limitations.

Some proof notes retain the research chronology, including superseded candidate claims. Their final addenda and the focused report control. The final consolidated report was independently reviewed by the semantics and adversarial agents. The latter recommended using a child identity detour for direct membership in the historical D_lin palette; this correction is incorporated. The executable sequent comparison's nonhypothetical restriction is explicitly recorded.

The principal remaining obligation is a full mixed tensor–implication realization of the refined carrier and one verification-client integration. Full ordinary identity with unchanged nonprimitive material coefficients has a sharp obstruction and is not an unfulfilled positive claim.
