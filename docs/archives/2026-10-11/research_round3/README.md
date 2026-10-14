# Typed CK residuals and normalization contracts — evidence

Read `CK_Typed_Residuals_and_Normalization_Contracts.html` first.

## Reproduce

Requires Python 3.10 or later, standard library only. From the extracted root:

    python run_round3_checks.py

The runner executes all seven independent/combined checks, failing on the first
nonzero exit. JSON result files are refreshed. The final integration test can
take longer than the small carrier tests. No Lean, Racket, network, or external
package installation is required. This is not a native POTKIN3 build.

## Proof map

* `carrier_audit.md`: typed P-tree bialgebra, connected coefficient Hopf quotient,
  lawful typed coaction, material projection, and failed-convention examples.
* `typed_coaction_inverse.md`: actual inverse cut relation, finite residual,
  complete-source guard, and reversed weakest-precondition staging law.
* `typed_d4.md`: designated-hole contracts, regular joint providers and all-CK-
  frontier analyzer. Distinguishes this relation from the coaction inverse.
* `natural_application.md`: independent normal-form material-demand theorem,
  finite exact registry, structural elaboration and application boundaries.
* `contract_transfer.md` and `sell_contract_bridge.md`: two-calculus transport,
  provider coverage and observer hypotheses, natural SELL material instance.
* `novelty_value.md` and `final_review.md`: continuity/novelty audit and final
  independent review. Later review addenda supersede provisional qualifications.

## Evidence distinction

Theorems are paper proofs. Bounded enumeration and deterministic random cases
test implementations. Finite observer saturation represents unbounded provider
sizes; it is not an enumeration of all proofs. No test count is substituted for
an inductive proof or a novelty claim.

The normalization observation counts designated material constructors in the
normal form. It is not runtime, reduction steps, peak space or process safety.
The full ambitious D4 analytic-calculus synthesis and native registry integration
remain open. The combined direct coaction/normalization integration did pass;
SELL repair invariance of that observation remains unproved.

`research_round2/check_sell.py` is the unchanged earlier logical checker used by
the new typed material-cut test, included for self-contained reproduction.
