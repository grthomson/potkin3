# Mixed material records and verification client

Read the focused `CK_MIXED_MATERIAL_RECORDS_AND_VERIFIED_MODULE_CLIENT_2026-10-10.md`, then `mixed_theory.md` for proofs. `verification_consequence.md` states the finite-history guarantee; `adversarial_review.md` and `novelty.md` record independent challenges and antecedents.

Preserve all three sibling directories when extracting this package. Run:

```sh
python3 mixed_2026_10_10/run_validation.py
```

Use Python 3.10 or later with the standard library; do not disable assertions with `-O`. The runner refreshes results and records stdout/stderr. The older directories are included dependencies and proof context, not newly claimed results. No external repository is modified.

The mixed checker verifies explicitly specified equations and actual CK flags. It is not a complete logical equality decision engine. The portable verifier integrates the prior implicational signature implementation; its cut enumeration is independent of the producer, while the signature code is shared. See `verification_client/practical.md` for exact trust and admission limits.

Paper proofs cover the mixed structural theorem. Tests are finite corroboration, not mechanization. The next missing implementation is the complete rigid-signature mixed equality module, followed by operational/native integration.
