# A runnable replacement certificate with intact composite modules

This client integrates the existing occurrence-linear `material_bridge_client`
with the continuation's finite material modes and exact Faà di Bruno expansion.
It is an implicational client while the mixed-fragment theory is developed
separately. It does not claim CP operational adequacy, deadlock freedom, or a
mechanized general theorem.

Run from any working directory:

```sh
python /workspace/scratch/a856b79eb300/mixed_2026_10_10/verification_client/test_client.py
```

The repository-relative imports require sibling directories
`continuation_2026_10_10` and `research_2026_10_10`, as in the delivered archive.
`certificate.py` also generates and verifies the accepted fixture on direct
execution. Its `verify(json_object)` entry point verifies a transported JSON
certificate and returns `ACCEPT` or `REFUSE`; invalid evidence raises
`ValueError`.

## What the decision buys

Let `g:p⊸q`, `x:p`, and let `r` be a selected binary material rule with an
existing nullary material proof `d:p`. The client accepts replacement of

`g(r(x,d))`

by

`(λh. h(r(x,d))) g`.

Their entire correlated finite signatures agree. For the explicit installation
`x := s(a,b)`, both complete proofs expose **the exact intact composite
`s(a,b)` and the larger exact composite `r(s(a,b),d)`**. The JSON records each
full factor, its persistent root, the complete output and free-input interface,
and every remainder hole seam. Verification requires these contracts to agree
for an accepted replacement. A missing nonprimitive coefficient is therefore
a failed verification condition, not optional explanatory metadata.

The useful refusal compares `r(x)` with `(λz.r(z))x`. They are ordinarily
beta-equivalent. Their mode signatures differ, and the actual admitted filler
`x := s(a,b)` witnesses failure: the first proof has the intact composite
`r(s(a,b))`, whereas the second does not, because the logical application
interrupts that material cone. The smaller `s(a,b)` remains available. Thus
the refusal states precisely which assembly boundary is lost; it does not say
the second term is ill-typed or behaviorally incorrect.

## Why the full CK information is used

The certificate contains all 11 actual admissible cuts of the installed
accepted proof, with native factors and exact remainder terms. Matching the
two implementations also checks all 53 second-stage cut terms. A strict flag
extracts `a`, then extracts the punctured composite `s(hole_a,b)`. Its two
factors and remainder are checked against extracting `s(a,b)` first and
opening `a` inside that factor. This is a concrete coassociativity instance,
including a nonprimitive second-stage coefficient.

Refilling the outer vacancy first with `s(hole_a,b)` and then filling `a`
equals filling the outer vacancy once with the composed `s(a,b)`. Here the
composition is of a nested flag; it is not an invalid simultaneous antichain
containing both ancestor `s` and descendant `a`.

The client also evaluates the prior Faà di Bruno outer/inner partition for
the material template `r(probe,d)` with `probe := s(a,b)` and compares all
11 reconstructed terms against an independent actual-cut enumerator. The
primitive probe has two cuts, whereas the supplied composite has five.
Substituting only in the primitive probe's two terms would miss its proper
internal cuts. The client retains these, rather than pretending evaluation
is a coefficient Hopf morphism.

## Portable verification and trust boundary

`accepted_certificate.json` and `refused_certificate.json` contain native
trees, actual supplied implementations, signature commitments, full cut
profiles, all second-stage profiles on residuals and inside detached factors, and intact-composite contracts. The
verifier reconstructs the trees, typechecks, recomputes complete signatures,
and recomputes the evidence. It does not trust claimed signatures, factors,
residuals, decisions, or nested flags.

The producer uses the established recursive antichain enumerator. The verifier
uses an independent vertex-subset enumeration with ancestry-prefix tests and
an independent residual builder. It shares the existing native typechecker,
canonical keys, and finite-signature algorithm: this is independent cut
verification, **not** a second independent implementation of the entire
semantics. Acceptance compares full signatures; hashes only serialize
commitments and are not substituted for that equality check.

Nine corrupted certificates are rejected: forged signature, forged decision,
deleted composite cut, deleted nested term, reordered composite children,
wrong payload type, forged residual signature, altered hole seam, and deleted inside-detached-factor cut. This
is integrity of mathematical evidence, not sender authentication. The input
language is the existing research kernel, not a hardened untrusted-input
service; resource limits and schema hardening would be required for deployment.

The universal future-implementation conclusion still depends on the paper
theorem and its stated fixed material profile and jointly admitted extension
conditions. The executable evidence establishes the supplied finite instances.
No fixed-base rejection is inferred merely from an unrealizable formal probe:
the refusal fixture supplies the concrete closed counterimplementation.

## Results

`results.json`: PASS. Accepted replacement, witnessed refusal, both intact
composite contracts, 11 actual cut terms, 53 matched nested terms, exact
11-term composite expansion, strict nested-flag identity, staged/composed
refill equality, and all nine tampering rejections pass.

The client verifies primitive typing as declared in each native syntax node; it does not verify membership in an external fixed-base rule registry. Consequently no certificate alone proves an extension is permitted by such a registry. Simultaneous installation requires payload occurrence namespaces disjoint from the retained host and other payloads; collisions (including capture risks) are rejected, and the exact combined free interface is checked. A namespace-collision regression passes.
