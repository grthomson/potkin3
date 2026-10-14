# Independent implementation: sorted CK residuals

## Files and reproduction

Run from the workspace root:

```
python research_round3/test_typed_checker.py
python research_round3/test_typed_natural.py
```

`typed_checker.py` implements a generic finite sorted ranked registry, exact reachable joint-observer-state saturation with actual closed tree witnesses, a deterministic word automaton for correlated ordered material tuples, a universal filling recognizer, counterexample reconstruction, and a finite all-antichain CK observer. `test_typed_checker.py` and `test_typed_natural.py` test it using independently enumerated cuts and literal filling.

## Implementation meaning

An open tree carries a relation `(u,q,v)`: starting the material-word observer in state u, there exists a correctly sorted ordered tuple of providers whose filling produces target state q and leaves the word observer in state v. Hole transitions range over **reachable** sorted joint states; they do not assume arbitrary pairs of provider and target observations are jointly realizable. A finite product observer can carry both observations. Rule transitions compose child relations in premise order.

Universal acceptance means there is no triple whose first state is initial, whose last state accepts the provider tuple, and whose q violates the target. Empty provider classes therefore yield vacuous acceptance. Feasibility is explicitly tested separately in the nonvacuous natural application. The counterexample operation enumerates exact reachable state choices for the finitely many holes, then uses saturation witnesses to produce real providers and a bad assembly.

For each closed input, the all-antichain observer retains a pair consisting of the actual extracted material word action and the relation state of its open remainder. Selecting the root produces a typed hole; declining the root recursively combines child cuts. In particular, root selection and the empty cut remain distinct. The finite summary intentionally forgets multiplicities: it recognises Boolean properties of CK cuts and is **not** a coefficient-preserving Hopf quotient or an asserted coaction on these finite states.

## Generic tests

Two observers on a six-rule, two-sort registry were tested separately. Each test covered all 255 closed trees of size at most six, their 2,678 literal cuts, and 683 distinct remainders. Each remainder relation was compared to literal filling over exact reachable representative providers. Every reported bad residual was accompanied by real accepted providers and an independently evaluated bad assembly.

Complete context-state saturation terminated in five rounds: 15 P / 17 Q states for the correlated-support example and 7 P / 7 Q states for the ancestry example. Every state has a real context witness and was checked against literal filling. These are complete finite saturation results, distinct from bounded input-tree enumeration.

Specific failure tests check:

* correlated provider pairs versus their independent projections;
* equal rule multisets but different nesting depth;
* typed root versus empty endpoints;
* rejection of incorrectly sorted providers;
* universal-contract vacuity.

## Integrated logical application

The second test instantiates the same recognizer using the positive-exponential material-demand observer from `check_natural_demand.py`. Its finite registry contains closed p (C), closed !p (B), and p under one unrestricted x:p (O). The constructors are a, unary material g, binary merge, promotion, let!, and the scoped variable x. It permits arbitrarily nested closed providers; it does not permit unboundedly many simultaneously open variable names.

With budget 2, capped affine states are `(c,d)` with cap 3. Let observes `c_Q+d_Q*c_P`. Exact reachable-state saturation has 4 B states, 4 C states and 16 O states, stabilising in six rounds. All 831 well-sorted closed/open terms up to size seven were compared with independently implemented substitution normalization; 12,696 literal CK cuts agreed with the generic summary.

The provider word language accepts exactly a B-provider followed by an O-body satisfying `c_Q+d_Q*c_P<=2`. The let context with those two antichain holes passes universally and nonvacuously. Adding an outer g fails; the recognizer reconstructs an actual assembly whose normal form has three g nodes. The contract admits expensive/erasing and cheap/duplicating combinations while excluding expensive/duplicating: independent projections are unsound.

Seven nested fixed-type duplicators normalize to 128 material nodes, while the finite observer returns overflow exactly. Thus finiteness of the observer is not a bound on proof size or amplification. Zero demand still erases overflow; clipping is not interpreted as a positive infinity with undefined zero multiplication.

## Limits

These are executable independent checks plus the companion mathematical theorem, not Lean mechanization. The generic automata algorithm is conditional on finite observation and registry data. The natural benchmark measures material occurrences **in the normal form**, not reduction time, peak space, effects, deadlock freedom, or general Cut elimination. The all-antichain construction genuinely uses rooted decomposition and compatible scoped holes, but ordinary finite tree-automata methods supply much of its algorithmic mechanism. Neither novelty nor a new Hopf algebra on finite observer states is claimed.

The optional `query(t)` uses one provider language both to select the actual extracted tuple and to specify replacement tuples. This is a tested special case. A migration query may instead use independent old-material and new-provider languages; the residual theorem does not require the old tuple to satisfy the replacement policy. Implementing the general query requires a separate old-material word observer in the first component of the all-cut summary, while leaving residual relations unchanged.

Natural-application reviewer clarification: the budget predicate on an O-root tests its constant contribution c, equivalently substitution of zero-cost inputs. It is not a guarantee for every arbitrary external substitution. The reported universal let contract and counterexample have closed C roots, for which c is the complete normal-form material count; the B-root interpretation is likewise closed.
