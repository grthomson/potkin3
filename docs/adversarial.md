# Adversarial assessment: Section 4 structural normalization

13 October 2026. Paper-level analysis against the uploaded Ciabattoni–Genco text and the latest Codex report. No new Lean claim.

## Source scope

The supplied paper assumes external-context-sharing rules, one active component in each premise (except EC), and absence of cross-component eigenvariable obstructions when reducing arbitrary rules to that format. Lemma 4.6 postpones external contractions by the lexicographic measure (maximum EC rank, number at that rank). Lemma 4.7 constructs repeated applications of one such rule. Lemma 4.8 then arranges EW. None alone is logical Cut elimination. Section 5 obtains analyticity by translation plus an independently supplied analytic-rule completion theorem.

The latest Codex report proves scoped certificate gluing and signed context action for its exact native setting. The certificate semantics remains the fixed right-ghost fragment. It has not yet interpreted arbitrary hypersequent derivations or the paper's nonlocal 2-system instances. Structural context geometry can transfer more generally only after native signature/admission adapters are proved.

## Strongest immediately feasible combined theorem

Fix a context-sharing rule schema r with n >= 1 ordered premises, one active component C_i per premise, conclusion active hypersequent H, and a proof that every context extension used below is an admitted instance. Fix G,c,d,e,x with e <= d and sum(x)=d-e. Construct the canonical full n-ary depth-e open derivation whose node after a prefix w of length k has conclusion

    G | H^(c+e-k) | product_i C_i^(x_i + count_i(w)).

At a nonleaf, each premise increments exactly its corresponding C_i count and reduces the H exponent by one. This is precisely an instance of r under the required extended context. Leaves are indexed by physical words w in {1,...,n}^e, with profiles count(w); do not identify them.

Prove native admission and the boundary formula, then use the existing installed-cut/context machinery on this explicitly constructed open derivation. This gives full physical-cut/refill correctness for the actual normalization expansion, not merely an abstract n-ary tree.

For Lemma 4.6 additionally choose, for each leaf profile alpha, a donor premise i with alpha_i >= m_i (after the exact d=q specialization). EW must be an actual admitted chain supplying the remaining components. Copy the donor's derivation at each physical use; retain explicit origin renaming. Finish with the stated EC queue. Prove the same end-hypersequent and absence of newly introduced logical Cut whenever the old premises and r are Cut-free. Formula analyticity is a separate theorem requiring the relevant rule property.

This is an appropriate D2/D3/D4 milestone. It can lead to a D6 comparison and D1 result later; it is not already that larger theorem.

## Counterexample 1: profiles do not determine CK records

Take n=2,e=2. Four physical provider positions are 11,12,21,22. Their profiles are respectively (2,0),(1,1),(1,1),(0,2). Install the same provider P_alpha at positions with profile alpha, with coherent occurrence renaming.

The cuts selecting {11,12} and {11,21} have the same multiset of selected profiles, and their pruning forests contain the same two provider templates P_(2,0) and P_(1,1). Their literal remainders differ:

    r(r(Box20,Box11), r(P11,P02))
    r(r(Box20,P11), r(Box11,P02)).

The first empties both premise positions of one sibling, the second empties one position in each sibling. Typed native node labels may vary with the profile; that does not remove this difference. A same-profile summary cannot be substituted for the full addressed cut carrier, remainder, or witness matching.

The boundary coincidence for words 12 and 21 is weaker than identity of their positions in the surrounding proof. It permits template reuse under a proved adapter; it does not permit merging the occurrences.

## A corrected compression theorem that is useful

Suppose an observer of a canonical expansion is evaluated by a local algebra, and every node label/provider value and required scope adapter factors through (depth k, prefix profile alpha). Then compute its value once per reachable state (k,alpha), keeping the n ordered outgoing premise roles. Reuse the computed value in each occurrence but combine repeated children independently using the observer's operation.

For scalar cut-size enumeration, with positive-node root-selection weight u, the recurrence is

    Q_(k,alpha) = u + product_i Q_(k+1,alpha+e_i)

at each positive expansion node. At the leaf boundary use the actual installed-provider Q, or 1 for an unfilled zero-node Box. This retains independent cut choices through multiplication. No physical cuts have been deleted. A multivariate local decoration weight can replace u if it also factors through the state.

There are sum_(k=0)^e binom(n+k-1,k) = binom(n+e,e) states including leaf profiles, compared with n^e physical leaf positions. For fixed n this is polynomial in e; it is not polynomial uniformly in n and e. The arithmetic-circuit size can be bounded by the number of states times n, but expanded polynomial output and integer bit complexity may still be large.

This proves correctness of a compressed computation of that observer, not a compact representation of arbitrary full CK tensors. In particular, residual-tree-valued observations must retain the actual branching information or a proved suitable quotient. Grounding/certificate observers additionally require shared-scope compatibility; profile equality alone supplies none.

This is a genuine new choice over the failed inventory route: compression is derived from a specified normalization family's recursive construction and a verified observer algebra, not guessed from coarse rule data.

## Counterexample 2: normalization need not be CK compatible

Consider a derivation a of H|C|C and a distinct component D. The valid local permutation

    EC_C(EW_D(a))  -->  EW_D(EC_C(a))

has the same end-hypersequent H|C|D. Both sides are cut-free if a is. Their CK extraction records differ: selecting the immediate child gives EW_D(a) tensor EC_C(Box) on the left and EC_C(a) tensor EW_D(Box) on the right. Other source-payload terms similarly have different literal exteriors. Thus even a harmless structural permutation need not preserve the full coaction literally.

A rewrite quotient equating the two whole derivations is not automatically a coalgebra quotient: proper tensor factors need not be equated by that relation. One must prove a coideal condition or retain the exact extraction defect. The already verified same-boundary context action transports such local defects:

    delta(C[P']) - delta(C[P]) = K_C(delta(P') - delta(P)).

This relies on actual identical native boundary types and the chosen record linearization. It cannot be applied when the transformation changes a boundary until an explicit boundary adapter is supplied.

## Counterexample 3: copying invalidates positive-linear compiler assumptions

The existing macro-defect note gives the decisive example: b(P) mapped to f(P,P). Transporting the source child-cut yields P tensor f(Box,Box), while the target both-copy cut yields P^2 tensor f(Box,Box). Single-copy target cuts also exist. Therefore the difference is not generally a positive sum of extra cuts. A copying normalization cannot inherit the positive-linear-macro theorem by renaming it a compiler.

Correct factorization: physical copying/deleting wiring with explicit origin/scope maps, followed by a linear template. Apply the full physical-hole cut law to copying and the positive macro theorem only where its actual hypotheses hold.

Duplicating a derivation in a metatheoretic tree construction does not by itself invoke object-level internal contraction. In this route the actual object-level EC/EW uses and the admissibility of the context-sharing r instances must be exhibited; do not conflate this with an unrestricted contraction principle for every substructural base.

## Generic-rule trap

Without context-parametric admission, the repeated-r expansion can be false. A schema allowed only at empty external context may admit its initial instance C_1,...,C_n / H but reject the extended contexts needed at depth two. Calling it 'the same rule' does not discharge this side condition. Eigenvariable freshness or fixed global resource side conditions can cause the same problem.

Use either an explicitly parametric external-context rule family with proof of stability, or instantiate a concrete permitted structural hypersequent rule and prove the exact extensions. Context-sharing shape alone, viewed as one isolated concrete occurrence, is insufficient.

## Normalization and cost traps

- q = 1 + sum_i(m_i-1) is a sharp universal pigeonhole threshold for the donor condition, not a lower bound on every possible proof normalization's size.
- n^e leaves and (n^e-1)/(n-1) internal nodes describe the canonical full expansion for n>1; for n=1 the counts are 1 and e. They are not optimality results.
- Compressed evaluation may use a DAG internally; the proof and CK carrier remain the unfolded rooted tree. Do not transfer DAG cut semantics to it.
- A source cut-free proof remains cut-free under a construction inserting only non-Cut r, EW and EC. It need not thereby gain the subformula property if r does not have it.
- The EC-rank measure of Lemma 4.6 is a theorem about its specified global strategy. Arbitrary local copying rewrites may increase size and other measures; do not announce unrestricted strong normalization.
- Certificate transport under normalization need not be a bijection or count preserving. Existing gluing bijections concern decomposing one fixed source, not changing that source by copying or erasure.
- An antipode rebasing identity is useful for cumulative analyses only after coefficients, character/linearity properties, and observer semantics are supplied. It is not a logical normalizer.

## Recommendation

Proceed with the concrete Lemma 4.7 expansion plus one EC-postponement family, and derive a CK observer recurrence and a verified compression theorem for its canonical profile-indexed construction. Keep the proof-producing revival compiler as a connected but distinct native semantics target. The strongest useful connection is not 'normalization preserves CK'; it is 'normalization has an exact, compositional extraction effect, which can be evaluated efficiently for specified analyses while preserving proof reconstruction'.

## Independent audit: early stopping gives a stronger construction

The root and other agents proposed an improvement during review. It passes the proof-theoretic audit and should replace full expansion as the main positive result.

In Lemma 4.6 put q=1+sum_i(m_i-1), G''=sum_i G'_i, and fix each donor derivation D_i of G|G'_i|C_i^mi. At recursive state alpha define k=sum(alpha), h=q-k and target

    B_alpha = G | G'' | H^h | product_i C_i^alpha_i.

If some alpha_i >= m_i, stop and weaken D_i directly to B_alpha. Otherwise h>=1 by the pigeonhole bound, and apply r to the recursively constructed n children B_(alpha+e_i). Their common external context is G|G''|H^(h-1)|C^alpha, so the rule instance is admitted by the same context-parametric hypothesis. Its conclusion is B_alpha. Start at alpha=0 and finish with the ordinary EC queue from G|G''|H^q to G|H.

The decisive point is that EW can add H components before all q layers of r have been built. The original full expansion delayed this opportunity. No logical Cut or new rule is required. Every branch stops by depth q; the stop addresses form a prefix-free antichain, but the transformed proof still contains positive donor/EW trees at those interfaces, not bare terminal holes.

For m=(1,M), the only continuing branch increments the second coordinate. There are exactly M r nodes, M terminal copies of D_1 and one of D_2. The full depth-M binary expansion has 2^M donor leaves and 2^M-1 r nodes. This is an exact construction-to-construction comparison, not an optimality theorem or runtime benchmark.

Counting one EW per added component, a leaf using donor i adds

    |G''|-|G'_i| + h*|H| + |alpha|-m_i

components, where the common initial G cancels and each C_i is one component. This is valid as a chosen tagged multiset embedding even if some concrete C_i or components of H/G coincide. Such coincidences may permit an earlier stopping condition or cheaper weakening, so no minimality is asserted. Repeated donor copies have their own physical addresses and independent extraction choices. A cache may reuse their checked templates with fresh occurrence origins; it must not merge their CK nodes.

The replacement of a full-expansion region by an early-stop donor/EW proof has exactly the same hypersequent boundary, so the existing K_C local-to-global defect equation is applicable once the concrete native signature adapter exists. The difference is not generally positive and the two proofs need not have equal certificate counts. A scoped grounding interpretation requires its own interpretation of these hypersequent rules; validity in HLJ is established directly by the r/EW/EC construction.

Early stopping is not merely a compressed evaluation of the same tree: it constructs a smaller actual proof tree. Profile memoization is a second, independent optimization of evaluation/construction. Keep those two contributions distinct.

## Audit: cost-optimal canonical stopping plans and a tied-cost separator

Fix donor derivations and use one positive node per EW. Put g_i=|G''|-|G'_i|. Among canonical plans that stop at an eligible donor or continue with one r and all its n ordered children, down to maximum depth q, the Bellman recurrence is

    V(alpha) = min(
      { |D_i| + g_i + (q-|alpha|)|H| + |alpha|-m_i : alpha_i>=m_i },
      { 1+sum_i V(alpha+e_i) : |alpha|<q }).

At depth q the first set is nonempty. The recurrence proves minimum unfolded proof-tree node count within this grammar by backward induction: every plan has exactly one of the two root forms and continuation subplans have disjoint physical occurrence sets. Shared memoized numeric evaluation does not charge fewer physical copies. This is not an optimum among all derivations, all normalizers, or arbitrary alternative structural adapters.

For n=2,m=(1,2),q=2,|H|=4,g=0 and one-node donors, the proposed early/full trees have ten positive nodes and exactly these cut-cardinality spectra:

    early = 1+10z+22z^2+10z^3;
    full  = 1+10z+26z^2+26z^3+8z^4.

They are respectively r(chain5,r(chain2,chain1)) and r(r(chain2,chain2),r(chain2,chain1)), where a length-L positive unary chain has Q=1+Lz. The arithmetic is correct. BUT a one-node donor of C_2|C_2 is not the singleton identity axiom displayed in the paper's Fig.1. Thus this exact fixture requires an explicit additional/generalized nullary-rule convention, and must not be called an ordinary HLJ fixture without it.

A direct repair uses D_1 as one-node identity and D_2 as identity followed by EW, hence two nodes. Since D_2 occurs once in each plan the costs remain tied, now at eleven nodes. The two trees become r(chain5,r(chain2,chain2)) and r(r(chain2,chain2),r(chain2,chain2)), with

    early = 1+11z+29z^2+20z^3;
    full  = 1+11z+33z^2+40z^3+16z^4.

Four final EC nodes add 4z to either spectrum, yielding fifteen-node closed constructions. A concrete admitted two-premise rule with four conclusion components is still required; arbitrary declarations of a node shape are not its proof.

For the nonnegative scalar antichain-size observer and a fixed compatible one-hole context, Q(C[P])=a_C+b_C Q(P) with nonnegative b_C. Coefficientwise comparison therefore survives context installation. It means the full construction offers more frontiers at each cardinality while the early construction has fewer such decomposition obligations; which direction is desirable depends on the application. It does not imply dominance of grounding feasibility, useful caches, proof semantics or runtime. Those require richer interface-sensitive coefficients. Signed general coefficients do not inherit this order argument automatically.
