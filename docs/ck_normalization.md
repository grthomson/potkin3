# CK analysis of contraction-postponement expansion

Status: PAPER DERIVATION plus finite executable checks; no new Lean result. Based on the supplied text of Ciabattoni–Genco Lemmas 4.6–4.7, with full CK/context conventions from the project. The source paper proves derivability and normalization; the optimizations and CK recurrences below are our proposed additional analysis.

## 1. Precise expansion states and early stopping

Fix the external-context-sharing n-premise rule r with premises G|C_i and conclusion G|H. Let source proofs D_i conclude G|G'_i|(C_i)^{m_i}, with m_i>=1 and every component of G'_i already present in G. Put G''=G'_1|...|G'_n and q=1+sum_i(m_i-1).

At profile a in N^n with |a|<=q, use the hypersequent

    S_a = G | G'' | H^{q-|a|} | product_i C_i^{a_i}.

For |a|<q, the n premises S_(a+e_i) yield S_a by r. This is the literal local instance of Lemma 4.7. Whenever a_i>=m_i, S_a already follows from D_i by external weakening: choose the source's existing occurrences and add the rest. Therefore branch expansion may stop at the FIRST threshold hit instead of always continuing to depth q. At every depth-q profile some threshold is hit, by the source's pigeonhole argument.

The resulting proof remains cut-free if the D_i are cut-free; it uses only r and EW before the concluding EC queue. All EC movements still have the source paper's structural hypotheses. This is NOT a proof for an arbitrary resource-sensitive base without EW/EC.

At internal profiles 0<=a_i<m_i, the number of physical occurrences with profile a is multinomial(|a|;a). Hence the number of r nodes of the early-stop tree is

    N(m)=sum_(0<=a_i<m_i) multinomial(|a|;a),

and its number of source leaves is 1+(n-1)N(m). The full-depth unfolding has (n^q-1)/(n-1) r nodes for n>1. An early-stop tree is obtained by pruning entire full-expansion subtrees, so these counts are weakly smaller. It is uniquely minimal in r-node count among r-expansion trees that may terminate only at threshold-enabled profiles. This optimality does not range over other logical normalization methods.

Examples: m=(2,2): 5 rather than 7 r nodes, 6 rather than 8 source leaves. m=(2,2,2): 16 rather than 40 r nodes, 33 rather than 81 leaves. For m=(1,M), the early-stop tree is a comb with M r nodes and M+1 leaves, whereas q=M full unfolding has 2^M-1 r nodes and 2^M leaves.

The fixed root still contains H^q. This construction does not reduce q or remove its final contraction queue.

## 2. Full CK recurrence, including weakening and actual source proofs

For a positive rooted proof tree P let Q_P(y)=sum_A y^{|A|}, where A ranges over all occurrence-address antichains, including empty and root selections. This forgets labels but retains the number and multiplicity of physical cuts. A positive leaf has Q=1+y. A typed interface leaf with no positive occurrence has Q=1. These are different states.

For an r occurrence with children P_1,...,P_n,

    Q_(r(P_1,...,P_n))(y) = y + product_i Q_(P_i)(y).

For w unary EW occurrences above a source P,

    Q_(EW^w(P))(y) = w*y + Q_P(y).

The two summands distinguish the unique selected ancestor from cuts strictly inside the payload. They are disjoint and exhaustive. No eligibility filtering, factor deduplication, or deletion of internal EW cuts occurs.

Choose the terminating source index j(a) deterministically. Let w(a,j) be the exact number of EW rule applications in its chosen boundary adapter. The complete early-stop proof has recurrence

    Q_a = Q_(D_j(a)) + w(a,j(a))*y       at a terminal profile,
    Q_a = y + product_i Q_(a+e_i)        otherwise.

The final EC queue contributes one y for each unary contraction node. Actual source proofs are not opaque unless that opacity is explicitly the observer's definition.

When H has h components and the chosen EW adapter adds one component per rule, the component-count cost, with no cancellations and a fixed occurrence embedding of D_i's conclusion, is

    w(a,i) = |G''|-|G'_i| + (q-|a|)*h + |a|-m_i.

This formula requires the displayed source/target contexts; coincident component formulas do not license collapsing physical occurrences. In particular, for a singleton H the EW count for source i is constant in a: |G''|-|G'_i|+q-m_i. Early stopping then does not increase that source's individual boundary-adapter length. For multi-component H it may, so reductions in r nodes/source leaves alone do not imply a reduction of total primitive-rule count.

The complete **address-sensitive** polynomial is

    F_P({x_v}) = sum_A product_(v in A) x_v,
    F_(r(P_i)) = x_root + product_i shift_i(F_(P_i)),

where shift prefixes every descendant address by its physical premise index. This recurrence retains each physical cut once. A monomial's selected addresses determine its full pruning packet and typed remainder in the fixed source P, so it is also an exact index for reconstructing the complete coaction. The polynomial alone without P is not that coaction.

## 3. Profile dynamic programming without merging physical cuts

There are product_i m_i internal profile states, although their full unfolded tree can be exponential. Provided the source selection, EW adapter and scalar observation depend only on profile, Q_a can be evaluated once per profile and reused. Repeated uses are multiplied as distinct physical slots. They are NOT identified as a single selected occurrence.

For example, if two children have the same polynomial Q, their contribution is Q^2, not Q and not 2Q. It counts independent selections in their two physical copies. Absolute addresses are reinstated by prefix shifts when reconstructing packets. With scope-sensitive decorations, one must add enough boundary/scope state to make the reused summary invariant; profile equality alone is not a certificate equivalence.

This computes a projected CK spectrum compactly. It does not compute exponentially many distinct full addressed extraction packets in polynomial output size. Even scalar coefficients may have very large bit-length, and expanding the polynomial by cut width is an additional cost. A safe complexity statement is O(n*product_i m_i) arithmetic-circuit gates, plus the supplied source/adapter summaries and terminal states. No polynomial-in-binary-input or full-proof-size speed claim follows automatically.

For m=(1,M), if terminals are opaque Box leaves, the comb has Q=1+M*y. If every terminal is a single positive source node and there are **no EW wrappers**, put B=1+y and Q_0=B; then

    Q_M = y + B*Q_(M-1),
    Q_M = B^(M+1) + y*sum_(j=0)^(M-1) B^j,
    Q_M(1)=3*2^M-1.

This is a shape-only benchmark. Actual Lemma4.6 adapters generally contain EW nodes; inserting them through the terminal recurrence is mandatory before claiming a native normalization cut count.

## 4. Compiler choices and swallowed alternatives

If one explores several valid stop/expand constructions, root selection must still count the compiler's choices of descendants, even though it swallows their internal cuts. Let P_a be the generating function of construction plans, and R_a the joint generating function of plans and CK cuts. With plan weight t for an r node, terminal options j of weight u_j and source spectra Q_j:

    P_a = sum_(eligible j) u_j + t*product_i P_(a+e_i),
    R_a = sum_(eligible j) u_j*Q_j
          + t*(y*product_i P_(a+e_i) + product_i R_(a+e_i)).

Omit the expansion term at |a|=q; include appropriate EW costs in u_j or extra source spectra. The factor product P in the root-selected term is essential: replacing it by 1 loses distinct construction plans; replacing it by product R counts forbidden internal cuts below the selected root. This is precisely the ancestor-swallowing distinction handled by the verified K context construction.

## 5. Shared certificates versus independent choices

DP reuse of an already computed scalar summary is safe for counting independent cut selections. It must not conflate two different semantics of copied certificate providers:

- Independent copies choose witnesses independently, giving W^k at the Type level (and |W|^k counts when all interfaces agree).
- A compiler choosing one witness and copying it k times uses the diagonal W -> W^k, with image cardinality |W|, not |W|^k.

Shared owner colours and side conditions add further compatibility relations. They require the verified dependent gluing interface; neither Q_a nor a profile multinomial proves them. The proposed use is to prepare a certificate generator once for a proven equivalent boundary state, then instantiate it at fresh physical positions with explicit shared external parameters.

## 6. Connection to verified context action

For any same-boundary normalization step P -> P' in a compatible native context C, the verified linear context law gives

    delta(C[P']) - delta(C[P]) = K_C(delta(P')-delta(P)).

Thus a local defect computed by the above recursion propagates to an arbitrary exterior. A sequence telescopes after applying the actual successive context actions. This is a compositional comparison of extraction records, not preservation of the CK coproduct, invertibility of normalization, or a proof of logical admissibility/termination.

A useful next native theorem package is: construct the early-stop derivation; prove admission and cut-freeness under stated source assumptions; prove its rule count; prove its full-cut summary recurrence including EW nodes; then derive contextual transport using existing K laws. The source/target normalization carrier may be the same calculus here. Cross-presentation comparison needs separate source/target decorated CK objects.

## Validation

`check_threshold_normalization.py` independently constructs 39 small physical threshold trees, checks their rule and leaf counts against the multinomial formula, compares unfolded cut recurrence with profile-DP recurrence, and explicitly enumerates physical antichains for cases with at most 13 internal nodes. Its bare terminal leaves are opaque interfaces; the printed spectra are deliberately labelled as such. These finite checks support implementation arithmetic only; the preceding universal statements are paper derivations, not inferred from the samples.

## 7. EW-complete arithmetic fixture: an actual reversal

Take n=2, m=(2,2), q=3, G'=empty, H with h components, and supplied one-node positive source derivations of (C_i)^2. This is a schematic relative-to-source fixture: it does not claim those source sequents are theorems of bare HLJ. Count the complete r/EW/source construction before the identical final EC queue.

The early-stop tree has two terminal profiles at depth 2 (each requiring h EW nodes) and four at depth 3 (each requiring one EW node). Its total positive-node size is 15+2h. The full-depth construction has 23 nodes. Their full CK cut-count polynomials are determined by

    B_h(y)=1+(h+7)y+(5h+9)y^2+(4h+4)y^3,
    Q_early(y)=y+B_h(y)^2,
    Q_full(y)=y+[y+(y+(1+2y)^2)^2]^2.

Therefore Q_early(1)=1+(21+10h)^2 and Q_full(1)=10202.

- h=1: early-stop has 17 versus 23 nodes and 962 versus 10202 CK cuts.
- h=20: early-stop has 55 versus 23 nodes and 48842 versus 10202 CK cuts.

The final EC queue adds the same number of nodes and one cut per node to both constructions; it does not change either comparison. This explicitly proves that early stopping is not a universally beneficial total-size or cut-count heuristic when H can contain many components. A stop/continue dynamic program with exact adapter costs, rather than a blanket early-stop policy, is the stronger normalization improvement. For a fixed selected plan, the full-cut recurrence above computes its exact spectrum. Selecting among plans can minimize size and then cut count among size ties because node cost is additive and cut count uses monotone products of positive child cut counts. This is optimal only within the stated expansion-plan grammar.

## 8. Contextual dominance theorem: why the optimization composes

For the cut-width polynomial observer (forget labels but retain occurrence multiplicity), every positive one-hole context C has polynomials a_C,b_C in N[y] such that

    Q_(C[P]) = a_C + b_C Q_P.

Induction down the unique hole spine proves this: sibling spectra multiply the payload term; selecting an ancestor contributes a term independent of cuts inside P. Equivalently this is the scalar projection of the L/A context splitting. For nested contexts,

    b_(C[D])=b_C b_D,
    a_(C[D])=a_C+b_C a_D.

Thus Q_P<=Q_P' coefficientwise implies Q_(C[P])<=Q_(C[P']) coefficientwise, and Q_P(1)<=Q_P'(1) implies the corresponding global cut-count inequality. The latter is exact:

    Q_(C[P'])(1)-Q_(C[P])(1)
       = b_C(1) * (Q_P'(1)-Q_P(1)).

Node cost adds the fixed exterior size. Therefore a local choice that is no larger and has no more CK cuts remains no larger/no-more-cuts in EVERY compatible fixed exterior. This is a reusable, compositional optimality certificate for the plan DP, rather than a claim about a single closed normalization example. If one keeps coefficientwise cut-width dominance, one also certifies every nonnegative weighted sum of cut-width coefficients. Multi-hole contexts are multiaffine with nonnegative coefficients in distinct physical provider spectra, so simultaneous coefficientwise-dominant replacements also preserve dominance, including repeated identical providers when interpreted as physical copies.

Limits: this observer's dominance does not prove logical replacement validity; the checked compiler/interface theorem supplies that separately. It does not compare shape-sensitive or owner-sensitive extraction observations, nor prove Hopf equality. Exact boundary compatibility and fixed external context are essential. The quantity optimized here is explicit combinatorial extraction size, not a claimed runtime cost. Its use becomes operational when an analysis actually visits or materializes those cut records; any such runtime claim needs its own implementation cost model.
