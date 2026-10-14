# Exact contracts across a linear rule compiler

Independent derivation, 11 October 2026. This develops the combined D4/D1 comparison gate. It is generic mathematics plus explicit SELL hypotheses, not an assertion that full CK or normalization commutes with SELL repair.

## 1. Separate proof substitution from extraction

Let S and T be two typed proof languages with the same interface set. Write S(J), T(J) for their providers. Contexts retain distinct, physically indexed typed holes. Suppose F acts on proofs and contexts and satisfies

    F(C[P1,...,Pk]) = F(C)[F(P1),...,F(Pk)].                    (1)

This is supplied by a fixed exactly-once rule-macro compiler with coherent typing and routing. An arbitrary colinear linear map does not supply (1).

For a source context C, a target accepted predicate L_T and a source tuple domain D_S, define

    Good_S(C,D_S) := every P in D_S satisfies C[P] in L_S,
    Good_T(FC,D_T) := every Q in D_T satisfies FC[Q] in L_T.

Provider domains can be correlated relations; do not replace them by products of their marginals. Assume observer compatibility

    P in L_S iff F(P) in L_T.                               (2)

This can be obtained by defining L_S as the pullback, but that does not establish agreement with a separately motivated source property. Such agreement needs its own proof.

### Contract transfer theorem

If D_T = F^k(D_S), then Good_S(C,D_S) iff Good_T(FC,D_T).

Proof: for each source tuple, (1) and (2) identify its acceptance with the acceptance of its image. Image coverage quantifies over exactly the target tuples. This works identically for existential acceptance and produces counterexample transport in both directions when image witnesses are available.

More precisely:

* If F^k(D_S) is contained in D_T, target universal safety implies source universal safety.
* If D_T is contained in F^k(D_S), source universal safety implies target universal safety.

These are useful one-sided statements when exact domain equality fails. The directions should not be reversed.

The corresponding joint weakest preconditions satisfy

    WP_S(C,L_S) = (F^k)^(-1)(WP_T(FC,L_T))                  (3)

without surjectivity. Equation (3) classifies source providers. It does not state that the image equals the full target weakest precondition.

## 2. Retracts and ALL target providers

Suppose G:T->S is an inclusion fixing interfaces and FG=id_T. Then F is surjective at every interface. For unrestricted provider domains, D_S=product_i S(J_i) and D_T=product_i T(J_i), the exact image condition holds. This proves transfer for ALL target providers, not only an image-restricted class.

For restricted domains, the sufficient checks are F^k(D_S) contained in D_T and G^k(D_T) contained in D_S. Their combination gives exact image equality. In particular, admitting all source proofs but only Cut-free target proofs does not meet the first check, and admitting only Cut-free source proofs need not meet the second.

For correlated domains the checks must use the joint relation. Per-hole surjectivity does not imply joint surjectivity. Example: source allows only two tuples (0,0),(1,1), target allows all four Boolean tuples, and every coordinate map is the identity. Every target coordinate is covered while off-diagonal tuples have no admitted joint lift.

### SELL completion instance

Take S to be the permission-completed calculus WITH Cut, T the original calculus WITH Cut at the same promotion preorder. F expands each newly enabled structural rule by its chosen old-rule macro and fixes every old rule. G is inclusion of old proofs. Then FG=id exactly (up to the declared occurrence renaming convention), and (1) follows from one-use macro filling. Thus unrestricted-provider contract transfer is available whenever (2) is proved.

This is stronger than claiming that only compiler-image target providers are covered: every old provider already has the explicit source lift G(Q). But it is weaker than asserting that every independently motivated observation is compiler-invariant. For instance, a source Cut-free weakening rule can compile to a target macro containing Cut. Cut-freeness, raw size, derivation height and number of Cut steps do not satisfy (2). Normalized material demand might satisfy it in a suitable semantics, but requires a separate normalization compatibility proof. No such theorem is assumed here.

## 3. Actual selected CK cuts: a sufficient bijection criterion

The archived quotation theorem (`CK_COMPOSITIONAL_BASE_NORMALIZATION_2026-10-01(1).md`, Theorem 7.2) proves that natural generic one-use quotations correspond to fixed typed macros. It does not by itself prove the following extraction criterion; that criterion is checked directly.

Fix material rule constructors B, kept distinct from logical identity. Assume:

1. Every selected material rule compiles to itself with its original ordered ports.
2. Every unselected source rule compiles to a positive typed macro all of whose added rule vertices are unselected.
3. Every source premise occurs once, with its complete interface and physical left-to-right order preserved (or with the same explicitly declared order transport on both sides).
4. Typed vacancies remain vacancies and their routes are transported coherently. The pointed whole-provider endpoint is kept distinct from the ordinary empty-forest endpoint.

Then the selected material cuts of P and F(P) correspond bijectively, with literal detached material forests and compiled remainders.

Proof. A target pure-material subtree cannot contain an added macro vertex. It therefore lies entirely in an unchanged material part descending from a unique source occurrence. Conversely, every source pure-material subtree survives unchanged: its constructors are fixed and it has no unselected shell to expand. One-use substitution preserves ancestry/incomparability between these occurrences, and ordered routing preserves their detached forest order. Thus source admissible antichains of pure-material roots and target ones correspond. Puncturing at corresponding roots commutes with the macro compiler by (1). The empty and selected whole-provider cases obey the separately declared endpoint convention. Repeated occurrences remain distinct, so coefficient multiplicities are preserved.

Consequently, on an already established source and target material comodule carrier,

    rho_B(F(P)) = (id ⊗ F) rho_B(P).                        (4)

The pointwise occurrence bijection is stronger evidence than simply checking a scalarized version of (4). It also supplies compatible nested flags by applying the same argument to each actual punctured remainder and extracted piece. This is an application of the archived macro/flag discipline, not a new general coaction law for a carrier lacking one.

Conditions 1–2 rule out a hidden failure: a compiler that deletes every unselected vertex of a formerly impure subtree can create a new pure-material extraction. Exactly-once usage alone would not prevent that. Similarly, a compiler that inserts a selected identity material node would create an extra selectable occurrence.

### SELL check

The weakening repair macro and the nested contraction repair macro described in round 2 use their old premise once. Their new nodes are logical dereliction, promotion, old weakening/contraction, logical identity and Cut. If these are all explicitly unselected and the original material constructors are fixed, the criterion applies. A designated material identity from another project carrier must not be silently identified with this unselected logical identity.

## 4. What (4) does and does not transfer

For a fixed P, (4) with its positive occurrence bijection transports all predicates on corresponding extracted material and corresponding remainders, as well as finite nested cut queries. In particular, independently supplied target predicates can be pulled back to source cut predicates exactly.

A universal inverse-assembly residual asks more: it ranges over ALL proofs admitting a cut with a specified remainder. A compiler's pointwise cut bijection for F(P) does not show that every target host with remainder F(R) is compiled from some source host with remainder R. Two separate additions can resolve this:

* Work with genuine fixed-hole filling contracts and use (1) plus the provider-domain theorem above.
* Prove a host-lifting theorem for the full target assembly relation, with exact boundary and source-remainder reconstruction.

Do not replace the second theorem by colinearity. In a fixed-hole material-cut setting, if every target host is literally F(R)[Q] and Q lifts through G, filling R[GQ] supplies the required host lift. Ordinary untyped CK inverse assembly also allows extra detached components and varying attachment positions; those must be included in the source assembly relation before the same argument can be used.

## 5. Explicit negative examples

### A. Even a full Hopf inclusion does not cover all target providers

Let H_a be the ordinary decorated CK Hopf algebra with label a, and H_ab the one with labels a,b. The inclusion F is a full Hopf map, hence preserves every CK cut. Give every tree the same provider sort and take the one-hole identity context. Let L_T mean no b vertex occurs; its pullback L_S is all source trees. Every source provider satisfies the source contract. The target provider b violates the target contract. Thus Hopf preservation, and a fortiori relative colinearity, does not supply target-provider coverage. Here no G with FG=id_Hab exists.

### B. Coverage does not give observer compatibility

Let S include an old unary rule l and a new derived rule r; let T have l alone, with F(r(P))=l(l(FP)), F(l(P))=l(FP), and G the old-rule inclusion. Then FG=id. With a fixed common nullary provider a, source property raw height at most two accepts r(a), but target raw height at most two rejects l(l(a)). Filling and surjectivity hold; property (2) fails. This is the same reason raw Cut-freeness cannot be transferred through a Cut-using repair macro.

### C. Exactly-once alone does not preserve selected cuts

Let a selected material leaf a sit below an unselected unary r, itself below a selected unary f. Compile r(P) directly to F(P), fixing a and f, using the premise exactly once but adding no positive shell. The source tree f(r(a)) is not pure material; its target f(a) is. Source material selections are empty and the a subtree. Target selections additionally include the whole f(a) tree. Thus its extra coefficient f(a) has no source counterpart, falsifying (4) under the weaker one-use-only hypothesis. An unchanged unselected outer wrapper c gives the same failure with proper nonroot selected cuts only.

The smaller source r(a) would NOT be a counterexample: its proper a cut maps to the whole target a cut, so the pointed coaction can still agree. The selected ancestor f is essential to creating a genuinely new material coefficient.

## 6. Value and novelty status

Equations (1)–(3) are ordinary inverse-image/substitution facts. The project already has one-use macro and material naturality machinery. A contribution candidate is the **concrete SELL repair instance together with a genuinely meaningful observer and complete target-provider coverage**, or a precise counterexample showing why the observer cannot transfer. Neither should be inflated into new automata theory or automatic normalization preservation.

The natural positive exponential demand benchmark currently pursued in parallel is a separately justified D4 observer. Its semantic contract must be proved first; importing it into SELL completion additionally requires (2). Keeping those two results distinct avoids a false bridge.
