# Threshold-pruned contraction postponement

Paper-level development, 12 October 2026. Primary source: supplied transcription of Ciabattoni–Genco, *Hypersequents and Systems of Rules: Embeddings and Applications*, Section 4.2.1, Lemmas 4.6–4.7. The construction below refines the literal uniform-depth witness in that proof; no publication novelty or Lean claim is made.

## 1. Exact setting and assumptions

Fix n>=1 and a rule schema r with one designated active component in each premise:

    (X | C_1), ..., (X | C_n) / (X | H).

Here X is an arbitrary finite multiset hypersequent, H is a fixed finite multiset of active conclusion components, and the displayed substitution instance of C_i,H is fixed throughout the construction. The schema must admit every context X used below. Thus context restrictions, eigenvariable conditions crossing components, or a merely isolated admissible instance require separate proofs; they are not silently subsumed by context sharing.

Given m_i>=1 and EC-free supplied derivations D_i of G | G'_i | C_i^{m_i}, assume every component of G'_i also occurs in G. Put G''=sum_i G'_i, q=1+sum_i(m_i-1). EW adds one arbitrary component, and EC contracts two identical component occurrences. Physical copies of a supplied derivation are copied trees, not a graph quotient. Internal owner/binder identifiers require freshening; external interface identifiers remain shared according to the logical signature.

The paper constructs G|G''|H^q by r/EW and then contracts to G|H. Its explicit Lemma 4.7 expansion, unfolded literally to depth q, has n^q supplied-proof slots and sum_{k<q} n^k occurrences of r.

## 2. Adaptive recurrence

For a vector x in N^n with |x|<=q, define the boundary

    B(x) = G | G'' | H^(q-|x|) | sum_i C_i^(x_i).

Define a proof T(x) of B(x) recursively, starting at x=0.

* If some x_i>=m_i, stop. Choose such i and weaken a fresh physical copy of D_i to B(x).
* Otherwise apply r to the n recursive proofs T(x+e_i).

The recursive call is well-founded by q-|x|. If all x_i<m_i, then |x|<=sum_i(m_i-1)=q-1, so there is an H copy to become the active conclusion of r. Its shared context is exactly

    G | G'' | H^(q-|x|-1) | sum_j C_j^(x_j).

Premise i has one additional C_i. This proves all rule typings, not just a tree-shape recurrence. At a terminal vector reached from the root, exactly one coordinate has just reached its threshold: x_i=m_i and x_j<m_j for j!=i. Therefore the selected supplied proof is unambiguous even if multiple formula components happen to coincide syntactically.

The terminal weakening count, for the particular designated multiset inclusion, is

    w(x,i)=|G''|-|G'_i| +(q-|x|)|H| + |x|-m_i.

All terms are nonnegative. Fix an explicit order for these EW insertions. This order is part of the literal proof and can affect CK extraction; do not equate alternative weakening placements merely because their boundaries agree.

At the root B(0)=G|G''|H^q. Append exactly

    c=|G''|+(q-1)|H|

EC nodes, first removing the designated G'' duplicates into G, then reducing q copies of each occurrence-position of H to one. Aliases between G and H do not invalidate this designated construction. It may not be a minimal contraction sequence when equal components admit alternative accounting, but its stated length is exact for this protocol.

### Theorem A: proof-producing soundness

The recurrence terminates and returns a derivation of G|H. Every upper-segment inference is r or EW, every introduced EC belongs to a terminal queue, and each supplied D_i is inserted as an intact copied derivation. If r is not logical Cut and all D_i are Cut-free, the output is Cut-free. If the rules/premises satisfy a specified formula-analyticity invariant, the recurrence adds no formulas except those already in G,G'_i,C_i,H; a stronger subformula theorem needs the corresponding premise/rule invariant.

Proof: induction on q-|x| using the exact contexts above, followed by the designated EC queue. No Cut rule or semantic completeness argument is used.

This improves a local witness in the global EC-postponement argument. Global strategy termination still uses the source paper's EC-rank measure; the local optimality theorem below is not a replacement for that global proof.

## 3. Exact physical sizes and strict improvement

Let U={x:0<=x_i<m_i for every i}. For x in U, exactly |x|!/(prod_i x_i!) physical internal occurrences have profile x: every permutation of its letters stays below all thresholds.

Thus the exact number of r applications is

    I(m)=sum_{x in U} multinomial(|x|;x).

Terminal words ending in i have penultimate profile y with y_i=m_i-1 and 0<=y_j<m_j for j!=i. Their exact number is

    L_i(m)=sum_{such y} multinomial(|y|;y).

Write L=sum_i L_i. The full n-ary tree identity gives L=1+(n-1)I, including n=1 (one leaf). Every terminal word has length <=q; its final letter and profile identify its source D_i.

With d_i the node count of D_i, exact total output size is

    c + I + sum_(terminal physical words u) [w(profile(u),last(u)) + d_last(u)].

Copy counts, EW counts and supplied-proof sizes are kept separate. There is no assertion of a runtime speed-up for an implementation not supplied here.

For n=2 and m=(1,M): q=M, U={(0,k):0<=k<M}. Hence I=M, L_1=M, L_2=1. The uniform-depth witness has 2^M leaves and 2^M-1 r nodes; the adaptive witness has M+1 leaves and M r nodes. For m=(2,2), q=3, the reduction is from 8 to 6 leaves and from 7 to 5 r nodes.

### Caution: first stopping does not minimize total proof size

For m=(1,2), G empty, G'_i empty, and |H|=h, first stopping uses 2 r nodes, 3 supplied-proof copies and h+1 EW nodes. Uniform depth 2 uses 3 r nodes, 4 supplied-proof copies and 3 EW nodes (choosing D_1 at both mixed-profile leaves). With supplied proof sizes d_1,d_2, first-stop minus uniform total size is h-3-d_1; the final EC queue is the same. Consequently first stopping can increase total size when H has many components. The r-count optimality below deliberately does not claim total-size optimality. The parent investigation develops a weighted stop/continue dynamic program that includes both constructions as options.

## 4. Optimality in an explicitly restricted typed resource instance

Assume now that the C_i are pairwise distinct component symbols; none appears in G,G'_j,H; and H is nonempty and contains no such symbols. The upper-segment derivations may use only r, EW, and the supplied D_i as opaque leaves. No extra logical derivations, EC, other rule instances, or component identifications are allowed.

### Theorem B: optimal number of r applications

Among upper-segment derivations of G|G''|H^q in this restricted language, T(0) minimizes the number of r applications.

Proof. Traverse any such derivation from conclusion toward premises, deleting unary EW nodes from its shape. This gives a full n-ary tree of r nodes whose leaves are the supplied D_i. Along a branch, let x_i count selections of premise i. Initially there are no C_i; a reversed r adds one C_i in branch i; reversing EW can only remove components. Hence a leaf D_i with m_i C_i requires x_i>=m_i. Every leaf word must therefore hit a threshold. The unique smallest full n-ary prefix tree with that property is the tree stopping at the first threshold. It is obtained from any competing tree by deleting all descendants after the first threshold. Its r-node count is I(m).

### Theorem C: sharp H-multiplicity threshold

In the same restricted language, if G and the G'_i also contain no components of H, at least q active copies of H are necessary in the upper-segment conclusion (taking H to be one fresh component is sufficient for the theorem).

Proof. Backwards, every r removes one H and EW never adds H. An adversary can select premise letters without reaching any threshold for q-1 steps: any ordering of the multiset with m_i-1 copies of each i works. A leaf is impossible before hitting a threshold, and q r steps require at least q copies of H at the conclusion. The construction attains q.

The qualifications are essential. If C_1=C_2=C and m=(2,2), two total premise selections already supply C^2, so q=3 is no longer sharp. If H aliases available premise/context components, more shortcuts may exist. These are valid logical optimizations, not errors in the construction. The optimality result concerns the declared r/EW language and the separated resource instance, never arbitrary derivability in the ambient logic.

## 5. Full CK cuts by dynamic programming without identifying occurrences

Fix the literal EW protocol. Let Q(P) count all full rooted branch cuts, including empty and whole-root selections. For a positive node with children P_j,

    Q(node(P_1,...,P_k))=1+prod_j Q(P_j).

A unary EW or EC adds one. For a terminal profile x ending in i, set

    F_x = w(x,i)+Q(D_i).

For an internal profile x,

    F_x = 1+prod_i F_(x+e_i).

Then Q(output)=c+F_0. This counts all physical CK cuts of the actual unfolded proof; no cut filtering or pathwise merging occurs. Its proof is structural induction on the explicit proof recurrence.

More strongly, with z recording the number of selected regions, replace 1 by z:

    F_x(z)=w(x,i) z+Q(D_i;z)          at terminals,
    F_x(z)=z+prod_i F_(x+e_i)(z)      internally,
    Q(output;z)=c z+F_0(z).

Here Q(D;z)=sum_c z^(number of selected subtrees in c). This is a cut-width spectrum, not just a node-size statistic. It is a specialization of full CK decomposition; literal forest factors/remainders require richer records.

The number of distinct profile states needed for this numerical recurrence is

    prod_i m_i + sum_i prod_(j!=i) m_j.

Memoizing this recurrence is valid because the scalar observation is insensitive to physical address renaming and the literal subtree recipe is determined by x. The rooted proof carrier remains the expanded tree. No DAG Hopf algebra or quotient of physical proofs is introduced.

Arithmetic operation counts do not imply a polynomial bit complexity: coefficients and degrees can be large. A scoped certificate kernel can use the same sharing only after proving equivariance and equality/transport of inherited boundary states. An address-dependent observer refutes unqualified profile caching.

## 6. Why this is useful for the current project

This supplies a genuine logical normalization family with arbitrary supplied proofs, explicit structural hypotheses and costs, a strict construction improvement, and an exact CK observation recurrence. It uses the paper's normalization objective rather than inventing a new toy calculus.

D2: actual physical copying is quantified. D3: context sharing, EW and final EC are explicit. D4: the produced derivation is compositional and Cut-free whenever its providers are. D5: profile caching has a precise sufficient condition; certificate sharing requires the established scoped interface theorem. D1: this structural stage can support a later Cut-elimination transport, but it is not itself Cut elimination. D6: translation of these derivations to systems of rules remains a separate adapter, with its own CK correction.

Most promising next theorem: mechanize T(x), admission/Cut-freeness, first-hit optimality in the separated instance, and full-cut spectrum recurrence in one connected native development. The context K theorem then transports its before/after extraction difference through arbitrary admitted exteriors. Do not replace this with scalar checks alone.

## 7. Signed normalization defect: a necessary distinction

Let X_i(z)=Q(D_i;z). In the original local proof, each D_i is followed by c_i=|G'_i|+m_i-1 designated EC steps and then r. Therefore

    Q_old(z)=z+prod_i (X_i(z)+c_i z),
    Q_new(z)=c z+F_0(z).

The difference can have either sign after evaluation; the positive extra-internal-cuts theorem for linear positive macros does not apply automatically to structural normalization.

For n=2, m=(1,1), |G'_1|=1 and |G'_2|=0, q=1. The old proof contracts the extra shared context copy above premise 1. The new proof weakens that copy into premise 2 and contracts it below r. Then

    Q_old=z+(X_1+z)X_2,
    Q_new=2z+X_1(X_2+z),
    Q_new-Q_old=z(1+X_1-X_2).

In particular Q_new(1)<Q_old(1) whenever Q(D_2)>Q(D_1)+1. The provider contract allows such pairs: an EC-free, Cut-free provider can have arbitrarily long internal weakening/contraction detours while retaining its end-hypersequent. This is not an algebraic pathology; the EC site changes which large subtree can be swallowed together with it.

Full before/after extraction records must consequently use a signed difference, transported to exteriors by the existing K_C action. The scalar specialization above is a necessary regression example for any proposed positivity statement about EC-postponement.

## 8. Actual HLJ+communication fixture

Take the paper's communication rule with Phi=A, Psi=B, both Gamma contexts empty, Pi_1=A, Pi_2=B, and empty external G. Its active premises are C_1=(A=>A), C_2=(B=>B), and conclusion is H=(B=>A)|(A=>B). Let m=(2,2). Each donor D_i is an ordinary identity axiom C_i followed by one EW adding another C_i. Thus |D_i|=2, both donors are EC-free and Cut-free, and Q(D_i;z)=1+2z.

Here q=3, |H|=2. The first-hit construction has 5 communication nodes, 6 donors, and 8 EW nodes: there are two terminal words of length 2, each requiring two EW, and four terminal words of length 3, each requiring one EW. Hence its upper segment has 25 nodes. The uniform-depth construction has 7 communication nodes, 8 donors and 8 EW nodes, hence 31 nodes. Both append four EC nodes, giving actual cut-free HLJ+com derivations of H with respectively 29 and 35 nodes.

The full physical cut-width spectra are:

    Q_first = 1+29z+218z^2+960z^3+2233z^4+2664z^5+1296z^6,
    Q_uniform = 1+35z+359z^2+2262z^3+8431z^4+19314z^5
                  +26730z^6+20412z^7+6561z^8.

Thus the cut totals are 7401 and 84105. These numbers follow from the exact recurrence, independently evaluated by integer polynomial arithmetic; they are not Lean-checked claims. The coefficient of z agrees with the positive-node count in each case, as every positive occurrence supplies exactly one singleton selection.

This example uses the actual published communication rule, ordinary identities and EW/EC. A native registry adapter remains to be built; no such adapter is presumed by this paper-level fixture.
