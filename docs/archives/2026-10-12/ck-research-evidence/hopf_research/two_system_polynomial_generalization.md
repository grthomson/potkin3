# From arbitrary scoped 2-systems to the same polynomial/CK framework

12 October 2026. Narrow paper-level generalisation. This is not a theorem
about scheduling normal forms, the hypersequent embedding, or Cut elimination.
No Lean verification is claimed.

## 1. Exact source discipline

Ciabattoni--Genco, *Hypersequents and Systems of Rules: Embeddings and
Applications*, arXiv:1805.04852v1, Definition 2.1, pp. 5--6, specifies a
2-system with top roles r_1,...,r_k and one bottom rule. The bottom has k
premise derivations with the same endsequent as its conclusion. Inside its
i-th premise derivation, role r_i may occur repeatedly, using fixed active
multisets Sigma_{i,0},...,Sigma_{i,n_i}; the surrounding top-rule context and
succedent may vary between occurrences. The displayed role has shape

    Sigma_{i,1},Gamma' => Pi'    ...    Sigma_{i,n_i},Gamma' => Pi'
    ---------------------------------------------------------------- r_i
                       Sigma_{i,0},Gamma' => Pi'.

The paper allows schematic variables to be shared between different roles.
Those are exactly the identifications declared by the chosen system schema;
there is no universal requirement that all roles use identical active tuples.
Remark 2.1 explicitly contrasts the definition with an earlier once-only
restriction. No requirement to use every role is added here. The later
embedding argument can remove unused/redundant system applications, but that
is not a condition of this carrier.

Primary source inspected directly:
https://arxiv.org/pdf/1805.04852 , Definition 2.1 and Remark 2.1; the
parameter-sharing interpretation is also stated in its introduction.

## 2. Data for one concrete system instance

Fix a registry of system schemata sigma. For each sigma define a set
Par(sigma) of **persistent instance parameter packs**. A pack theta contains:

* the active multiset tuple for each top role;
* the values of any schematic parameters shared between roles or with the
  bottom, subject to precisely the schema's declared identifications;
* any further explicit instance-level side conditions of that schema.

Equivalently, define Par as the set of compatible role tuples directly,
without retaining irrelevant extra presentations of the same tuple. Do not
freeze occurrence-local Gamma',Pi' in theta unless the schema specifically
declares them persistent. Those local contexts are chosen at each top-rule
occurrence and must form the displayed literal inference instance.

The theorem below starts with **explicitly instantiated** system instances:
each bottom carries sigma,theta, and each top occurrence carries its owning
bottom and role. This avoids an artificial uniqueness assertion when an
unannotated derivation has unused roles or underdetermined schematic values.
Different parameter completions of such an unannotated derivation are
different decorated witnesses, not automatically distinct underlying proofs.
Par(sigma) can be infinite; finitary means finite premise arity, not finitely
many possible formulas or parameter packs.

## 3. Local state and constructors

A state is (S,E), a literal sequent S and an ordered stack E of active ancestor
system instances. Each entry has data (sigma,theta,j), where j is the bottom
premise branch containing the current position. Physical owner identity is
represented by stack position. The constructors are:

1. **Ordinary rule.** Any literal base-calculus rule instance transports E
   unchanged to each of its premises. Its input/output sequents are its actual
   rule instance. No weakening or contraction assumption is silently added.
2. **Bottom.** Choose sigma,theta and a permitted literal bottom instance with
   endsequent S. For each premise j, its input state is
   (S, E ++ [(sigma,theta,j)]). Thus the single chosen theta is shared across
   all the bottom's premise branches. The new owner is scoped over each of
   those branches, and no other branch is identified with it.
3. **Top.** Choose one active stack entry at a specific de Bruijn index. If it
   has (sigma,theta,j), choose a literal occurrence of top role r_j whose
   active tuple agrees with theta and whose occurrence-local context and
   succedent satisfy the rule. Its ordered premises inherit E unchanged.
   The constructor retains the selected index, role, and actual local rule
   instance. Selecting one of two eligible owners remains a distinct choice.

There is no pop operation along the root-to-premise traversal: an owner
exists precisely in its descendant premise states, and disappears outside
them by lexical tree structure. A top may select an older ancestor rather
than the most recent one. Multiple tops of one owner may occur on the same
path. Tops of distinct owners may be entangled. The grammar does not assume
the normal forms used by the source's hypersequent translation.

## 4. Scope-localisation theorem

Call a decorated literal derivation **validly scoped** when every top belongs
to an actual ancestor bottom, lies in the corresponding role's premise
branch, and has exactly the persistent active parameters of that bottom,
with all ordinary and system rule instances locally valid.

**Theorem.** Explicitly parameter-instantiated, validly scoped 2-system
derivations are in bijection, modulo consistent owner-ID renaming, with closed
locally typed constructor trees of Section 3 at empty-stack root. The same
statement holds for open derivations relative to a specified ordered external
scope interface.

**Proof.** Traverse an instantiated scoped derivation from its root. Record
each entered bottom's pack and branch role on the stack; replace every top's
owner ID by its index in that stack. Scope validity makes the lookup defined
with the correct role. Persistent-parameter validity makes the local top
constructor admissible. Ordinary rules simply preserve the stack. This
determines all states and constructors uniquely modulo owner naming.

Conversely, give each bottom in a typed tree its physical address as owner ID.
Resolve each top's stored index against the ancestor stack. The selected
bottom is an actual ancestor in the prescribed branch, and equality with its
pack is ensured by the local constructor. All local rule instances are valid
by construction. This produces a validly scoped derivation. The two maps are
inverse after the safe owner-name quotient, since an index selects exactly
the same physical ancestor in both directions. Open interfaces are carried
unchanged throughout the same argument. QED.

This is a representation theorem for the explicitly scoped notion, which is
the occurrence-labelled form of the source's instance discipline. It does
not decide from a bare unannotated rule tree which instance assignment is
intended, nor quotient different possible assignments into one.

## 5. The algebraic consequences are now generic to scoped 2-systems

Let I be these states, B the local constructors, and E the pairs consisting
of a constructor and one of its physical premise slots. The diagram

    I <- E -> B -> I

defines a finitary polynomial. Consequently all the constructions proved in
`polynomial_bridge.md` apply without changing their proofs:

* open proof trees are its P-trees, with distinct zero-node state edges e_i;
* the full cut bialgebra keeps every positive-node extraction frontier;
* H=B_P/(e_i-1) is a connected graded CK-style Hopf algebra;
* rho=(q tensor id)Delta is its coaction on typed remainder modules, with
  rho(e_i)=1 tensor e_i and whole extraction T tensor e_i;
* indexed one-hole contexts have the exact McBride spine decomposition;
* Green sums satisfy the genuine many-type Faà di Bruno cut/grafting identity

    Delta(G_i) = sum_n (product_j G_j^{n_j}) tensor g_{i,n}.

The same basiswise completion or explicit locally finite signature conditions
are required. Infinite parameter domains do not invalidate finitary local
constructors or the finite witness bijections; they do prevent unchecked
finite numerical counting claims.

This is the stronger D4 orientation: the algebraic framework is not confined
to one accidental LQ observer. It is available for the scoped 2-system
formalism itself. LQ's forced-colour partition diagrams and checkpoint
relations are a particularly explicit and useful coefficient semantics for
one analytic certificate problem within that framework. Other systems need
their own exact parameter/obligation semantics; no universal finite equality
solver is asserted.

## 6. Precise native and proof-theoretic gaps

The current theorem supplies no new hypersequent embedding or normalisation
strategy. To instantiate it in POTKIN3, one must identify the native rules,
instance packs, ordered premise roles and owner-ID annotations with this
definition, prove the correspondence, and compare the native eligibility
policy with all positive nodes. The canonicalisation must retain literal
sequent/formula data and physical occurrence addresses.

To transport through the published hypersequent embedding or focused macro
expansion, one must account for copying, new internal vertices and changed
cut fibres. The source's existence of equivalent calculi does not itself
prove a Hopf morphism. Open-boundary cut/substitution compatibility remains
the requested D4/D6 theorem. D1 analytic/Cut consequences require the actual
source's base assumptions; D3 structural adapters are not created by the
polynomial representation. D5 contextual replacement follows only after a
sound coefficient semantics and matching boundary theorem are supplied.

Thus the advance here is exact and structural: arbitrary explicitly scoped
2-systems admit the same typed polynomial/CK/Faà di Bruno framework. Its
proof-theoretic applications are specific further theorems, rather than a
claim that tree packaging alone gives analyticity.
