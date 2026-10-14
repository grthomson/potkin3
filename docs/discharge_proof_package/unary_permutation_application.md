# Concrete application: unary LJ permutations across Sys(com) discharge

## Independently specified rules
Let S = Gamma,A => B and T = Gamma => A -> B. The ordinary LJ implication-right inference R maps S to T. Let b be an instance of the Sys(com) bottom rule, with fixed shared top-rule parameters Phi,Psi. Its two premises and conclusion are equal; that common sequent may be either S or T. Top rules assigned to b must occur in their prescribed premise branch and use its shared Phi,Psi. These are Ciabattoni–Genco Definition 2.1 and the communication instance, not new correctness conditions.

The open conversion is

  R(B_b(?0,?1))  --->  B_b'(R(?0),R(?1)).

Both holes have boundary S; both whole fragments have boundary T. b and b' share the same top-rule parameters and branch numbering but have different common bottom sequents. They are globally corresponding occurrences, not literally identical complete rule instances.

## Relation to established normalization
Aschieri–Ciabattoni–Genco, Goedel Logic: from Natural Deduction to Parallel Computation, arXiv:1607.05120, Figure 1, contains

  lambda x^A (u ||_a v) ---> (lambda x^A u) ||_a (lambda x^A v).

This is the corresponding natural-deduction/term permutation. Their Theorem IV.2 already proves subject reduction. We must not claim that preservation itself is new, nor silently claim a complete translation to the term calculus. The proposed application is a universally quantified open Sys(com) discharge-preservation result and its CK extraction certificate transport for this established structural conversion.

The reverse orientation factors a repeated inference and shrinks proof syntax. It is NOT their stated normalization orientation. Use the displayed forward direction when discussing their normalization procedure.

## Global occurrence transport
Addresses are root-first. Source holes lie at 0.i and target holes at i.0 (i=0,1); a filling occurrence at suffix a is sent from 0.i.a to i.0.a. The unique shell bottom goes from source address 0 to target root. Outside occurrences retain their identity modulo insertion-address prefixes. Ordinary R copies introduce no system top or bottom applications. Each filling's internal rule occurrences and discharge assignments remain unchanged, except references to the shell bottom use its declared b-to-b' correspondence.

For every filling occurrence, shell bottom ancestry and branch index i are identical before and after transport. The bottom's shared parameters are identical. Hence every explicit top-to-bottom assignment satisfies its rule-discharge condition before iff after. This proves preservation AND reflection, not just existence preservation. Filler-internal assignments, external assignments, and relationships between branches are preserved because a single global b-to-b' map is used. No holewise independent renaming is allowed.

Ordinary local typing follows directly from R and the bottom rule. For implication-right the two fillings have S and both outputs have T. This sequent presentation needs no term-variable capture claim; a later term translation must additionally handle ordinary lambda binding.

## Finite boundary summary for this application
At each hole the exact available shell discharge data are the single entry (b, Phi,Psi, i), transported globally to (b',Phi,Psi,i). There are no shell top applications and hence no outstanding shell discharge requirements. The summary omits the placement and copies of R and the changed bottom sequent, precisely because neither is inspected by the independent rule-discharge conditions. This is a non-identical-interior pair satisfying the summary theorem.

More generally, R can be any fixed finite chain U of unary ordinary propositional LJ inferences, with fixed endpoints S,T, no system top/bottom applications, and valid local side conditions. The same proof is induction on chain length. For a k-premise system bottom, the identical argument works at all k physical holes. Binary logical permutations duplicating bottom occurrences are outside this bijective correspondence theorem and need a separate copying theorem.

## CK consequence
Write F_t(z) for the physical full-cut frontier polynomial, F_Box=1 and F_node=z+product F_children. For a unary chain U of m positive ordinary nodes, F_U(t)=F_t+m z. For the binary permutation:

  F_source=(m+1)z+F_P F_Q,
  F_target=z+(F_P+mz)(F_Q+mz),
  F_target-F_source=mz(F_P+F_Q-1)+m^2 z^2.

Since every F has constant term one, the last polynomial has nonnegative coefficients. At z=1 the normalization permutation increases full-cut cardinality by m(Q_P+Q_Q)+m^2-m. This is an exact structural cost of the literature's normalization direction, not a speedup claim.

Full typed extraction records are not ordered by that scalar/polynomial inequality: changing the bottom boundary changes record types. Reuse the established physical packet/gluing and macro-defect laws to transport and compare full records. The new discharge summary must compose with their occurrence-resolved restriction and gluing maps; a separate scalar corollary is insufficient.

## Payoff and limit
The conversion can be certified before either premise is completed, including fillings whose top-rule applications are discharged by b inside the transformed fragment. Its certificate can be checked through successive CK cuts without losing that dependency. This strengthens the applicable project replacement theorem's future-filling scope. Literature priority of the whole package is unestablished, and the underlying permutation/subject reduction is already known.

Primary source: https://arxiv.org/pdf/1607.05120 (Figure 1; Theorem IV.2; appendix subject-reduction case 7). Ciabattoni–Genco source supplied by user, arXiv:1805.04852 Definition 2.1.
