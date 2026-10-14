# Concrete tensor-shell extension of the carrier comparison

## Recovered intended calculus

The original source is identifiable directly, not inferred from the classical proof-net work. `prior_sources/august_material_occurrence.txt`, §5.12, printed p.48, specifies single-conclusion **intuitionistic multiplicative linear logic**, with fusion `•` (tensor) and implication, multiset contexts, Gentzen Cut, and no Weakening or Contraction. Atomic-base applications are material; logical rules and Cut are nonmaterial. Atomic reflexivity is removed from the detached material observer.

Printed p.52 names the full linear palette: both principal cells; each nonprincipal Cut permutation through each premise of tensor right/left and implication right/left, on either side of Cut; both Cut–Cut reassociations; and both identity cells. Its Theorem 5.18 is an occurrence-observer result for Υ. It is expressly not a theorem of descent of the actual pure-material CK coaction. This distinction survives the current completion: principal tensor fusion still separates the two notions.

## A complete canonical observer for the tensor-only fragment

There is an explicit positive extension beyond implication: the unit-free linear tensor calculus with variables of arbitrarily nested tensor type, Pair, tensor elimination Let, explicit Cut, and named atomic primitive rules of finite arity. Primitive conclusions and inputs are atoms; primitive physical identifiers remain rigid. The executable version handles nonhypothetical primitives. Its source judgments are exact occurrence-indexed linear contexts.

Define the **atomic-leaf expansion** of `x:A⊗B` recursively as the pair of indexed resources `(x,0):A` and `(x,1):B`; nested types add path indices. Atomic `x:a` becomes the leaf `(x,(),a)`. Evaluate the proof recursively:

- Pair becomes an ordered pair of expressions.
- An atomic primitive becomes its named operation applied to the recursively evaluated atomic arguments.
- `Let P as (x,y) in Q` evaluates P to a pair and substitutes its two components into Q.
- `Cut(P,x,Q)` substitutes the complete evaluated P for x in Q.
- A material vacancy is a distinct named atomic constant retaining its complete interface.

Call the resulting finite expression `L(t)`. Every linear resource leaf is used once; evaluation never copies or discards a material operation. This is directly implemented in `carrier_client/tensor_shell.py`, independently of the implication checker.

**Canonical-observer theorem.** L is sound and complete for the tensor βη theory with linear Let commuting conversions, explicit Cut substitution equations and context exchange, retaining fixed primitive names and ordered primitive ports.

**Proof.** Soundness is substitution composition, ordered pair substitution and pair η. For completeness first η-expand each free tensor resource to its uniquely indexed atomic leaves. Commute these resource-destructuring Lets outward in a fixed order. Evaluate each remaining Let/Cut: a closed or constructed tensor value is a pair; a neutral tensor variable has already been expanded. The result is exactly the ordered Pair/primitive expression L, with the fixed outer destructuring telescope. No elimination remains internally. Both the expansion telescope and this expression are determined by L and the complete indexed context. Reversing these equations gives a representative of every input proof, so identical L values yield equivalent proofs. No implication, tensor unit, copying, erasure or untracked operation is used. ∎

This supplies the independent normal observer needed by the abstract logical-shell construction in a genuine tensor fragment. It is not a conditional appeal to a future convergent rewrite system. It does not supply a combined tensor–implication observer: function-valued neutral expressions and their interaction with Let require an additional construction.

## Native sequent interpretation and actual CK consequence

Tensor right maps to Pair. Tensor left with principal assumption `z:A⊗B` maps to `Let z as (x,y) in J(Q)`. Gentzen Cut maps to explicit one-use Cut. Retain source-origin labels on the introduced Let/variable macros for raw readback, exactly as with implication macros. Since every extra node is logical or Ref, this translation preserves actual positive pure primitive cones and their complete vacancies. As previously, compare detached forests under the declared commutative observation; no full CK macro map is asserted.

Use the actual projected coaction, not an occurrence inventory, to form

`F_tensor(t) = (id_H ⊗ L) ρ_material(t)`.

This is a finite exact Counter of actual material forests and fully evaluated residual shells. Coassociativity makes its image a material subcomodule of the cofree target with coaction `Δ_H⊗id`. The Cut/Pair and Cut/Let passive permutations preserve it: actual selected primitive roots correspond, the active bound occurrence blocks a new pure cone through the moved wrapper, and corresponding residuals have the same L by substitution composition. This includes Cut whose interface itself is tensor-valued. Independent Let exchanges similarly preserve the profile when the exchanged scopes satisfy the linear resource side conditions.

Principal tensor beta is not generally admitted: with closed selected nullaries δ and ε,

`Let Pair(δ,ε) as (x,y) in r(x,y)`

and `r(δ,ε)` have identical L but material profiles of respectively **4 and 5 terms**. The new fifth term is the composite material cone r(δ,ε). Conversely a principal reduction that retains a logical Pair between supplied components is accepted in the checked example. Thus this concrete tensor observer supports the intended distinction between ordinary logical normalization and CK-preserving normalization.

The finite-mode completion can now be instantiated using this explicit shell observer and an appropriate canonical reification telescope, rather than assuming a tensor rewrite oracle. The current tensor executable checks the cofree profile and future atomic-input modes; it does **not** yet implement the full combined canonical mode-core construction, or prove mode completeness for compound open inputs. In particular tensor-typed free inputs have indexed atomic components, so any future mode algorithm must declare how its input modes treat these components rather than silently considering only atomic entries of the outer context.

## Executed checks

Run `python continuation_2026_10_10/carrier_client/tensor_shell.py`.

Eight exact comparisons pass: tensor principal material fusion (correctly distinguished), tensor η, Cut into either Pair premise, Cut into either Let premise, compound-interface Cut/Pair, and a principal tensor case retaining the logical boundary. The passive cases additionally pass **28 free atomic-input purity modes** with fresh formal material providers. A nested tensor η case checks recursive indexed resource expansion, and an independent two-Let exchange checks elimination scheduling. Every comparison validates complete contexts and types; profiles enumerate actual material antichains and exact residual expressions.

The source code and `carrier_client/tensor_results.json` provide finite evidence. The canonical-observer argument above is a paper proof; it is not proof-assistant formalization. The comparison remains strictly narrower than the full original IMLL palette and narrower than arbitrary classical MLL+Mix identity.
