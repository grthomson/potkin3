# CK convolution as a calculus of coordinated certificate replacement

12 October 2026. Independent algebraic investigation. All universal results
below are paper proofs. This is not a Lean theorem and does not establish
full LQ revival. The concrete semantics is the connectivity/variable
consistency component of a revival certificate.

## 1. Main result and why the query matters

A proof's cached modules can be individually well formed while only some
**simultaneous combinations** preserve a shared discharge-variable
certificate. Full CK cuts enumerate exactly the allowed simultaneous
subtree replacement frontiers. Boundary partition constraints select the
compatible combinations before any Boolean projection.

The resulting family of all-frontier certificate enumerators is acted on
by the convolution group of cache valuations. Consequently:

1. CK coassociativity gives an exact composition law for hierarchical
   certificate-reuse accounting;
2. the antipode removes a previously installed cache valuation;
3. a relative convolution character changes cache valuations without
   reconstructing the underlying exposed-skeleton valuation, provided its
   cumulative values on all required remainders have been retained.

The last statement is an algebraic update formula, not an unproved runtime
complexity improvement. Intermediate coefficients are signed. Negative
coefficients are cancellation terms, not negative numbers of proofs.

## 2. An explicit carrier with typed holes left intact

Fix an indexed rule signature. Every rule symbol records its output type,
ordered input types, and any fixed local decorations. A type may include
the sequent and its named discharge-scope environment. Work with explicit
names before considering any alpha-equivalence quotient.

A *positive partial rule tree* has at least one rule vertex; any input slot
may contain a matching partial rule tree or a typed hole. Internal holes
are retained as missing children in specified slots. A physical cut is an
antichain of rule-vertex addresses, including the empty and root cuts.
Removing a selected subtree leaves a hole of its exact input type.

Let H be the free commutative Z-algebra on these positive partial trees.
It is graded by the number of rule vertices. For a generator t set

    Delta(t) = sum_c P_c(t) tensor R^H_c(t),

where P_c is the forest of detached partial trees. The whole-tree cut has
R^H_c=1; every other remainder is its positive partial tree with all slot
information retained. Extend Delta multiplicatively to forests. The usual
two-cut-flag bijection proves coassociativity: the decorated slots survive
the bijection unchanged. The grading is connected, so H has its connected
graded antipode S.

For every output type e, let M_e be free on Box_e and the positive partial
trees of output type e. Define

    rho(Box_e) = 1 tensor Box_e,
    rho(t) = sum_c P_c(t) tensor R^M_c(t),

where the whole-tree remainder is Box_e, **not a coefficient unit**.
Then M_e is an H-comodule. One short proof identifies M_e with the left
coideal span of 1 and the generators of output type e in H; the copied
vector 1 in this identification is named Box_e in M_e. The direct sum over
e keeps all these typed holes distinct.

More explicitly, j_e(Box_e)=1 and j_e(t)=t give an injective map of free
Z-modules. Every remainder in Delta(j_e(t)) is either 1 or a positive
tree of output e, so Delta j_e=(id tensor j_e)rho_e. Coassociativity and
counitality of rho_e follow by applying the injective maps
id tensor id tensor j_e and j_e, respectively. Tensor injectivity here
is immediate from the displayed free bases. For different e the images
of j_e share 1, but the M_e summands themselves remain distinct. This is
why a single untyped scalar cannot replace their typed endpoint states.

An actual identity inference is a rule vertex, distinct from Box_e. This
construction makes no identity/Cut coaction equation and no claim that a
primitive-to-composite rule expansion is a Hopf morphism. Nor does it
restrict cuts to discharge-saturated frontiers. Open pieces retain their
boundary scopes.

This is an explicit abstract signature-level construction, not yet a
comparison theorem with POTKIN3's native CK carrier. Native comparison
must match endpoint conventions, ordered packets, and coefficient
multiplicities. For a fixed source proof, its finitely many positive
partial subtrees generate an extraction-closed sub-Hopf algebra; finite
source data does not mean a globally finite-state proof language.

## 3. The coefficient algebra remembers shared owners

Fix a finite set U of named boundary ports and a set V of variable labels.
All ports through which future pieces can attach must remain exposed.
Let P(U,V) consist of:

* a partition of U;
* at most one forced label in V on each block;
* a conflict element 0.

Multiply two consistent elements by taking the join of their partitions
and pooling forced labels. If a resulting block has two different labels,
the result is 0. The identity has the discrete partition and no forced
labels. Conflict is absorbing.

LEMMA. This is a commutative monoid with zero.

PROOF. Both parenthesizations take the equivalence closure of the same
union of relations and pool the same forced labels on each final block.
If a conflict arises at an intermediate stage, later joins cannot undo it.
The discrete unlabelled partition changes no constraint. QED.

Take the monoid algebra Z[P(U,V)] and quotient by the ideal generated by
the conflict basis element. Adjoin independent polynomial variables for
cache choices, exposed checking costs, etc. Call the resulting commutative
ring A. Thus [sigma][tau] equals their joined constraint when compatible,
and equals algebraic zero when incompatible.

Individual basis constraints are idempotent, but polynomial coefficients
retain occurrence multiplicity. For example, if sigma tau is compatible,
the two physical choices producing sigma tau contribute twice even when
their boundary summary is equal.

Earlier contextual-compatibility results justify replacing an internally
consistent constraint graph by this summary. Internal components disjoint
from U can be checked and forgotten for consistency. This step is valid
only when later attachments cannot refer to their hidden vertices.

Boolean 'consistent' is NOT a multiplicative map on this ring: two
individually consistent constraints may join to conflict. Likewise the
number of compatible assignments is generally not multiplicative. These
observations are made after convolution, not used as scalar characters.

## 4. Cache valuations and the universal action theorem

For every positive partial tree T, give a finite family Cache(T) of
replacement certificates with the same exact exposed interface, together
with a boundary summary sigma(c) and a formal choice weight y_c. Set

    phi(T) = sum_(c in Cache(T)) y_c [sigma(c)].

The free commutative property extends this assignment uniquely to an
algebra homomorphism phi:H -> A with phi(1)=1. Empty Cache(T) gives zero.
Multiplication of forests makes all simultaneous cache choices and joins
their shared-owner constraints. Names shared across different components
must not be independently freshened.

Let N be any A-module. A typed remainder valuation alpha:M_e -> N may
record exposed checking cost, source-skeleton constraints, certificate
states, or a vector of these. Define

    (U_phi alpha)(m) = sum_(rho(m)) phi(m_-1) alpha(m_0).

For A-valued valuations phi,psi write convolution

    (phi * psi)(h) = sum_(Delta(h)) phi(h_1) psi(h_2).

THEOREM (composition, inversion, cache change).

    U_phi U_psi = U_(phi * psi),
    U_epsilon = identity,
    U_phi^(-1) = U_(phi o S),

and, writing C_phi=U_phi alpha,

    C_psi = U_(psi * (phi o S)) C_phi.

PROOF. Expand the first expression into a double sum. The comodule law
reindexes it into the two coefficient factors of Delta, and associativity
of the A-action gives convolution. The counit gives the identity. Since
phi is an algebra homomorphism, applying phi to the antipode equations
gives (phi o S)*phi=epsilon=phi*(phi o S). Substitute into the first
identity for inversion and cache change. QED.

Every expression on a fixed m is finite. No finite dimensionality of H or
global convergence is assumed. Over a semiring lacking subtraction the
forward transform remains meaningful, but antipode inversion requires
passing to a ring or module with additive inverses.

The space Hom_Z(M_e,N) is closed under every displayed U operation:
rho_e only produces remainders of the same output type/scope e, and finite
A-linear combinations stay in N. The inverse therefore acts within the
same typed observer space, rather than cancelling types or crossing
between unrelated outputs.

The composed action concerns source-derived layers of partial contexts:
an outer cached context may still have holes filled by an earlier layer.
It does not, without another theorem, classify cuts inside arbitrary new
trees produced by module replacement. A source/target substitution law is
the additional bridge required for that operational claim.

The theorem also holds for algebra-valued characters in an associative
noncommutative ring acting on a left module, as far as a character and its
own convolution inverse are concerned. To claim closure of arbitrary
characters under convolution, their relevant images must commute; the
commutative partition-constraint ring above avoids this issue. Arbitrary
interface matrices must NOT be silently substituted for A.

## 5. Exact semantics of the forward transform

Set alpha(R)=z^(number of exposed rule vertices in R)[sigma(R)], where
sigma(R) is the constraint summary of the retained skeleton, including
its still-required external debts. A cut term in U_phi alpha expands as

    product_(selected modules) y_(chosen replacement)
      * z^(exposed rule count)
      * [joined skeleton/replacement constraints].

Therefore its nonzero monomials enumerate precisely the compatible
replacement choices on every CK frontier, with physical multiplicity.
This assertion is a theorem for the constraint-graph model when every
cross-piece constraint is mediated by the retained ports U. It is not yet
a theorem that these monomials enumerate complete LQ revival proofs:
branch routing, occurrence ownership, empty-succedent checkpoints and
formula-flow transport need their own sound, complete interface adapter.

An important distinction: if every cache contains only the original
subtree's exact certificate, the joined constraint is constant across
cuts. The interesting application uses alternative certified modules or
alternative certificate instantiations. The resulting interaction is not
captured by checking the original proof's fixed certificate repeatedly.

## 6. A coordinated replacement that local checks miss

Let U={x} be one shared owner port, and take distinct variable labels p,q.
Write P for the constraint x=p, Q for x=q and E for the unconstrained
identity. In A:

    P^2=P, Q^2=Q, P Q=0, E a=a.

Take the three-vertex partial proof shape t=r(a,a), with ordered left and
right input slots. Both original leaf certificates force x=q; the root
adds no variable constraint. Each leaf has cached alternatives forcing p
or q, with weights u and v:

    phi(a)=u P+v Q.

Keep the two one-leaf remainders b_L and b_R separate. They have equal
valuations in this example, but are distinct slotted trees. The native
cut contributions are

    1 tensor t,
    a tensor b_L,
    a tensor b_R,
    a^2 tensor r,
    t tensor Box.

The skeleton valuation is

    alpha(t)=z^3 Q,
    alpha(b_L)=alpha(b_R)=z^2 Q,
    alpha(r)=z E,
    alpha(Box)=E.

Writing w=phi(t), the exact all-frontier result is

    C_phi(t)=z^3 Q + 2 z^2 v Q
             + z (u^2 P + v^2 Q) + w.

Explanation of the nontrivial term: replacing just one q-forcing module
by its p-forcing alternative conflicts with the unreplaced q module.
Replacing BOTH simultaneously by their p alternatives is consistent.
The shared-port product rejects the mixed p/q choices, while retaining
the jointly valid u^2 P choice. The coefficient 2 records the two
different single-leaf cuts; it is not inferred from a set of summaries.

This is a precise simultaneous-update benefit of all-frontier extraction.
It is a certificate-level example; instantiating it with an actual full
LQ revival pair remains work for the logical adapter.

## 7. Worked antipode cancellation with generic cache values

For the same ordered corolla, put

    x=phi(a), y=phi(r), u_L=phi(b_L), u_R=phi(b_R), v=phi(t).

All quantities may be elements of the partition-constraint ring. Direct
connected-graded recursion gives

    S(a)=-a,
    S(r)=-r,
    S(b_i)=-b_i+a r,
    S(t)=-t+a b_L+a b_R-a^2 r.

Thus

    (phi o S)(t)=-v+x(u_L+u_R)-x^2 y.

For any remainder valuation alpha, let A0=alpha(Box), R=alpha(r),
B_i=alpha(b_i), T=alpha(t). Then

    C_phi(t)=T+x(B_L+B_R)+x^2 R+v A0,
    C_phi(b_i)=B_i+xR+u_i A0,
    C_phi(r)=R+y A0,
    C_phi(Box)=A0.

Inversion at t reads

    alpha(t)=C_phi(t)-x(C_phi(b_L)+C_phi(b_R))
             +x^2 C_phi(r)
             +(-v+x(u_L+u_R)-x^2 y)C_phi(Box).

Substitution cancels every extracted-frontier contribution and leaves T.
This is a genuine boundary-valued antipode calculation: the constraints
remain in A throughout, and the typed Box survives as the module state.

If one specializes to the all-ones character zeta, cancellations can make
the inverse particularly simple. That special case must not be presented
as evidence that all examples need elaborate counterterms. General cache
characters retain the independent u_i,v data used above.

## 8. Scope of the contribution

Established here on paper:

* a typed-open signature-level CK comodule;
* a shared-port constraint algebra;
* an exact all-frontier coordinated replacement enumerator;
* convolution composition, antipode inversion, and cache-rebase theorems;
* a nontrivial interacting replacement example with physical multiplicity.

Still required for the project's intended theorem:

* native carrier comparison and mechanization;
* a complete LQ revival interface (not only connectivity consistency);
* concrete analytic-rule or concurrent-migration instances;
* an account of transport under copying, masking and variable freshness;
* any claim of efficient implementation or complexity improvement.

The specific Hopf contribution is the canonical invertible action of cache
characters and its cancellation/update calculus. One frontier can be
checked by a zipper or constraint solver; the algebra connects all
frontiers and their iterated updates in one law. There is no assertion
that software implementing that law must expose Hopf notation, or that a
framework must be impossible to reformulate combinatorially to be useful.

## 9. Connected sensitivity: a stronger differential consequence

Let phi_s:H -> A[s] be a character whose generator values vary
polynomially in a parameter s. Extend scalars as needed and differentiate
formally. Put

    gamma_s = (d phi_s/ds) * (phi_s o S).

THEOREM. gamma_s is an infinitesimal character:

    gamma_s(1)=0,
    gamma_s(ab)=gamma_s(a)epsilon(b)+epsilon(a)gamma_s(b).

For C_s=U_phi_s alpha one has

    d C_s/ds = U_gamma_s C_s.

PROOF. Differentiate phi_s(ab)=phi_s(a)phi_s(b). Use multiplicativity of
Delta and of phi_s o S (the target is commutative), and regroup the four
factors. The two resulting sums contain respectively
phi_s*(phi_s o S)=epsilon on b and on a. This is the displayed derivation
identity. For the observer equation, differentiate the finite cut sum,
then use U_(dphi_s/ds)=U_gamma_s U_phi_s. QED.

In particular gamma_s vanishes on a forest with two or more positive tree
components. Thus the derivative of an all-simultaneous-frontier observable
has the connected form

    d C_s(t)/ds = sum_(one-subtree cuts c)
                    gamma_s(P_c(t)) C_s(R_c(t)).

The whole-tree cut participates; the empty cut contributes zero. The
coefficient gamma_s of a connected subtree can itself include signed
corrections involving smaller trees. This is not a claim that independent
updates are sufficient: the Hopf logarithmic derivative has already
absorbed the interactions. It gives a canonical sensitivity equation with
one connected extraction at a time.

No integration, exponential series, or division by factorials is used.
This derivative is with respect to cache weights, not McBride's derivative
of a datatype. The link to the context derivative is through *marked
physical cut occurrences*, described next.

## 10. Finite perturbations, marked cuts, and the context connection

Replace the value of a selected cache generator a from x to x+d, keeping
all other generator values fixed. The coefficient of d^k in C_psi(t) is
the sum over cuts with k distinguished selected occurrences of type a,
using d at those occurrences and x at the others. If a forest contains m
equal a-components, there are binomial(m,k) such physical choices.
This follows by expanding each forest product; it is the Hasse derivative
interpretation of the forward CK transform. It is valid over Z and does
not require factorial inverses.

Each distinguished occurrence determines a one-hole context in the
underlying tree datatype. Several distinguished occurrences must be
incomparable to lie on one CK frontier. Thus a higher datatype derivative
allowing arbitrary distinct recursive positions is not automatically the
same structure: the physical cut condition still matters. Composition of
marked layers must use the matching context-substitution theorem before
being called a Faà di Bruno law.

For the ordered corolla of Section 7, let beta=psi*(phi o S). Direct
calculation gives

    beta(a)=d,
    beta(r)=0,
    beta(b_i)=-d y,
    beta(t)=-d(u_L+u_R)-d^2 y,
    beta(a^2)=d^2.

The update theorem becomes

    C_psi(t)=C_phi(t)+d(C_phi(b_L)+C_phi(b_R))
             +d^2 C_phi(r)
             +[-d(u_L+u_R)-d^2 y]C_phi(Box).

Substituting the cumulative values cancels their previously included
whole-module terms and gives exactly

    C_psi(t)-C_phi(t)
       =d(B_L+B_R)+(2xd+d^2)R.

The quadratic term is the simultaneous two-module update. The signed
counterterms prevent previously cached whole remainders from being
counted as new local work. This combines the marked-cut/Hasse viewpoint
with the antipode cache-change law in one checkable example.

## 11. Commutators measure staged extraction interference

Let g,h:H -> A be infinitesimal characters. Their convolution commutator

    [g,h] = g*h-h*g

is again an infinitesimal character, and the induced operators satisfy

    [U_g,U_h] = U_[g,h].

PROOF. For a,b in H, expand g(a_1 b_1)h(a_2 b_2) with the two
infinitesimal-character identities. The terms where both functionals act
on a give (g*h)(a)epsilon(b); those where both act on b give the symmetric
term. The two cross terms are g(a)h(b)+h(a)g(b). The same cross terms
occur with g,h reversed and cancel because A is commutative. Subtracting
gives the infinitesimal identity for the bracket. The operator identity
follows from U_g U_h=U_(g*h), which holds for arbitrary linear g,h.

For a concrete directional witness, let a be a nullary rule tree and b a
unary rule with its input left as a typed hole. Let t=b(a). Let delta_a
and delta_b assign 1 to their respective single-tree generator and zero
to all other generators and to every nontrivial forest product. Then

    (delta_a*delta_b)(t)=1,
    (delta_b*delta_a)(t)=0,
    [delta_a,delta_b](t)=1.

The first sequence extracts the child and then the residual parent
context; the reversed sequence has no corresponding source cut. By
contrast the bracket vanishes on a forest of two disconnected positive
components. With square-zero parameters epsilon,eta, the mixed difference
between (I+epsilon U_g)(I+eta U_h) and the opposite ordering is exactly
epsilon eta U_[g,h]. No analytic convergence or characteristic-zero
division is involved.

This detects interference between staged extraction/valuation operations.
It does NOT establish noncommutation of two actual proof-normalization
passes until each pass has been identified with such an operator. It uses
the given CK algebra and its character action; no change to a
Grossman–Larson substitution carrier is being made.

## 12. Minimum residual checking, with the correct late observation

Assume cache weights and skeleton weights have nonnegative polynomial
coefficients. Define the Z-linear map

    tau_plan([sigma])=1 for each consistent boundary constraint sigma.

It is not a ring homomorphism. Apply it only after the shared-port joins:

    F_T(z,y)=tau_plan(C_phi(T)).

PROPOSITION. The coefficient of a monomial in F_T is the number of
compatible pairs consisting of a physical CK frontier and one concrete
cache-certificate choice per selected occurrence, with exactly that use
multiset and that exposed-rule cost.

PROOF. Expand the finite sum and each cache factor. Each resulting term
has one frontier and one choice at each of its physical roots. Its joined
constraint is either inconsistent, contributing zero, or one consistent
basis state, contributing one under tau_plan. The exponent of z is the
retained rule count by construction. No term has a negative coefficient,
so distinct choices accumulate without cancellation. QED.

These are **plans**, not distinct resulting proofs and not all variable
colourings of a certificate. Two plans may yield the same proof; two
explicit cached certificates with the same summary remain two choices.
Each cache choice must have one deterministic summary. A non-disjoint
symbolic cover of possible certificates cannot be counted this way without
first correcting its overlap.

Set all y variables to 1. The least exponent of z with nonzero coefficient
is exactly the minimum residual number of rule vertices requiring an
exposed check. If original T is certified, the empty frontier guarantees
some plan and gives upper bound |T|. Any nonnegative cost per exposed rule
can replace unit node cost; cache-lookup costs can be added in phi.

For an exterior constraint E, use tau_plan([E]C_phi(T)) before taking the
minimum. The same boundary-valued enumerator therefore answers contextual
minimum-checking queries while preserving shared-owner correlations.
Taking independent minima before joining boundaries can be wrong.

The inverse/cache-change formulas operate in the ring before this late
observation. Intermediate signed expressions are cancellation devices;
one cannot take a minimum, Boolean support, or an assignment count of
those intermediate terms and expect the update theorem to survive.

In particular, unused ports in a fixed U cause no spurious colouring
factor under tau_plan. It counts existence of a compatible assignment,
not the number of assignments to U. Full colouring counts need an
active-port account or local kernels with last-use summation. Summing q
choices for every global U port would overcount owners removed by a
replacement and is not the operation defined here.

There is also a valid *forward-only* minimum-cost semiring interpretation.
Use finitely supported functions from consistent boundary states to
N union {infinity}. Addition is pointwise minimum; multiplication takes
the minimum of f(sigma)+g(tau) over compatible pairs with the specified
joined state. This is a semiring by associativity of constraint joining.
From the nonnegative polynomial subsemiring, send each state coefficient
to its least z exponent after setting choice weights to 1. This map
preserves addition and multiplication because nonnegative terms cannot
cancel. It computes the same optimum without retaining plan counts.
It cannot extend to the entire signed ring: cancellation in an antipode
update must finish before applying this minimum-cost projection.

## 13. A literal LQ instance with an exact 21-to-11 residual cost

The revival workstream supplied the following source-specific fixture.
It uses the LQ ghost calculus's ghost initial, ghost disjunction owner,
and ordinary intuitionistic rules. Its certificate semantics is checked
there separately; the algebra here consumes those explicit certificates.

Fix distinct atoms p,q and the empty-succedent sequent

    S = p, not p, q, not q => .

Let M_p begin at the ghost initial =>p assigned to external RIGHT owner x.
An ordinary not-left rule gives not p=>, satisfying the required
empty-succedent checkpoint, and three unary internal weakenings add
p,q,not q to reach S. M_q is the analogous five-vertex module beginning
at =>q and ending at the same S. Both have the same literal root sequent
and external scope x:right. Their certificates force respectively x=p
and x=q.

Put two modules under an ordinary disjunction-left rule with A=B=p and
Gamma=not p,q,not q, obtaining

    R = not p,q,not q,p or p => .

This is the right premise subtree of the sole ghost disjunction owner x.
For its left premise use an ordinary intuitionistic proof of R: two
four-vertex proofs of S (identity p=>p, not-left, two weakenings), joined
by one ordinary disjunction-left inference. This left proof has nine
vertices and no ghost leaves. The complete source with both right
modules M_q has

    1 outer owner + 9 left proof + 1 right disjunction-left
      + 5 + 5 module vertices = 21 vertices.

Only owner x is available to the two ghost leaves, so mixed M_p/M_q
replacements cannot escape the consistency conflict by choosing another
owner. Both same-colour replacements satisfy the checkpoints and routing.
The concluding sequent is already intuitionistically derivable; the
separation concerns valid certificates of these concrete ghost derivations,
not semantic unprovability of R.

Now install a reusable cache containing only the certified module M_p,
usable at either of the two source M_q roots. Every other positive partial
tree has cache valuation zero. Set the M_p choice weight to u. The only
nonzero native frontier possibilities are the empty cut, either module
root alone, or both module roots. The single-root cases have p/q conflict
and vanish. Hence

    C_phi(T) = z^21 Q + u^2 z^11 P,
    F_T(z,u) = z^21 + u^2 z^11.

The optimal residual check has 11 rule vertices. Testing the two cached
replacements separately would reject both and retain cost 21. The full
simultaneous frontier realizes the 10-vertex saving. The u^2 term records
two physical copied uses of the reusable cached module, not one aliased
proof occurrence. If cache use is capacity-limited, the capacity condition
must be imposed on those exponents explicitly.

This is a concrete D5 application of the full-cut, shared-interface
framework. It is an exact accounting theorem for the stated verifier cost,
not a wall-clock speedup claim or a general LQ cut-elimination theorem.

For a tangible Hopf update, start instead with the q-module cache
phi(M_q)=vQ. Its cumulative value is

    C_phi(T)=z^21 Q+2v z^16 Q+v^2 z^11 Q.

Change to psi(M_q)=uP. The relative character beta=psi*(phi o S) takes
value uP-vQ on M_q and zero on the other connected source generators.
Here the inverse simplifies because the cached generator is a completely
closed slotted module: it cannot be the remainder of a nonempty proper
cut of a larger tree. Applying U_beta to the old cumulative value cancels
its old-cache terms and returns exactly z^21 Q+u^2 z^11 P.

If one forgets partitions *before* this update, the scalar expression
u-v falsely admits single p-module uses and produces spurious terms
2u z^16. Thus the explicit example also tests the claimed late observation
discipline, not merely an ordinary polynomial substitution.

Finally add, rather than replace, the p-cache using

    phi_s(M_q)=vQ+s uP.

Then

    C_s(T)=z^21 Q+2v z^16 Q+v^2 z^11 Q+s^2 u^2 z^11 P.

The first derivative at s=0 is zero, while the second Hasse coefficient
is u^2 z^11 P. A one-hole improvement test misses this cooperative
two-module reuse. The logarithmic sensitivity law sees the derivative
2s u^2 z^11 P through the two connected module cuts; the second-order
marked-frontier term records the simultaneous gain. This connects the
Hopf action and higher-context sensitivity on the same actual LQ fixture.

## 14. Executable evidence

`check_hopf_consequences.py` implements a small independent slotted-tree
model and exact integer polynomial arithmetic, including the constraint
relations P^2=P, Q^2=Q, PQ=0. It checks the corolla identities above and
exhaustively checks all 210 trees and 476 forests through degree four for
the signature a:nullary, b:unary, r:binary, with typed holes represented by
missing input subtrees in this one-output-type test model.

Checks cover full cut-flag coaction, both antipode identities, polynomial
inversion, the logarithmic derivative's infinitesimal identity, the
connected sensitivity equation, Lie closure, the operator commutator,
and the directional two-vertex witness. Universal statements rest on the
paper proofs, not finite agreement. This is neither native POTKIN3 nor
Lean kernel evidence. Source-specific LQ rules/certificates are checked
in the separate revival workstream's fixture.

The script additionally imports that validated 21-vertex fixture,
preserves exact input/output sequents and active scope in node labels,
enumerates **all 963 physical cuts**, and evaluates zero on uncached
positive factors rather than deleting any coproduct terms. Four frontiers
are provider-supported; two survive boundary consistency, with residual
costs 21 and 11. It checks the old-q/new-p antipode cache change and the
vanishing-first/nonzero-second sensitivity calculation over the full cut
sum. These checks validate this fixture, not a general native Lean bridge.
