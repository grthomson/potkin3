# Flat cache updates and the role of connected corrections

12 October 2026. Paper derivation for the boundary-valued CK cache framework.
This is a standard character-group identity instantiated to this programme,
not a claim to have discovered the Maurer–Cartan equation. No Lean claim.

Let H be the connected typed positive-tree Hopf algebra, A the commutative
boundary-constraint coefficient ring, M its typed remainder comodule, and
U_f the linear convolution action on A-valued remainder observations. Keep
the typed empty remainder as a state. Work with polynomial parameters
s_1,...,s_r and a character phi_s:H→A[s_1,...,s_r]. All evaluations on a fixed
finite proof tree are finite. Formal differentiation requires no division.

Define the right logarithmic derivatives

    gamma_i = (partial_i phi) * phi^{-1},   phi^{-1}=phi o S.

Each gamma_i is infinitesimal. Therefore its action is a sum over cuts having
one positive detached component, with the whole-root cut included. The
coefficient on that component may contain signed corrections from smaller
trees. It is not obtained by merely ignoring simultaneous cuts.

## Exact finite rebasing is a groupoid action

For three cache characters phi,psi,chi, set beta_(psi,phi)=psi*phi^{-1}.
Then

    beta_(chi,psi) * beta_(psi,phi) = beta_(chi,phi),
    beta_(phi,phi)=epsilon,
    beta_(psi,phi)^{-1}=beta_(phi,psi).

Proof: associativity and cancellation of psi^{-1}*psi. Applying U proves
that coherent rebasing through an intermediate cache gives the same result
as direct rebasing. Required cumulative values on partial remainders must be
retained. This is not an assertion that arbitrary changes to actual proof
syntax commute, and not a complexity claim.

## Infinitesimal flatness

Differentiate phi*phi^{-1}=epsilon to obtain

    partial_i(phi^{-1}) = -phi^{-1}*(partial_i phi)*phi^{-1}.

Consequently

    partial_i gamma_j
      = (partial_i partial_j phi)*phi^{-1} - gamma_j*gamma_i,

and hence

    partial_i gamma_j - partial_j gamma_i = [gamma_i,gamma_j].

Mixed formal partial derivatives commute even over an arbitrary commutative
ground ring. Define nabla_i=partial_i-U_(gamma_i). Since U preserves the
convolution product and therefore the commutator,

    [nabla_i,nabla_j]=0.

For C_s=U_(phi_s) alpha, the exact equation is nabla_i C_s=0. This supplies a
consistency criterion for a proposed family of incremental cache-update
operators: omitting the connected correction terms can leave nonzero
curvature or an incorrect cumulative observable. It does not establish
that the same operators describe normalization steps of a process calculus.

## A two-node calculation exposing the otherwise hidden correction

Let a be a nullary positive tree, b a positive unary root with its input left
as a typed hole, and t=b[a] the filled two-node tree. Their nontrivial cut is
a tensor b. Keep their compatible output types and the root typed Box fixed.
Choose independent cache generator values

    phi(a)=s,  phi(b)=tpar,  phi(t)=v,

where v is constant with respect to s,tpar. Assign arbitrary remainder values
alpha(t)=T, alpha(b)=B, alpha(Box)=E. Then

    C(t)=T+sB+vE,
    C(b)=B+tpar E,
    C(Box)=E.

There is no tpar term in C(t): the partial root b is not itself a whole
subtree of the original two-node proof. It appears as a remainder after the
a extraction. In contrast C(b) legitimately uses its own whole-root cache.

Direct convolution gives

    gamma_s(a)=1, gamma_s(b)=0, gamma_s(t)=-tpar;
    gamma_tpar(a)=0, gamma_tpar(b)=1, gamma_tpar(t)=0.

Thus the connected sensitivity equation at the original source is

    partial_s C(t) = C(b)-tpar C(Box) = B.

The subtraction removes the partial-root cache already present in the
cumulative remainder value. The naive one-subtree update C(b), without the
antipode correction, would incorrectly add tpar E. The bracket satisfies
[gamma_s,gamma_tpar](t)=1, while
partial_s gamma_tpar(t)-partial_tpar gamma_s(t)=1, so the correction is also
exactly what makes the two-parameter connection flat.

This small example explains a practical algebraic role for the antipode:
reuse of cumulative remainder data needs systematic cancellation of work
already represented at a different decomposition layer. The richer LQ
example additionally has shared-owner incompatibility, physical multiplicity,
and a cooperative second-order update; all those coefficients can be retained
through the same calculation.
