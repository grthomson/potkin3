import Potkin.Research.OpenCertificateKernel
import Potkin.Research.CutHoleAdapter
import Potkin.CompositeCutExpansion

/-!
# Native scoped certificate restriction and gluing

The interfaces below are physical holes of the native remainder.  The callback
evaluates its exactly aligned native detached factor at the absolute address
and inherited scope supplied by that particular remainder certificate.  In
particular this is not a product of independently closed factor counts.

Completeness is used only for the cut-created-hole adapter.  General open
substitution is handled by the continuation kernel's filling equivalence.
-/

namespace Potkin.Research.CertificateCutGluing

open RevivalInterface OpenCertificateKernel

variable {G : Hypersequent sigma} {tree : CKTree sigma Data G}

/-- The native complete-source remainder, equipped with dependent callbacks.
An interface itself does not advance the checkpoint state. -/
abbrev PieceCertificates (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (address : InternalAddress) (scope : List OwnerSlot) :=
  Kernel cut.remainder
    (fun hole actual inherited =>
      ClosedKernel (cut.detachedLeafAssignment complete hole) actual inherited)
    address scope

/-- The equivalence uses literal native refill followed by constructor-wise
restriction.  Its inverse invokes the same callbacks at the same owner scope.
The whole-branch constructor is allowed here; public `CKCut` excludes the root
but includes the empty cut. -/
def cutGluingEquiv (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (address : InternalAddress) (scope : List OwnerSlot) :
    ClosedKernel tree address scope ≃ PieceCertificates cut complete address scope :=
  (Equiv.cast (congrArg (fun t => ClosedKernel t address scope)
    (cut.fillAssignment_detached complete).symm)).trans
      (fillEquiv cut.remainder (cut.detachedLeafAssignment complete) address scope)

def restrictCertificate (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (address : InternalAddress) (scope : List OwnerSlot) :=
  (cutGluingEquiv cut complete address scope).toFun

def glueCertificate (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (address : InternalAddress) (scope : List OwnerSlot) :=
  (cutGluingEquiv cut complete address scope).invFun

theorem glue_restrict (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (address : InternalAddress) (scope : List OwnerSlot)
    (certificate : ClosedKernel tree address scope) :
    glueCertificate cut complete address scope
      (restrictCertificate cut complete address scope certificate) = certificate :=
  (cutGluingEquiv cut complete address scope).left_inv certificate

theorem restrict_glue (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (address : InternalAddress) (scope : List OwnerSlot)
    (pieces : PieceCertificates cut complete address scope) :
    restrictCertificate cut complete address scope
      (glueCertificate cut complete address scope pieces) = pieces :=
  (cutGluingEquiv cut complete address scope).right_inv pieces

/-- Admitted sources connect the Type-valued bridge to the existing verified
Prop-valued grounding relation.  The relation is existence, not multiplicity. -/
theorem cut_existence_iff (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (admitted : LocallyAdmittedTree presentation tree)
    (address : InternalAddress) (scope : List OwnerSlot) :
    HasScopedCertificate tree address scope ↔
      Nonempty (PieceCertificates cut complete address scope) := by
  rw [← closed_nonempty_iff tree admitted address scope]
  exact (cutGluingEquiv cut complete address scope).nonempty_congr

/-- Exact finite counting of the dependent piece witnesses.  Owner colours
are shared Sigma choices and ordered premises are products inside the kernel;
factor callbacks remain conditioned on that same scope.  This is not an
unconditional product of independently closed detached-factor counts. -/
def piecesCountEquiv (cut : CKBranchCut tree) (complete : tree.IsComplete)
    (admitted : LocallyAdmittedTree presentation tree)
    (address : InternalAddress) (scope : List OwnerSlot) :
    PieceCertificates cut complete address scope ≃
      Fin (certificateCount tree address scope) :=
  (cutGluingEquiv cut complete address scope).symm.trans
    (closedCountEquiv tree admitted address scope)

/-- Root-excluding public cuts, including the empty cut, use native descent. -/
def properCutGluingEquiv (cut : CKCut tree) (complete : tree.IsComplete)
    (address : InternalAddress) (scope : List OwnerSlot) :=
  cutGluingEquiv (.descend cut.plan) complete address scope

/-- Pointwise scoped replacement transports certificates; it does not assert
ordinary LJ derivability, unrestricted logical equivalence or compiler C1. -/
def scopedReplacementEquiv (context : CKTree sigma Data G)
    (left right : context.LeafAssignment)
    (pointwise : ∀ hole actual inherited,
      ClosedKernel (left hole) actual inherited ≃
        ClosedKernel (right hole) actual inherited)
    (address : InternalAddress) (scope : List OwnerSlot) :
    ClosedKernel (context.fillAssignment left) address scope ≃
      ClosedKernel (context.fillAssignment right) address scope :=
  (fillEquiv context left address scope).trans
    ((providerEquiv context (factorClosedProvider context left)
      (factorClosedProvider context right) pointwise address scope).trans
      (fillEquiv context right address scope).symm)

end Potkin.Research.CertificateCutGluing

#check Potkin.Research.CertificateCutGluing.cutGluingEquiv
#check Potkin.Research.CertificateCutGluing.scopedReplacementEquiv
#check Potkin.Research.OpenCertificateKernel.closed_nonempty_iff
#check Potkin.Research.CertificateCutGluing.piecesCountEquiv
#print axioms Potkin.Research.CertificateCutGluing.cutGluingEquiv
#print axioms Potkin.Research.CertificateCutGluing.glue_restrict
#print axioms Potkin.Research.CertificateCutGluing.restrict_glue
#print axioms Potkin.Research.CertificateCutGluing.cut_existence_iff
#print axioms Potkin.Research.CertificateCutGluing.piecesCountEquiv
#print axioms Potkin.Research.CertificateCutGluing.scopedReplacementEquiv
