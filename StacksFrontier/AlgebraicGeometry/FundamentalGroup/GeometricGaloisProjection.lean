module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricQuotientGaloisEquiv
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# The continuous projection `π₁(X, η̄) ⟶ Aut(k̄/k)`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraically closed
algebraic extension of `k` which is separable over `k` (for instance an algebraic closure of a
perfect field, such as a finite field), and `η̄` a geometric point of `X_k̄`. The base identifies
`π₁(X, η̄) ⧸ π₁(X_k̄, η̄) ≃* Aut(k̄/k)` (`AlgebraicGeometry.geometricQuotientGaloisEquiv`,
Tags 0BTX and 0BNE). This file proves that the resulting projection

`π₁(X, η̄) ⟶ Aut(k̄/k)`

is continuous for the Krull topology on `Aut(k̄/k)`, so that the third map of the fundamental
exact sequence `1 → π₁(X_k̄, η̄) → π₁(X, η̄) → Gal(k^{sep}/k) → 1` of Section 03VJ is a
continuous surjection of profinite groups with kernel the image of `π₁(X_k̄, η̄)`.

Continuity is that of each factor: the map `π₁(X) ⟶ π₁(Spec k)` of fundamental groups, the
transport along an isomorphism of fibre functors, the inverse of the homeomorphism
`Gal(k^{sep}/k) ≅ π₁(Spec k)` of Tag 0BNE, and the inverse of the restriction
`Aut(k̄/k) ⟶ Gal(k^{sep}/k)`, a continuous bijection from a compact group (`k̄/k` is Galois) to a
Hausdorff one.

## Main definitions

* `AlgebraicGeometry.geometricGaloisProjection`: the continuous homomorphism
  `π₁(X, η̄) →ₜ* Aut(k̄/k)`.

## Main results

* `AlgebraicGeometry.surjective_geometricGaloisProjection`.
* `AlgebraicGeometry.ker_geometricGaloisProjection`: the kernel is the image of `π₁(X_k̄, η̄)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Restriction

variable (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosed kbar]
  [Algebra.IsAlgebraic k kbar]

/-- The restriction `Aut(k̄/k) ⟶ Gal(k^{sep}/k)` is continuous. -/
theorem continuous_separableClosureRestrictMulEquiv :
    Continuous (separableClosureRestrictMulEquiv k kbar) := by
  have : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  exact InfiniteGalois.restrictNormalHom_continuous (separableClosure k kbar)

/-- For `k̄` separable over `k`, the inverse of the restriction `Aut(k̄/k) ⟶ Gal(k^{sep}/k)` is
continuous: `Aut(k̄/k)` is compact, `k̄/k` being Galois, and `Gal(k^{sep}/k)` is Hausdorff. -/
theorem continuous_separableClosureRestrictMulEquiv_symm [Algebra.IsSeparable k kbar] :
    Continuous (separableClosureRestrictMulEquiv k kbar).symm := by
  have : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  have : IsGalois k kbar := { to_isSeparable := inferInstance, to_normal := inferInstance }
  exact (continuous_separableClosureRestrictMulEquiv k kbar).continuous_symm_of_equiv_compact_to_t2
    (f := (separableClosureRestrictMulEquiv k kbar).toEquiv)

end Restriction

/-- The inverse of the transport of étale fundamental groups along an isomorphism of fibre
functors is continuous: the fundamental groups are compact and Hausdorff. -/
theorem continuous_etaleFundamentalGroupMulEquiv_symm {S : Scheme.{u}} [ConnectedSpace S]
    {x x' : GeometricPoint S} (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    Continuous (etaleFundamentalGroupMulEquiv t).symm := by
  have := compactSpace_etaleFundamentalGroup S x
  have := t2Space_etaleFundamentalGroup S x'
  exact (continuous_etaleFundamentalGroupMulEquiv t).continuous_symm_of_equiv_compact_to_t2
    (f := (etaleFundamentalGroupMulEquiv t).toEquiv)

section Projection

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- **The projection `π₁(X, η̄) ⟶ Aut(k̄/k)`** of the fundamental exact sequence, as a continuous
homomorphism: the quotient by the image of `π₁(X_k̄, η̄)` followed by
`AlgebraicGeometry.geometricQuotientGaloisEquiv`. -/
def geometricGaloisProjection :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) →ₜ* (kbar ≃ₐ[k] kbar) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  { toMonoidHom := (geometricQuotientGaloisEquiv B X f kbar y).toMonoidHom.comp
      (QuotientGroup.mk' _)
    continuous_toFun := by
      change Continuous fun γ ↦ geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)
      simp only [geometricQuotientGaloisEquiv, MulEquiv.trans_apply]
      refine (continuous_separableClosureRestrictMulEquiv_symm k kbar).comp ?_
      refine ((galoisEquivEtaleFundamentalGroup k (separableClosure k kbar)
        kbar).symm.continuous).comp ?_
      refine (continuous_etaleFundamentalGroupMulEquiv_symm _).comp ?_
      exact map_continuous (etaleFundamentalGroupMap f
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) }

omit [Smooth f] in
/-- `π₁(X, η̄) ⟶ Aut(k̄/k)` is surjective. -/
theorem surjective_geometricGaloisProjection :
    Function.Surjective (geometricGaloisProjection B X f kbar y) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  exact (geometricQuotientGaloisEquiv B X f kbar y).surjective.comp
    (QuotientGroup.mk'_surjective _)

omit [Smooth f] in
/-- **The kernel of `π₁(X, η̄) ⟶ Aut(k̄/k)` is the image of `π₁(X_k̄, η̄)`.** -/
theorem ker_geometricGaloisProjection :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGaloisProjection B X f kbar y : _ →* (kbar ≃ₐ[k] kbar)).ker =
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  ext γ
  change geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

omit [Smooth f] in
/-- The image of `γ` in `Aut(k̄/k)` is its class in `π₁(X, η̄) ⧸ π₁(X_k̄, η̄) ≃* Aut(k̄/k)`. -/
theorem geometricGaloisProjection_apply
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricGaloisProjection B X f kbar y γ =
      geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) :=
  rfl

end Projection

end AlgebraicGeometry

end
