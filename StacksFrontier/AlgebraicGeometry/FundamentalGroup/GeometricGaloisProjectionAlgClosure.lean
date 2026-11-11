module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricGaloisProjection
public import StacksFrontier.FieldTheory.Galois.SeparableClosureGaloisGroup
public import Mathlib.Algebra.CharP.Reduced

/-!
# The projection `π₁(X, η̄) ⟶ Aut(k̄/k)` over an arbitrary field

Let `k` be any field and `k̄` an algebraic closure of `k`. The restriction
`Aut(k̄/k) ⟶ Gal(k^{sep}/k)` is a bijection (`AlgebraicGeometry.separableClosureRestrictMulEquiv`),
and its inverse is continuous for the Krull topologies even when `k̄` is not separable over `k`:
`k̄` is purely inseparable over `k^{sep}`, so for `x ∈ k̄` some `x ^ (q ^ n)` lies in `k^{sep}`,
and since the iterated Frobenius of `k̄` is injective an automorphism fixes `x` exactly when it
fixes `x ^ (q ^ n)`. So the stabilizer of `x` in `Aut(k̄/k)` pulls back to the stabilizer of an
element of `k^{sep}` in `Gal(k^{sep}/k)`, which is open.

Hence for a geometrically connected smooth curve `X` over `k` the projection
`π₁(X, η̄) ⟶ π₁(X, η̄) ⧸ π₁(X_k̄, η̄) ≃ Aut(k̄/k)` of the fundamental exact sequence of Section 03VJ
is a continuous surjection with kernel the image of `π₁(X_k̄, η̄)`, for every field `k`. Its
underlying homomorphism is the one of `AlgebraicGeometry.geometricGaloisProjection`, which is the
same construction under the extra hypothesis that `k̄` is separable over `k`.

## Main definitions

* `AlgebraicGeometry.geometricGaloisProjectionOfAlgClosure`: `π₁(X, η̄) →ₜ* Aut(k̄/k)`.

## Main results

* `AlgebraicGeometry.continuous_separableClosureRestrictMulEquiv_symm_of_isAlgClosed`.
* `AlgebraicGeometry.surjective_geometricGaloisProjectionOfAlgClosure`.
* `AlgebraicGeometry.ker_geometricGaloisProjectionOfAlgClosure`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Restriction

variable (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosed kbar]
  [Algebra.IsAlgebraic k kbar]

/-- **The inverse of the restriction `Aut(k̄/k) ⟶ Gal(k^{sep}/k)` is continuous**, for any
algebraically closed algebraic extension `k̄` of `k`: an automorphism of `k̄` fixes `x` if and only
if it fixes `x ^ (q ^ n)`, which for large `n` lies in `k^{sep}`. -/
theorem continuous_separableClosureRestrictMulEquiv_symm_of_isAlgClosed :
    Continuous (separableClosureRestrictMulEquiv k kbar).symm := by
  obtain ⟨q, hq⟩ := ExpChar.exists k
  have : ExpChar kbar q := expChar_of_injective_algebraMap (algebraMap k kbar).injective q
  have : ExpChar (separableClosure k kbar) q :=
    expChar_of_injective_algebraMap (algebraMap k (separableClosure k kbar)).injective q
  refine continuous_of_stabilizer_mem_nhds_one (k := k) (E := kbar)
    (separableClosureRestrictMulEquiv k kbar).symm.toMonoidHom fun x ↦ ?_
  obtain ⟨n, s, hs⟩ := IsPurelyInseparable.pow_mem (separableClosure k kbar) q x
  refine Filter.mem_of_superset (stabilizer_mem_nhds_one (k := k) s) fun g hg ↦ ?_
  have hg : g s = s := hg
  change (separableClosureRestrictMulEquiv k kbar).symm g x = x
  have hσ : (separableClosureRestrictMulEquiv k kbar).symm g (algebraMap _ kbar s) =
      algebraMap _ kbar s := by
    have h := separableClosureRestrictMulEquiv_apply_coe k kbar
      ((separableClosureRestrictMulEquiv k kbar).symm g) s
    rw [MulEquiv.apply_symm_apply, hg] at h
    exact h.symm
  apply iterateFrobenius_inj kbar q n
  rw [iterateFrobenius_def, iterateFrobenius_def, ← map_pow, ← hs, hσ]

end Restriction

section Projection

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- **The projection `π₁(X, η̄) ⟶ Aut(k̄/k)`** of the fundamental exact sequence, as a continuous
homomorphism, for an arbitrary field `k` and an algebraic closure `k̄` of `k`: the quotient by the
image of `π₁(X_k̄, η̄)` followed by `AlgebraicGeometry.geometricQuotientGaloisEquiv`. -/
def geometricGaloisProjectionOfAlgClosure :
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
      refine (continuous_separableClosureRestrictMulEquiv_symm_of_isAlgClosed k kbar).comp ?_
      refine ((galoisEquivEtaleFundamentalGroup k (separableClosure k kbar)
        kbar).symm.continuous).comp ?_
      refine (continuous_etaleFundamentalGroupMulEquiv_symm _).comp ?_
      exact map_continuous (etaleFundamentalGroupMap f
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) }

/-- The image of `γ` in `Aut(k̄/k)` is its class in `π₁(X, η̄) ⧸ π₁(X_k̄, η̄) ≃* Aut(k̄/k)`. -/
theorem geometricGaloisProjectionOfAlgClosure_apply
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricGaloisProjectionOfAlgClosure B X f kbar y γ =
      geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) :=
  rfl

/-- `π₁(X, η̄) ⟶ Aut(k̄/k)` is surjective. -/
theorem surjective_geometricGaloisProjectionOfAlgClosure :
    Function.Surjective (geometricGaloisProjectionOfAlgClosure B X f kbar y) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  exact (geometricQuotientGaloisEquiv B X f kbar y).surjective.comp
    (QuotientGroup.mk'_surjective _)

/-- **The kernel of `π₁(X, η̄) ⟶ Aut(k̄/k)` is the image of `π₁(X_k̄, η̄)`.** -/
theorem ker_geometricGaloisProjectionOfAlgClosure :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricGaloisProjectionOfAlgClosure B X f kbar y : _ →* (kbar ≃ₐ[k] kbar)).ker =
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  ext γ
  change geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

/-- Under the extra hypothesis that `k̄` is separable over `k`, the projection is
`AlgebraicGeometry.geometricGaloisProjection`. -/
theorem geometricGaloisProjectionOfAlgClosure_eq [Algebra.IsSeparable k kbar] :
    geometricGaloisProjectionOfAlgClosure B X f kbar y = geometricGaloisProjection B X f kbar y :=
  rfl

end Projection

end AlgebraicGeometry

end
