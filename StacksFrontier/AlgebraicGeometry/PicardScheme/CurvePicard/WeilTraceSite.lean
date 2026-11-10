/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.PolarizationTrace
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# Weil's trace formula on a big fppf site: genus zero and the `ℓ`-adic form

For a smooth projective curve `X` over an algebraically closed field `k` with a rational point,
in the language of the big fppf site:

* `Stacks.PicardFunctor.abelianVarietyDimension_jacobian`: `dim J = g`;
* `Stacks.PicardFunctor.fixedPointIntersection_eq_of_dimension_eq_zero`: if `g = 0`, then
  `V(φ) = 1 + deg φ` and `Tr(φ^* | J) = 0`;
* `Stacks.PicardFunctor.fixedPointIntersection_eq_of_abelianVarietyTrace`: the identity
  `Tr(φ^* | J) = 1 + deg φ - V(φ)` in `ℚ` gives the `ℓ`-adic form of [Stacks, Tag 03U1],
  `V(φ) = 1 - Tr(φ^* | T_ℓ J) + deg φ` in `ℤ_ℓ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open CartesianMonoidalCategory Stacks.CurvePower
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k]

attribute [local instance] isAbelianVariety_jacobian

/-- **The Jacobian of a curve of genus `g` has dimension `g`.** -/
theorem abelianVarietyDimension_jacobian :
    Stacks.Groupoids.abelianVarietyDimension (jacobianGrp B hX hk f σ hσ).X =
      genus (B.inclusion.map f) := by
  set A := (jacobianGrp B hX hk f σ hσ).X
  have : SmoothOfRelativeDimension (genus (B.inclusion.map f)) A.hom :=
    smoothOfRelativeDimension_picardSchemeDegreeComponent B hX hk f σ hσ 0
  have : Nonempty A.left := ⟨(η[A]).left (IsLocalRing.closedPoint k)⟩
  have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
    (genus (B.inclusion.map f)) A.hom
  have h2 := Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension A
  rw [h1] at h2
  exact_mod_cast h2.symm

variable (φ : X ⟶ X) (w : φ ≫ B.inclusion.map f = B.inclusion.map f)

omit [IsAlgClosed k] in
/-- The trace of an endomorphism of a zero-dimensional abelian variety is zero. -/
theorem abelianVarietyTrace_eq_zero_of_dimension_eq_zero {A : Over (Spec (.of k))} [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (h : Stacks.Groupoids.abelianVarietyDimension A = 0)
    (α : A ⟶ A) [IsMonHom α] : Stacks.Groupoids.abelianVarietyTrace A α = 0 := by
  have hd := Stacks.Groupoids.natDegree_endCharPoly A α
  rw [h, mul_zero] at hd
  rw [Stacks.Groupoids.abelianVarietyTrace, Polynomial.nextCoeff, ite_eq_left hd, neg_zero]

/-- **Weil's formula in genus zero**: `V(φ) = 1 + deg φ`, since `J` is a point. -/
theorem fixedPointIntersection_eq_of_dimension_eq_zero
    (h : Stacks.Groupoids.abelianVarietyDimension (jacobianGrp B hX hk f σ hσ).X = 0) :
    CurveGraph.fixedPointIntersection (B.inclusion.map f)
        (topologicalKrullDim_left_le_one (curveOver B hX hk f)) φ w =
      1 + (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ) := by
  set J := (jacobianGrp B hX hk f σ hσ).X
  have : IsIso J.hom := Stacks.Groupoids.isIso_hom_of_topologicalKrullDim_eq_zero J (by
    rw [Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension J, h]
    rfl)
  have hJ : ∀ {T : Over (Spec (.of k))} (a b : T ⟶ J), a = b := fun a b => by
    apply Over.OverMorphism.ext
    rw [← cancel_mono J.hom, Over.w a, Over.w b]
  have h0 := eq_pullSndP_sub_of_classifyingMap B hX hk f σ hσ φ w
    (hasDegreeZero_zero B hX hk f σ hσ _) (hJ _ _) (map_zero _)
  have hd := curveDeg_diagRestrict_of_eq B hX hk f σ hσ φ w h0
  rw [map_zero] at hd
  have hz : curveDeg (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f) 0 = 0 :=
    (curveDegHom (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f)).map_zero
  rw [hz] at hd
  linarith

/-- **The `ℓ`-adic form**: the identity `Tr(φ^* | J) = 1 + deg φ - V(φ)` in `ℚ` gives
`V(φ) = 1 - Tr(φ^* | T_ℓ Pic⁰) + deg φ` in `ℤ_ℓ` for every prime `ℓ` invertible in `k`. -/
theorem fixedPointIntersection_eq_of_abelianVarietyTrace
    (hdim : topologicalKrullDim X ≤ 1)
    (htr : Stacks.Groupoids.abelianVarietyTrace (jacobianGrp B hX hk f σ hσ).X
        (jacobianPullback B hX hk f φ w σ hσ) =
      ((1 + (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ) -
        CurveGraph.fixedPointIntersection (B.inclusion.map f) hdim φ w : ℤ) : ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    ((CurveGraph.fixedPointIntersection (B.inclusion.map f) hdim φ w : ℤ) : ℤ_[ℓ]) =
      1 - CurveGraph.jacobianTateTrace (B.inclusion.map f) hdim φ w ℓ +
        (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ_[ℓ]) := by
  have h1 := Stacks.Groupoids.trace_tateModuleMap_eq_abelianVarietyTrace
    (jacobianGrp B hX hk f σ hσ).X ℓ (jacobianPullback B hX hk f φ w σ hσ) hℓ
  have h2 := trace_tateModuleMap_jacobianPullback B hX hk f φ w σ hσ hdim ℓ
  rw [h2, htr] at h1
  have h3 : CurveGraph.jacobianTateTrace (B.inclusion.map f) hdim φ w ℓ =
      ((1 + (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ) -
        CurveGraph.fixedPointIntersection (B.inclusion.map f) hdim φ w : ℤ) : ℤ_[ℓ]) := by
    apply Subtype.ext
    rw [h1, PadicInt.coe_intCast, Rat.cast_intCast]
  rw [h3]
  push_cast
  ring

/-! ### The polarization condition at rational points -/

variable {L : SheafOfModules.{u}
    (structureSheafRing (jacobianGrp B hX hk f σ hσ).X.left.toRingedSpace)}
  {hL : Stacks.SheafOfModules.IsInvertible (jacobianGrp B hX hk f σ hσ).X.left.presheaf
    (jacobianGrp B hX hk f σ hσ).X.left.ringCatIsSheaf L}

/-- **The polarization condition can be checked at rational points.** If for every `k`-point `y`
of `J` the fibre of `Λ_L` at `y`, the class `aj^*(t_y^* L) - aj^* L` on `X`, has degree zero and
classifying map `-y`, then `Λ_L` has degree-zero fibres and classifying map `-𝟙_J`. -/
theorem exists_classifyingMap_polarizationClass_eq_of_points
    (hpt : ∀ y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X,
      ∃ h : HasDegreeZero B hX hk f σ hσ (powerObj B hX hk f 0)
          (picardMap B hX hk f (powerHomJac B hX hk f σ hσ y)
            (polarizationClass B hX hk f σ hσ L hL)),
        classifyingMap B hX hk f σ hσ _ _ h = y⁻¹) :
    ∃ hΛ : HasDegreeZero B hX hk f σ hσ _ (polarizationClass B hX hk f σ hσ L hL),
      classifyingMap B hX hk f σ hσ _ _ hΛ = (𝟙 (jacobianGrp B hX hk f σ hσ).X)⁻¹ := by
  have hΛ : HasDegreeZero B hX hk f σ hσ _ (polarizationClass B hX hk f σ hσ L hL) := by
    have := isSeparated_of_isCurve B hX hk f
    have := isNoetherian_of_isCurve B hX hk f
    obtain ⟨U, hU, hUaff⟩ := Stacks.TwoAffineCech.exists_cover_isAffineOpen X
      (topologicalKrullDim_le_one_of_isCurve B hX hk f)
    have hlc := isLocallyConstant_fibreDegree B hX hk f σ hσ
      (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) U hU hUaff
      (picardSchemeDegreeComponent B hX hk f σ hσ 0)
      (toPicardFunctorHom B hX hk f _ (polarizationClass B hX hk f σ hσ L hL))
    obtain ⟨-, -, hirr⟩ := universallyClosed_picardSchemeDegreeComponent_zero B hX hk f σ hσ
    have : PreconnectedSpace ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
        (picardSchemeDegreeComponent B hX hk f σ hσ 0)) :=
      ⟨(@IrreducibleSpace.isIrreducible_univ _ _ hirr).2.isPreconnected⟩
    obtain ⟨h1, -⟩ := hpt 1
    intro t
    have hpt0 := h1 (IsLocalRing.closedPoint k)
    change fibreDegree B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) _
      (toPicardFunctorHom B hX hk f _ (picardMap B hX hk f (powerHomJac B hX hk f σ hσ 1)
        (polarizationClass B hX hk f σ hσ L hL))) _ = 0
      at hpt0
    rw [toPicardFunctorHom_apply, toPicardFunctor_app_naturality] at hpt0
    have h0 := (fibreDegree_map B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
      (powerHomJac B hX hk f σ hσ (m := 0) 1) _ (IsLocalRing.closedPoint k)).symm.trans hpt0
    change fibreDegree B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) _
      (toPicardFunctorHom B hX hk f _ (polarizationClass B hX hk f σ hσ L hL)) t = 0
    rw [hlc.apply_eq_of_preconnectedSpace t (B.inclusion.map
      (powerHomJac B hX hk f σ hσ (m := 0) 1).left (IsLocalRing.closedPoint k))]
    exact h0
  refine ⟨hΛ, ?_⟩
  have hV : IsVariety k (jacobianGrp B hX hk f σ hσ).X.hom :=
    (isAbelianVariety_jacobian B hX hk f σ hσ).toIsProperVariety.toIsVariety
  have : IsIntegral (jacobianGrp B hX hk f σ hσ).X.left := hV.toIsIntegral
  have : IsReduced (jacobianGrp B hX hk f σ hσ).X.left := inferInstance
  have : LocallyOfFiniteType (jacobianGrp B hX hk f σ hσ).X.hom := hV.toLocallyOfFiniteType
  have : IsSeparated (jacobianGrp B hX hk f σ hσ).X.hom := hV.toIsSeparated
  refine Stacks.Varieties.overHom_ext_of_points (X := (jacobianGrp B hX hk f σ hσ).X)
    (Y := (jacobianGrp B hX hk f σ hσ).X) _ _ fun p => ?_
  obtain ⟨h, hc⟩ := hpt p
  have e := classifyingMap_comp B hX hk f σ hσ (powerHomJac B hX hk f σ hσ (m := 0) p)
    (polarizationClass B hX hk f σ hσ L hL) hΛ
  replace e := (congrArg (· ≫ classifyingMap B hX hk f σ hσ _ _ hΛ)
    (post_map_powerHomJac B hX hk f σ hσ (m := 0) p)).symm.trans e
  have hp : p⁻¹ = p ≫ (𝟙 (jacobianGrp B hX hk f σ hσ).X)⁻¹ := by
    rw [GrpObj.comp_inv, Category.comp_id]
  exact e.trans (hc.trans hp)

/-- **Weil's formula, `ℓ`-adically, in genus zero.** -/
theorem fixedPointIntersection_eq_of_dimension_eq_zero_padic (hdim : topologicalKrullDim X ≤ 1)
    (h : Stacks.Groupoids.abelianVarietyDimension (jacobianGrp B hX hk f σ hσ).X = 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    ((CurveGraph.fixedPointIntersection (B.inclusion.map f) hdim φ w : ℤ) : ℤ_[ℓ]) =
      1 - CurveGraph.jacobianTateTrace (B.inclusion.map f) hdim φ w ℓ +
        (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ_[ℓ]) := by
  refine fixedPointIntersection_eq_of_abelianVarietyTrace B hX hk f σ hσ φ w hdim ?_ ℓ hℓ
  rw [abelianVarietyTrace_eq_zero_of_dimension_eq_zero h]
  have hV := fixedPointIntersection_eq_of_dimension_eq_zero B hX hk f σ hσ φ w h
  change _ = (((1 + (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ) -
    CurveGraph.fixedPointIntersection (B.inclusion.map f)
      (topologicalKrullDim_left_le_one (curveOver B hX hk f)) φ w : ℤ)) : ℚ)
  rw [hV, sub_self, Int.cast_zero]

/-- **Weil's formula, `ℓ`-adically, from a polarization given at rational points**: if `L` on
`J` has `aj^*(t_y^* L) - aj^* L = -y` for every `k`-point `y` and `deg aj^* L = dim J > 0`, then
`V(φ) = 1 - Tr(φ^* | T_ℓ) + deg φ`. -/
theorem fixedPointIntersection_eq_of_points (hdim : topologicalKrullDim X ≤ 1)
    (hg : 0 < Stacks.Groupoids.abelianVarietyDimension (jacobianGrp B hX hk f σ hσ).X)
    (hpt : ∀ y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X,
      ∃ h : HasDegreeZero B hX hk f σ hσ (powerObj B hX hk f 0)
          (picardMap B hX hk f (powerHomJac B hX hk f σ hσ y)
            (polarizationClass B hX hk f σ hσ L hL)),
        classifyingMap B hX hk f σ hσ _ _ h = y⁻¹)
    (hq : curveDeg (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f)
        (classQ (jacobianGrp B hX hk f σ hσ).X L hL
          (Additive.ofMul (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ))) =
      Stacks.Groupoids.abelianVarietyDimension (jacobianGrp B hX hk f σ hσ).X)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    ((CurveGraph.fixedPointIntersection (B.inclusion.map f) hdim φ w : ℤ) : ℤ_[ℓ]) =
      1 - CurveGraph.jacobianTateTrace (B.inclusion.map f) hdim φ w ℓ +
        (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ_[ℓ]) := by
  obtain ⟨hΛ, hcl⟩ := exists_classifyingMap_polarizationClass_eq_of_points B hX hk f σ hσ hpt
  exact fixedPointIntersection_eq_of_abelianVarietyTrace B hX hk f σ hσ φ w hdim
    (abelianVarietyTrace_jacobianPullback B hX hk f σ hσ φ w hΛ hcl hg hq) ℓ hℓ

end Stacks.PicardFunctor

end
