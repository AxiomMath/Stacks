/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.WeilTraceSite

/-!
# A criterion for the polarization condition

Let `L` be an invertible module on the Jacobian `J` of a curve `X` with base point `c₀`, and for a
`k`-point `y` of `J` let `ψ(y) = aj^*(t_y^* L) - aj^* L` on `X`. By the theorem of the cube `ψ` is
a homomorphism `J(k) ⟶ Pic(X)`.

Suppose `S ⊆ J(k)` satisfies `S - S = J(k)` and, for `x ∈ S`, `(aj - x)^* L = z_x + g[c₀]` with
`z_x` a degree-zero class whose classifying map is `x`. Then `ψ(y)` has classifying map `-y` for
every `y`, and `aj^* L = g[c₀]` (`Stacks.PicardFunctor.polarization_of_translates`). These are
the hypotheses of `Stacks.PicardFunctor.fixedPointIntersection_eq_of_points`. For the theta
divisor, `S` is the set of points `x` with `x + g[c₀]` normalized, and `z_x + g[c₀] = [D_x]`.
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

/-- A `k`-point of `J` as a constant morphism `C^1 = C ⊗ C^0 ⟶ J`. -/
abbrev pointConst (y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    Additive
      (curveOver B hX hk f ⊗ power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :=
  Additive.ofMul (snd (curveOver B hX hk f) (power (curveOver B hX hk f) 0) ≫ y)

/-- The Abel–Jacobi map on `C^1 = C ⊗ C^0`. -/
abbrev ajOne :
    Additive
      (curveOver B hX hk f ⊗ power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :=
  Additive.ofMul (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0) ≫
    abelJacobi B hX hk f σ hσ)

/-- The class of the base point on `C^1`, as a point of the Picard functor over `C^0`. -/
abbrev pointP : picardAt B hX hk f (powerObj B hX hk f 0) :=
  pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ)

omit [IsAlgClosed k] in
/-- `pointConst` sends the product of two `k`-points of `J` to the sum of their constant maps. -/
theorem pointConst_mul (y₁ y₂ : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    pointConst B hX hk f σ hσ (y₁ * y₂) =
      pointConst B hX hk f σ hσ y₁ + pointConst B hX hk f σ hσ y₂ := by
  show Additive.ofMul (snd _ _ ≫ (y₁ * y₂)) = _
  rw [MonObj.comp_mul]
  rfl

variable {L : SheafOfModules.{u}
    (structureSheafRing (jacobianGrp B hX hk f σ hσ).X.left.toRingedSpace)}
  {hL : Stacks.SheafOfModules.IsInvertible (jacobianGrp B hX hk f σ hσ).X.left.presheaf
    (jacobianGrp B hX hk f σ hσ).X.left.ringCatIsSheaf L}

/-- The pullback of `L` along a constant map `C^1 ⟶ J` is trivial. -/
theorem classQ_pointConst (y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    classQ (jacobianGrp B hX hk f σ hσ).X L hL (pointConst B hX hk f σ hσ y) = 0 := by
  have h := schemePullbackClass_classQ (jacobianGrp B hX hk f σ hσ).X L hL
    (snd (curveOver B hX hk f) (power (curveOver B hX hk f) 0)) (Additive.ofMul y)
  rw [precompHom_apply, toMul_ofMul] at h
  refine h.symm.trans ?_
  rw [Subsingleton.elim (classQ (jacobianGrp B hX hk f σ hσ).X L hL (Additive.ofMul y)) 0,
    Stacks.PicardFunctor.schemePullbackClass_zero]

variable (L hL) in
/-- `ψ(y) = aj^*(t_y^* L) - aj^* L` on `C^1`. -/
abbrev translateClass (y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    picardAt B hX hk f (powerObj B hX hk f 0) :=
  classQ (jacobianGrp B hX hk f σ hσ).X L hL
      (ajOne B hX hk f σ hσ + pointConst B hX hk f σ hσ y) -
    classQ (jacobianGrp B hX hk f σ hσ).X L hL (ajOne B hX hk f σ hσ)

variable (L hL) in
/-- `aj^* L` on `C^1`, as a point of the Picard functor over `C^0`. -/
abbrev ajQ : picardAt B hX hk f (powerObj B hX hk f 0) :=
  classQ (jacobianGrp B hX hk f σ hσ).X L hL (ajOne B hX hk f σ hσ)

/-- The fibre of the polarization class at a `k`-point `y` is `ψ(y)`. -/
theorem picardMap_polarizationClass_point
    (y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) y)
        (polarizationClass B hX hk f σ hσ L hL) =
      translateClass B hX hk f σ hσ L hL y := by
  rw [picardMap_polarizationClass, post_map_powerHomJac]
  exact (congrArg (fun q => classQ (jacobianGrp B hX hk f σ hσ).X L hL
      (ajOne B hX hk f σ hσ + pointConst B hX hk f σ hσ y) -
        classQ (jacobianGrp B hX hk f σ hσ).X L hL (ajOne B hX hk f σ hσ) - q)
    (classQ_pointConst B hX hk f σ hσ y)).trans (sub_zero _)

/-- `ψ` is a homomorphism: `ψ(y₁ y₂) = ψ(y₁) + ψ(y₂)`. -/
theorem translateClass_mul
    (y₁ y₂ : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    translateClass B hX hk f σ hσ L hL (y₁ * y₂) =
      translateClass B hX hk f σ hσ L hL y₁ + translateClass B hX hk f σ hσ L hL y₂ := by
  have hc := classQ_cube (jacobianGrp B hX hk f σ hσ).X L hL (ajOne B hX hk f σ hσ)
    (pointConst B hX hk f σ hσ y₁) (pointConst B hX hk f σ hσ y₂)
  rw [classQ_pointConst, classQ_pointConst, ← pointConst_mul, classQ_pointConst, add_zero,
    add_zero, add_zero] at hc
  rw [translateClass, translateClass, translateClass, pointConst_mul, ← add_assoc,
    eq_sub_of_add_eq hc]
  abel

omit [IsAlgClosed k] in
/-- Classes on `C^1 = X ×_k Spec k` are determined by their classifying maps. -/
theorem eq_of_classifyingMap_eq_powerObj_zero {z z' : picardAt B hX hk f (powerObj B hX hk f 0)}
    (hz : HasDegreeZero B hX hk f σ hσ _ z) (hz' : HasDegreeZero B hX hk f σ hσ _ z')
    (h : classifyingMap B hX hk f σ hσ _ z hz = classifyingMap B hX hk f σ hσ _ z' hz') :
    z = z' := by
  obtain ⟨N, hN⟩ := (classifyingMap_eq_classifyingMap_iff B hX hk f σ hσ _ hz hz').1 h
  have hN0 : N = 0 := Subsingleton.elim (α := PowerPic (curveOver B hX hk f) 0) N 0
  rw [hN0] at hN
  rw [Stacks.PicardFunctor.schemePullbackClass_zero] at hN
  exact (sub_eq_zero.1 hN.symm)

omit [IsAlgClosed k] in
/-- The classifying maps of equal degree-zero classes agree. -/
theorem classifyingMap_congr {T : BigFppfOver B (Spec (.of k)) hk} {z z' : picardAt B hX hk f T}
    (e : z = z') (hz : HasDegreeZero B hX hk f σ hσ T z) :
    classifyingMap B hX hk f σ hσ T z hz =
      classifyingMap B hX hk f σ hσ T z' (e ▸ hz) := by
  subst e
  rfl

/-- **The criterion.** Let `S` be a set of `k`-points of `J` with `S - S = J(k)` such that for
`x ∈ S`, `(aj - x)^* L = z_x + g[c₀]` with `z_x` of degree zero and classifying map `x`. Then every
fibre `ψ(y)` of the polarization class has classifying map `-y`, and `aj^* L = g[c₀]`. -/
theorem polarization_of_translates (g : ℤ)
    (S : Set (power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X))
    (hS : ∀ y, ∃ x ∈ S, ∃ x' ∈ S, y = x' * x⁻¹)
    (hT : ∀ x ∈ S, ∃ (z : picardAt B hX hk f (powerObj B hX hk f 0))
      (hz : HasDegreeZero B hX hk f σ hσ _ z), classifyingMap B hX hk f σ hσ _ z hz = x ∧
        classQ (jacobianGrp B hX hk f σ hσ).X L hL
            (ajOne B hX hk f σ hσ + pointConst B hX hk f σ hσ x⁻¹) =
          z + g • pointP B hX hk f σ hσ) :
    (∀ y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X,
      ∃ h : HasDegreeZero B hX hk f σ hσ (powerObj B hX hk f 0)
          (picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) y)
            (polarizationClass B hX hk f σ hσ L hL)),
        classifyingMap B hX hk f σ hσ _ _ h = y⁻¹) ∧
      ajQ B hX hk f σ hσ L hL = g • pointP B hX hk f σ hσ := by
  choose z hz hzc hzQ using hT
  have hψ : ∀ x (hx : x ∈ S), translateClass B hX hk f σ hσ L hL x⁻¹ =
      z x hx + g • pointP B hX hk f σ hσ - ajQ B hX hk f σ hσ L hL := by
    intro x hx
    exact congrArg (fun q : picardAt B hX hk f (powerObj B hX hk f 0) =>
      q - ajQ B hX hk f σ hσ L hL) (hzQ x hx)
  have hdiff : ∀ x (hx : x ∈ S) x' (hx' : x' ∈ S),
      translateClass B hX hk f σ hσ L hL (x' * x⁻¹) = z x hx - z x' hx' := by
    intro x hx x' hx'
    have h1 := translateClass_mul B hX hk f σ hσ (L := L) (hL := hL) x'⁻¹ x'
    rw [inv_mul_cancel] at h1
    have h0 : translateClass B hX hk f σ hσ L hL 1 = 0 := by
      have := translateClass_mul B hX hk f σ hσ (L := L) (hL := hL) 1 1
      rw [mul_one] at this
      exact add_left_cancel (this.symm.trans (add_zero _).symm)
    rw [h0] at h1
    rw [translateClass_mul, hψ x hx]
    have h2 : translateClass B hX hk f σ hσ L hL x' =
        -translateClass B hX hk f σ hσ L hL x'⁻¹ := eq_neg_of_add_eq_zero_right h1.symm
    rw [h2, hψ x' hx']
    abel
  have hpt : ∀ y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X,
      ∃ h : HasDegreeZero B hX hk f σ hσ (powerObj B hX hk f 0)
          (picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) y)
            (polarizationClass B hX hk f σ hσ L hL)),
        classifyingMap B hX hk f σ hσ _ _ h = y⁻¹ := by
    intro y
    obtain ⟨x, hx, x', hx', rfl⟩ := hS y
    have e : picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) (x' * x⁻¹))
        (polarizationClass B hX hk f σ hσ L hL) = z x hx - z x' hx' :=
      (picardMap_polarizationClass_point B hX hk f σ hσ _).trans (hdiff x hx x' hx')
    have hd := hasDegreeZero_sub B hX hk f σ hσ (hz x hx) (hz x' hx')
    refine ⟨e ▸ hd, ?_⟩
    rw [classifyingMap_congr B hX hk f σ hσ e (e ▸ hd)]
    have hsub := classifyingMap_add B hX hk f σ hσ _ (hz x hx)
      (hasDegreeZero_neg B hX hk f σ hσ (hz x' hx'))
    rw [classifyingMap_neg B hX hk f σ hσ _ (hz x' hx'), hzc, hzc] at hsub
    refine (classifyingMap_congr B hX hk f σ hσ (sub_eq_add_neg _ _) _).trans (hsub.trans ?_)
    rw [mul_inv, inv_inv, mul_comm]
  refine ⟨hpt, ?_⟩
  obtain ⟨x, hx, -, -, -⟩ := hS 1
  obtain ⟨h, hc⟩ := hpt x⁻¹
  have e := picardMap_polarizationClass_point B hX hk f σ hσ (L := L) (hL := hL) x⁻¹
  have hc' : classifyingMap B hX hk f σ hσ _ _ (e ▸ h) =
      classifyingMap B hX hk f σ hσ _ _ (hz x hx) := by
    rw [← classifyingMap_congr B hX hk f σ hσ e h, hc, inv_inv, hzc]
  have := eq_of_classifyingMap_eq_powerObj_zero B hX hk f σ hσ _ _ hc'
  rw [hψ x hx] at this
  have h3 : g • pointP B hX hk f σ hσ - ajQ B hX hk f σ hσ L hL = 0 := by
    refine add_left_cancel (a := z x hx) ?_
    rw [add_zero, ← add_sub_assoc]
    exact this
  exact (sub_eq_zero.1 h3).symm

variable (φ : X ⟶ X) (w : φ ≫ B.inclusion.map f = B.inclusion.map f)

/-- **Weil's formula, `ℓ`-adically, from the theta translates**: positive genus, an invertible
`L` on `J`, and a set `S ⊆ J(k)` with `S - S = J(k)` such that for `x ∈ S`,
`(aj - x)^* L = z_x + g[c₀]` with `z_x` of degree zero and classifying map `x`. -/
theorem fixedPointIntersection_eq_of_translates (hdim : topologicalKrullDim X ≤ 1)
    (hg : 0 < genus (B.inclusion.map f))
    (S : Set (power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X))
    (hS : ∀ y, ∃ x ∈ S, ∃ x' ∈ S, y = x' * x⁻¹)
    (hT : ∀ x ∈ S, ∃ (z : picardAt B hX hk f (powerObj B hX hk f 0))
      (hz : HasDegreeZero B hX hk f σ hσ _ z), classifyingMap B hX hk f σ hσ _ z hz = x ∧
        classQ (jacobianGrp B hX hk f σ hσ).X L hL
            (ajOne B hX hk f σ hσ + pointConst B hX hk f σ hσ x⁻¹) =
          z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    ((CurveGraph.fixedPointIntersection (B.inclusion.map f) hdim φ w : ℤ) : ℤ_[ℓ]) =
      1 - CurveGraph.jacobianTateTrace (B.inclusion.map f) hdim φ w ℓ +
        (CurveGraph.curveMapDegree (B.inclusion.map f) φ w : ℤ_[ℓ]) := by
  obtain ⟨hpt, hQ⟩ := polarization_of_translates B hX hk f σ hσ _ S hS hT
  have hdimJ := abelianVarietyDimension_jacobian B hX hk f σ hσ
  refine fixedPointIntersection_eq_of_points B hX hk f σ hσ φ w hdim (by omega) hpt ?_ ℓ hℓ
  show curveDeg (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f)
    (ajQ B hX hk f σ hσ L hL) = _
  rw [hQ, hdimJ]
  exact (curveDeg_zsmul (curveOver B hX hk f) (topologicalKrullDim_curveOver B hX hk f) _
    (pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ))).trans (by
      rw [curveDeg_pointClass, mul_one])

end Stacks.PicardFunctor

end
