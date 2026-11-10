/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.PolarizationCriterion
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Representability
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeparablyClosed
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# The theta translates generate the points of the Jacobian

Let `X` be a smooth projective curve of genus `g` over an algebraically closed field `k` with a
rational point `c₀`, and let `J` be its Jacobian. A `k`-point `x` of `J` is a *theta translate*
when `z_x + g[c₀]` is normalized, `H¹ = 0` and `dim H⁰ = 1`, for the degree-zero class `z_x` on
`X` classified by `x` (`Stacks.PicardFunctor.thetaTranslates`). These are the `k`-points of an
open subscheme `V` of `J`: the normalized locus of `ξ + g[c₀]`, for `ξ` the universal
degree-zero class on `X ×_k J`. By [Stacks, Tag 0B9Y] the open `V` is nonempty, and since `J` is
irreducible, `V ∩ y⁻¹V` contains a closed point for every `k`-point `y`. Hence every `k`-point of
`J` is a difference of two theta translates
(`Stacks.PicardFunctor.exists_mem_thetaTranslates_mul_inv`), the hypothesis `S - S = J(k)` of
`Stacks.PicardFunctor.fixedPointIntersection_eq_of_translates`.

## Main definitions

* `Stacks.PicardFunctor.IsNormalizedPointClass`: a class on `C^1 = X` with `H¹ = 0` and
  `dim H⁰ = 1`.
* `Stacks.PicardFunctor.thetaTranslates`: the theta translates in `J(k)`.

## Main results

* `Stacks.PicardFunctor.exists_mem_thetaTranslates_mul_inv`: `S - S = J(k)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open CartesianMonoidalCategory Stacks.CurvePower
open scoped CategoryTheory.MonObj

universe u

namespace CategoryTheory.GrpObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G : C} [GrpObj G]

/-- Left translation by a point `a`, `g ↦ a g`, evaluated at a point `x`. -/
theorem comp_toUnit_comp_mul_id (a x : 𝟙_ C ⟶ G) : x ≫ ((toUnit G ≫ a) * 𝟙 G) = a * x := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (𝟙 _),
    Category.id_comp]

/-- Left translations compose: `t_a ∘ t_b = t_{ab}`. -/
theorem toUnit_comp_mul_id_comp (a b : 𝟙_ C ⟶ G) :
    ((toUnit G ≫ b) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = (toUnit G ≫ (a * b)) * 𝟙 G := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (((toUnit G ≫ b) * 𝟙 G) ≫ toUnit G) (toUnit G), ← mul_assoc, ← MonObj.comp_mul]

end CategoryTheory.GrpObj

namespace Stacks.PicardFunctor

open Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k]

attribute [local instance] isAbelianVariety_jacobian

/-- **A normalized class on `C^1 = X`**: an invertible module with `H¹ = 0` and `dim H⁰ = 1`. -/
def IsNormalizedPointClass (w : picardAt B hX hk f (powerObj B hX hk f 0)) : Prop :=
  ∀ t, Module.finrank
      (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (powerObj B hX hk f 0)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology (baseChangeProj B hX hk f _)
        (Stacks.PicardCurve.rep w) t 1) = 0 ∧
    Module.finrank
      (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (powerObj B hX hk f 0)).residueField t)
      (Stacks.FibreCohomology.fibreCohomology (baseChangeProj B hX hk f _)
        (Stacks.PicardCurve.rep w) t 0) = 1

/-- **The theta translates**: the `k`-points `x` of `J` with `z_x + g[c₀]` normalized, for `z_x`
the degree-zero class on `X` classified by `x`. -/
def thetaTranslates : Set (power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :=
  {x | ∃ (z : picardAt B hX hk f (powerObj B hX hk f 0))
    (hz : HasDegreeZero B hX hk f σ hσ _ z), classifyingMap B hX hk f σ hσ _ z hz = x ∧
      IsNormalizedPointClass B hX hk f
        (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)}

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- A class on `C^1 = X` is normalized if and only if its fibre ranks in degrees `1` and `0` are
`0` and `1`. -/
theorem isNormalizedPointClass_iff (w : picardAt B hX hk f (powerObj B hX hk f 0)) :
    IsNormalizedPointClass B hX hk f w ↔
      ∀ t, classFibreRank (baseChangeProj B hX hk f _) w t 1 = 0 ∧
        classFibreRank (baseChangeProj B hX hk f _) w t 0 = 1 :=
  Iff.rfl

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- Any two morphisms into `C^0 = Spec k` agree. -/
theorem hom_powerObj_zero_ext {T : BigFppfOver B (Spec (.of k)) hk}
    (a b : T ⟶ powerObj B hX hk f 0) : a = b :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).map_injective
    (toUnit_unique (C := Over (Spec (.of k))) _ _)

omit [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- A normalized class on `C^1` has fibre degree `g`, so `w - g[c₀]` has degree zero. -/
theorem hasDegreeZero_sub_genus_smul_pointP (w : picardAt B hX hk f (powerObj B hX hk f 0))
    (hw : IsNormalizedPointClass B hX hk f w) :
    HasDegreeZero B hX hk f σ hσ _
      (w - (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ) := by
  intro t
  change curveFibreDegree B hX hk f σ hσ _ _ t = 0
  let δ : (picardFunctor B hX hk f).obj (op (powerObj B hX hk f 0)) →+ ℤ :=
    AddMonoidHom.mk' (fun ξ => curveFibreDegree B hX hk f σ hσ _ ξ t)
      (fun a b => fibreDegree_add B hX hk f σ hσ _ _ a b t)
  change δ (toPicardFunctorHom B hX hk f _ _) = 0
  rw [map_sub, map_zsmul, map_sub, map_zsmul]
  have hP : δ (toPicardFunctorHom B hX hk f _ (pointP B hX hk f σ hσ)) = 1 :=
    curveFibreDegree_familyClass B hX hk f σ hσ (powerObj B hX hk f 0)
      (graphFamily (curveOver B hX hk f) 0 (curvePowerZeroBasePoint B hX hk f σ hσ)) t
  have hW : δ (toPicardFunctorHom B hX hk f _ w) = genus (B.inclusion.map f) := by
    obtain ⟨h1, h0⟩ := (isNormalizedPointClass_iff B hX hk f w).1 hw t
    change fibreEuler B hX hk f σ hσ _ (powerObj B hX hk f 0) _ t -
      fibreEuler B hX hk f σ hσ _ (powerObj B hX hk f 0) 0 t = _
    rw [fibreEuler_zero, fibreEuler, fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom,
      h1, h0]
    push_cast
    ring
  rw [hP, hW, smul_eq_mul, mul_one, sub_self]

/-- The structure morphism of a test scheme to `C^0 = Spec k`. -/
abbrev toPowerObjZero (T : BigFppfOver B (Spec (.of k)) hk) : T ⟶ powerObj B hX hk f 0 :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage
    (toUnit ((Over.post (X := B.obj hk) B.inclusion).obj T) :
      _ ⟶ power (curveOver B hX hk f) 0)

/-- **The class `ξ + g[c₀]` on `X ×_k J`**, `[c₀]` pulled back from `C^1 = X`. -/
abbrev thetaClass (ξ : picardAt B hX hk f (picardSchemeDegreeComponent B hX hk f σ hσ 0)) :
    picardAt B hX hk f (picardSchemeDegreeComponent B hX hk f σ hσ 0) :=
  ξ + (genus (B.inclusion.map f) : ℤ) •
    picardMap B hX hk f (toPowerObjZero B hX hk f _) (pointP B hX hk f σ hσ)

omit [IsAlgClosed k] in
/-- The fibre of `ξ + g[c₀]` at a `k`-point `x` of `J` is `x^*ξ + g[c₀]`. -/
theorem picardMap_powerHomJac_thetaClass
    (ξ : picardAt B hX hk f (picardSchemeDegreeComponent B hX hk f σ hσ 0))
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) x) (thetaClass B hX hk f σ hσ ξ) =
      picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) x) ξ +
        (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ := by
  change picardMapHom B hX hk f _ (_ + _) = _
  rw [map_add, map_zsmul]
  change _ + _ • picardMap B hX hk f _ (picardMap B hX hk f _ _) = _
  rw [← picardMap_comp, hom_powerObj_zero_ext B hX hk f (_ ≫ _) (𝟙 _), picardMap_id]
  rfl

omit [IsAlgClosed k] in
/-- The fibre ranks of the pullback of a class on `X ×_k J` along a `k`-point `x` of `J` are those
of the class at the point `x`. -/
theorem classFibreRank_picardMap_powerHomJac
    (Θ : picardAt B hX hk f (picardSchemeDegreeComponent B hX hk f σ hσ 0))
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X)
    (t : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (powerObj B hX hk f 0))) (n : ℕ) :
    classFibreRank (baseChangeProj B hX hk f _)
        (picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) x) Θ) t n =
      classFibreRank (baseChangeProj B hX hk f _) Θ (x.left t) n := by
  have h := classFibreRank_schemePullbackClass (baseChangeProj B hX hk f _)
    (baseChangeMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) x))
    (baseChangeProj B hX hk f _) _
    (isPullback_baseChangeMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) x)) Θ t n
  have hl : B.inclusion.map (powerHomJac B hX hk f σ hσ (m := 0) x).left = x.left :=
    congrArg Over.Hom.left (post_map_powerHomJac B hX hk f σ hσ x)
  refine h.trans ?_
  rw [hl]
  rfl

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable]
  [IsAlgClosed k] in
/-- A point `t` of `T` lies in the normalized locus of a class `x` on `X ×_k T` if and only if the
fibre ranks of `x` at `t` in degrees `1` and `0` are `0` and `1`. -/
theorem mem_curveNormalizedLocus_toPicardFunctorHom_iff (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX hk f T) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    t ∈ curveNormalizedLocus B hX hk f σ hσ T (toPicardFunctorHom B hX hk f T x) ↔
      classFibreRank (baseChangeProj B hX hk f T) x t 1 = 0 ∧
        classFibreRank (baseChangeProj B hX hk f T) x t 0 = 1 := by
  change fibreRank B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ) T _ t 1 = 0 ∧
    fibreRank B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ) T _ t 0 = 1 ↔ _
  rw [fibreRank_eq, fibreRank_eq]

omit [IsAlgClosed k] in
/-- **The theta translates are the `k`-points of the normalized locus of `ξ + g[c₀]`**, for `ξ`
the universal degree-zero class on `X ×_k J`. -/
theorem mem_thetaTranslates_iff
    {ξ : picardAt B hX hk f (picardSchemeDegreeComponent B hX hk f σ hσ 0)}
    (hξ : HasDegreeZero B hX hk f σ hσ _ ξ)
    (hcl : classifyingMap B hX hk f σ hσ _ ξ hξ = 𝟙 _)
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    x ∈ thetaTranslates B hX hk f σ hσ ↔
      ∀ t, x.left t ∈ curveNormalizedLocus B hX hk f σ hσ _
        (toPicardFunctorHom B hX hk f _ (thetaClass B hX hk f σ hσ ξ)) := by
  have hzx := hasDegreeZero_picardMap B hX hk f σ hσ (powerHomJac B hX hk f σ hσ (m := 0) x) hξ
  have hcx : classifyingMap B hX hk f σ hσ _ _ hzx = x := by
    rw [← classifyingMap_comp B hX hk f σ hσ (powerHomJac B hX hk f σ hσ (m := 0) x) ξ hξ, hcl,
      post_map_powerHomJac]
    exact Category.comp_id _
  have hN : IsNormalizedPointClass B hX hk f
      (picardMap B hX hk f (powerHomJac B hX hk f σ hσ (m := 0) x) ξ +
        (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ) ↔ ∀ t, x.left t ∈
        curveNormalizedLocus B hX hk f σ hσ _
          (toPicardFunctorHom B hX hk f _ (thetaClass B hX hk f σ hσ ξ)) := by
    rw [isNormalizedPointClass_iff]
    refine forall_congr' fun t => Iff.symm ?_
    refine (mem_curveNormalizedLocus_toPicardFunctorHom_iff B hX hk f σ hσ _ _ (x.left t)).trans ?_
    rw [← picardMap_powerHomJac_thetaClass, classFibreRank_picardMap_powerHomJac,
      classFibreRank_picardMap_powerHomJac]
  constructor
  · rintro ⟨z, hz, hzc, hzN⟩
    obtain rfl := eq_of_classifyingMap_eq_powerObj_zero B hX hk f σ hσ hz hzx (hzc.trans hcx.symm)
    exact hN.1 hzN
  · exact fun h => ⟨_, hzx, hcx, hN.2 h⟩

/-- **The normalized locus of `ξ + g[c₀]` on `J` is nonempty**, by [Stacks, Tag 0B9Y]. -/
theorem exists_mem_curveNormalizedLocus_thetaClass
    {ξ : picardAt B hX hk f (picardSchemeDegreeComponent B hX hk f σ hσ 0)}
    (hξ : HasDegreeZero B hX hk f σ hσ _ ξ)
    (hcl : classifyingMap B hX hk f σ hσ _ ξ hξ = 𝟙 _) :
    ∃ v, v ∈ curveNormalizedLocus B hX hk f σ hσ _
      (toPicardFunctorHom B hX hk f _ (thetaClass B hX hk f σ hσ ξ)) := by
  have hsub : Subsingleton ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      (powerObj B hX hk f 0)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨t₀⟩ : Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      (powerObj B hX hk f 0)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨g₀, hg₀⟩ := exists_translate_mem_curveNormalizedLocus B hX hk f σ hσ
    (twistToNormalized_of_isSepClosed B hX hk f
      ((isProjectiveVariety_iff_isProjective k _).1 inferInstance))
    (powerObj B hX hk f 0) 0 t₀
  obtain ⟨w, hw⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) _
    ((translate B hX hk f g₀).hom.app (op (powerObj B hX hk f 0)) 0)
  rw [← hw] at hg₀
  have hg₁ := (mem_curveNormalizedLocus_toPicardFunctorHom_iff B hX hk f σ hσ _ w t₀).1 hg₀
  have hwN : IsNormalizedPointClass B hX hk f w :=
    (isNormalizedPointClass_iff B hX hk f w).2 fun t => Subsingleton.elim t₀ t ▸ hg₁
  have hz₀ := hasDegreeZero_sub_genus_smul_pointP B hX hk f σ hσ w hwN
  have hx₀ : classifyingMap B hX hk f σ hσ _ _ hz₀ ∈ thetaTranslates B hX hk f σ hσ :=
    ⟨_, hz₀, rfl, by rwa [sub_add_cancel]⟩
  exact ⟨_, (mem_thetaTranslates_iff B hX hk f σ hσ hξ hcl _).1 hx₀ t₀⟩

/-- **Every `k`-point of the Jacobian is a difference of two theta translates**: `S - S = J(k)`
for the set `S` of `x ∈ J(k)` with `z_x + g[c₀]` normalized. -/
theorem exists_mem_thetaTranslates_mul_inv
    (y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    ∃ x ∈ thetaTranslates B hX hk f σ hσ, ∃ x' ∈ thetaTranslates B hX hk f σ hσ, y = x' * x⁻¹ := by
  obtain ⟨ξ, hξ, hcl⟩ := exists_classifyingMap_eq B hX hk f σ hσ
    (picardSchemeDegreeComponent B hX hk f σ hσ 0)
    (𝟙 _ : _ ⟶ (jacobianGrp B hX hk f σ hσ).X)
  have hmem := mem_thetaTranslates_iff B hX hk f σ hσ hξ hcl
  obtain ⟨v, hv⟩ := exists_mem_curveNormalizedLocus_thetaClass B hX hk f σ hσ hξ hcl
  generalize curveNormalizedLocus B hX hk f σ hσ _
    (toPicardFunctorHom B hX hk f _ (thetaClass B hX hk f σ hσ ξ)) = V at hv hmem
  let JX := (jacobianGrp B hX hk f σ hσ).X
  let a : 𝟙_ (Over (Spec (.of k))) ⟶ JX := y
  let m : JX ⟶ JX := (toUnit JX ≫ a) * 𝟙 JX
  let m' : JX ⟶ JX := (toUnit JX ≫ a⁻¹) * 𝟙 JX
  have hmm : m' ≫ m = 𝟙 JX := by
    change ((toUnit JX ≫ a⁻¹) * 𝟙 JX) ≫ ((toUnit JX ≫ a) * 𝟙 JX) = 𝟙 JX
    rw [GrpObj.toUnit_comp_mul_id_comp, mul_inv_cancel, MonObj.comp_one, one_mul]
  let JY : Scheme.{u} := (Over.left (picardSchemeDegreeComponent B hX hk f σ hσ 0)).obj
  let mL : JY ⟶ JY := m.left
  let mL' : JY ⟶ JY := m'.left
  have hmmL : mL' ≫ mL = 𝟙 JY := congrArg Over.Hom.left hmm
  have : IrreducibleSpace JY :=
    (universallyClosed_picardSchemeDegreeComponent_zero B hX hk f σ hσ).2.2
  have hVo : IsOpen (V : Set JY) := V.isOpen
  have hmo : IsOpen (mL ⁻¹' (V : Set JY)) := hVo.preimage (Scheme.Hom.continuous mL)
  have hm'v : mL (mL' v) ∈ (V : Set JY) := by
    rwa [← Scheme.Hom.comp_apply, hmmL]
  have hU := nonempty_preirreducible_inter hVo hmo ⟨v, hv⟩ ⟨mL' v, hm'v⟩
  let πJ : JY ⟶ Spec (.of k) := JX.hom
  have : LocallyOfFiniteType πJ :=
    (isAbelianVariety_jacobian B hX hk f σ hσ).toIsProperVariety.toIsProper.toLocallyOfFiniteType
  have : JacobsonSpace JY := LocallyOfFiniteType.jacobsonSpace πJ
  obtain ⟨p, ⟨hpV, hpm⟩, hp⟩ := nonempty_inter_closedPoints hU (hVo.inter hmo).isLocallyClosed
  let x : power (curveOver B hX hk f) 0 ⟶ JX :=
    Over.homMk (pointOfClosedPoint πJ p hp) (pointOfClosedPoint_comp πJ p hp)
  have hxp : ∀ t, x.left t = p := fun t => pointOfClosedPoint_apply πJ p hp t
  have hx : x ∈ thetaTranslates B hX hk f σ hσ := (hmem x).2 fun t => (hxp t).symm ▸ hpV
  have hyx : x ≫ m = y * x := GrpObj.comp_toUnit_comp_mul_id a x
  have hx' : y * x ∈ thetaTranslates B hX hk f σ hσ :=
    hyx ▸ (hmem _).2 fun t => show mL (x.left t) ∈ V from (hxp t).symm ▸ hpm
  exact ⟨x, hx, y * x, hx', (mul_inv_cancel_right y x).symm⟩

end Stacks.PicardFunctor

end
