/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.CurvePowerSite
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeesawPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPullback
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerSection

/-!
# The polarization class of the Jacobian and the seesaw on `C × C`

Let `X` be a smooth projective curve over `k` with Jacobian `J`, Abel–Jacobi map `aj : X ⟶ J`
(`aj(c) = 𝒪(c - c₀)`) and let `L` be an invertible module on `J`. With `Q(x) = [x^* L]` and
`B(x, y) = Q(x + y) - Q(x) - Q(y)`, the *polarization class* of `L` is the class
`Λ_L = B(aj ∘ pr_X, pr_J)` on `X ×_k J`, a family of invertible modules on `X` parametrised by
`J`: its fibre at `y ∈ J` is `aj^*(t_y^* L) - aj^* L`.

This file computes, from the single input "`Λ_L` has degree-zero fibres and classifying map
`-𝟙_J`", the two seesaw identities on `X × X` used in the proof of [Stacks, Tag 03U1]:

* `B(aj ∘ p₀, aj ∘ p₁) = F₀ + F₁ - Δ` on `C^2`, the hypothesis of
  `Stacks.CurvePower.abelianVarietyTrace_eq_curveDeg`;
* for an endomorphism `φ` of `X` with `α = φ^*` on `J`,
  `B(aj ∘ p₀, α ∘ aj ∘ p₁) = -(φ × 1)^* Δ + (φ × 1)^* F₀ + p₁^*[φ(c₀)]`.

Both come from the seesaw principle `Stacks.PicardFunctor.classifyingMap_eq_classifyingMap_iff`
on the test scheme `C^1`, the constant of integration being read off along the section
`c ↦ (c₀, c)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

section BaseChange

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- **The base change of a morphism of test schemes** `g : T' ⟶ T` is `𝟙 × g`. -/
theorem baseChangeMap_eq_lift {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    baseChangeMap B hX hk f g =
      (lift (fst (curveOver B hX hk f) ((Over.post (X := B.obj hk) B.inclusion).obj T'))
        (snd _ _ ≫ (Over.post (X := B.obj hk) B.inclusion).map g) :
          curveOver B hX hk f ⊗ (Over.post (X := B.obj hk) B.inclusion).obj T' ⟶
            curveOver B hX hk f ⊗ (Over.post (X := B.obj hk) B.inclusion).obj T).left := by
  apply pullback.hom_ext
  · refine Eq.trans ?_ (congrArg Over.Hom.left (lift_fst
      (fst (curveOver B hX hk f) ((Over.post (X := B.obj hk) B.inclusion).obj T'))
      (snd (curveOver B hX hk f) ((Over.post (X := B.obj hk) B.inclusion).obj T') ≫
          (Over.post (X := B.obj hk) B.inclusion).map g))).symm
    simp only [baseChangeMap, pullback.lift_fst, Category.comp_id]
    rfl
  · refine Eq.trans ?_ (congrArg Over.Hom.left (lift_snd
      (fst (curveOver B hX hk f) ((Over.post (X := B.obj hk) B.inclusion).obj T'))
      (snd (curveOver B hX hk f) ((Over.post (X := B.obj hk) B.inclusion).obj T') ≫
          (Over.post (X := B.obj hk) B.inclusion).map g))).symm
    simp only [baseChangeMap, pullback.lift_snd]
    rfl

end BaseChange

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable]

/-! ### Classifying maps of negatives and of `φ^*`-pullbacks -/

/-- The classifying map of `-x` is the inverse of that of `x`. -/
theorem classifyingMap_neg (T : BigFppfOver B (Spec (.of k)) hk) {x : picardAt B hX hk f T}
    (hx : HasDegreeZero B hX hk f σ hσ T x) :
    classifyingMap B hX hk f σ hσ T (-x) (hasDegreeZero_neg B hX hk f σ hσ hx) =
      (classifyingMap B hX hk f σ hσ T x hx)⁻¹ := by
  have h := classifyingMap_add B hX hk f σ hσ T (hasDegreeZero_neg B hX hk f σ hσ hx) hx
  have h0 : classifyingMap B hX hk f σ hσ T (-x + x)
      (hasDegreeZero_add B hX hk f σ hσ (hasDegreeZero_neg B hX hk f σ hσ hx) hx) = 1 := by
    rw [← classifyingMap_zero B hX hk f σ hσ T]
    congr 1
    exact neg_add_cancel x
  rw [h0] at h
  exact eq_inv_of_mul_eq_one_left h.symm

variable [IsAlgClosed k] (Ψ : X ⟶ X) (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f)

/-- `(Ψ × 1)^*` preserves classes with degree-zero fibres. -/
theorem hasDegreeZero_endoBaseChangeMap (T : BigFppfOver B (Spec (.of k)) hk)
    {x : picardAt B hX hk f T} (hx : HasDegreeZero B hX hk f σ hσ T x) :
    HasDegreeZero B hX hk f σ hσ T
      (Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ T) x) := by
  have e := jacobianHomAddEquiv_comp_jacobianPullback B hX hk f Ψ hΨ σ hσ T
    (classifyingMap B hX hk f σ hσ T x hx)
  rw [jacobianHomAddEquiv_classifyingMap] at e
  change _ = (endoPicardMap B hX hk f Ψ hΨ).app (op T) ((toPicardFunctor B hX hk f).app (op T) x)
    at e
  rw [endoPicardMap_toPicardFunctor] at e
  rw [HasDegreeZero]
  change (toPicardFunctor B hX hk f).app (op T) _ ∈ _
  rw [← e]
  exact SetLike.coe_mem _

/-- **The classifying map of `(Ψ × 1)^* x` is that of `x` followed by `Ψ^*` on the Jacobian.** -/
theorem classifyingMap_endoBaseChangeMap (T : BigFppfOver B (Spec (.of k)) hk)
    {x : picardAt B hX hk f T} (hx : HasDegreeZero B hX hk f σ hσ T x) :
    classifyingMap B hX hk f σ hσ T
        (Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ T) x)
        (hasDegreeZero_endoBaseChangeMap B hX hk f σ hσ Ψ hΨ T hx) =
      classifyingMap B hX hk f σ hσ T x hx ≫ jacobianPullback B hX hk f Ψ hΨ σ hσ := by
  have e := jacobianHomAddEquiv_comp_jacobianPullback B hX hk f Ψ hΨ σ hσ T
    (classifyingMap B hX hk f σ hσ T x hx)
  rw [jacobianHomAddEquiv_classifyingMap] at e
  change _ = (endoPicardMap B hX hk f Ψ hΨ).app (op T) ((toPicardFunctor B hX hk f).app (op T) x)
    at e
  rw [endoPicardMap_toPicardFunctor] at e
  apply Additive.ofMul.injective
  apply (jacobianHomAddEquiv B hX hk f σ hσ T).injective
  rw [jacobianHomAddEquiv_classifyingMap]
  exact Subtype.ext e.symm

/-! ### The polarization class -/

section Polarization

attribute [local instance] isAbelianVariety_jacobian

instance isVariety_curveOver : IsVariety k (curveOver B hX hk f).hom :=
  inferInstanceAs (IsVariety k (B.inclusion.map f))

instance isProper_curveOver : IsProper (curveOver B hX hk f).hom :=
  inferInstanceAs (IsProper (B.inclusion.map f))

instance smoothOfRelativeDimension_curveOver :
    SmoothOfRelativeDimension 1 (curveOver B hX hk f).hom :=
  smoothOfRelativeDimension_one_of_isCurve k (B.inclusion.map f)

omit [GeometricallyIrreducible (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
  [IsProper (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem topologicalKrullDim_curveOver : topologicalKrullDim (curveOver B hX hk f).left = 1 :=
  IsCurve.topologicalKrullDim_eq_one (f := B.inclusion.map f)

include hσ in
/-- **The base point `c₀`** as a point `C^0 ⟶ C` of the curve over `k`. -/
def curvePowerZeroBasePoint :
    Stacks.CurvePower.power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f :=
  Over.homMk σ hσ

variable
  (L : SheafOfModules.{u} (structureSheafRing (jacobianGrp B hX hk f σ hσ).X.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible (jacobianGrp B hX hk f σ hσ).X.left.presheaf
    (jacobianGrp B hX hk f σ hσ).X.left.ringCatIsSheaf L)

/-- **The polarization class** `Λ_L = B(aj ∘ pr_X, pr_J)` on `X ×_k J` of an invertible module `L`
on the Jacobian, with `B(x, y) = [(x + y)^* L] - [x^* L] - [y^* L]`. -/
abbrev polarizationClass : picardAt B hX hk f (picardSchemeDegreeComponent B hX hk f σ hσ 0) :=
  Stacks.QuadraticMap.cubeBilin (Stacks.CurvePower.classQ (jacobianGrp B hX hk f σ hσ).X L hL)
    (Additive.ofMul (fst (curveOver B hX hk f) (jacobianGrp B hX hk f σ hσ).X ≫
      abelJacobi B hX hk f σ hσ))
    (Additive.ofMul (snd (curveOver B hX hk f) (jacobianGrp B hX hk f σ hσ).X))

/-- The restriction of the polarization class along `g : T ⟶ J` is `B(aj ∘ pr_X, g ∘ pr_T)`. -/
theorem picardMap_polarizationClass {T : BigFppfOver B (Spec (.of k)) hk}
    (g : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0) :
    picardMap B hX hk f g (polarizationClass B hX hk f σ hσ L hL) =
      Stacks.QuadraticMap.cubeBilin (Stacks.CurvePower.classQ (jacobianGrp B hX hk f σ hσ).X L hL)
        (Additive.ofMul (fst (curveOver B hX hk f) ((Over.post (X := B.obj hk) B.inclusion).obj T) ≫
          abelJacobi B hX hk f σ hσ))
        (Additive.ofMul (snd (curveOver B hX hk f) ((Over.post (X := B.obj hk) B.inclusion).obj T) ≫
          (Over.post (X := B.obj hk) B.inclusion).map g)) := by
  rw [picardMap, baseChangeMap_eq_lift]
  refine (Stacks.CurvePower.schemePullbackClass_cubeBilin_classQ (jacobianGrp B hX hk f σ hσ).X L hL
    _ _ _).trans ?_
  congr 1
  · exact congrArg Additive.ofMul (lift_fst_assoc _ _ _)
  · exact congrArg Additive.ofMul (lift_snd _ _)

variable {L hL} (hΛ : HasDegreeZero B hX hk f σ hσ _ (polarizationClass B hX hk f σ hσ L hL))
  (hcl : classifyingMap B hX hk f σ hσ _ _ hΛ = (𝟙 (jacobianGrp B hX hk f σ hσ).X)⁻¹)

include hcl in
/-- If `Λ_L` has classifying map `-𝟙_J`, its restriction along `g : T ⟶ J` has classifying map
`-g`. -/
theorem classifyingMap_picardMap_polarizationClass {T : BigFppfOver B (Spec (.of k)) hk}
    (g : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0) :
    classifyingMap B hX hk f σ hσ T (picardMap B hX hk f g (polarizationClass B hX hk f σ hσ L hL))
        (hasDegreeZero_picardMap B hX hk f σ hσ g hΛ) =
      ((Over.post (X := B.obj hk) B.inclusion).map g ≫ 𝟙 (jacobianGrp B hX hk f σ hσ).X)⁻¹ := by
  rw [← classifyingMap_comp B hX hk f σ hσ g _ hΛ, hcl]
  exact GrpObj.comp_inv _ _

end Polarization

/-! ### The seesaw on `C^2` -/

section Seesaw

attribute [local instance] isAbelianVariety_jacobian

open Stacks.CurvePower

/-- A morphism `C^m ⟶ C` as a morphism of test schemes. -/
abbrev powerHomCurve {m : ℕ} (y : power (curveOver B hX hk f) m ⟶ curveOver B hX hk f) :
    powerObj B hX hk f m ⟶ curveObj B hX hk f :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage y

/-- A morphism `C^m ⟶ J` as a morphism of test schemes. -/
abbrev powerHomJac {m : ℕ}
    (y : power (curveOver B hX hk f) m ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    powerObj B hX hk f m ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0 :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage y

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem post_map_powerHomCurve {m : ℕ}
    (y : power (curveOver B hX hk f) m ⟶ curveOver B hX hk f) :
    (Over.post (X := B.obj hk) B.inclusion).map (powerHomCurve B hX hk f y) = y :=
  Functor.FullyFaithful.map_preimage _ _

omit [IsAlgClosed k] in
theorem post_map_powerHomJac {m : ℕ}
    (y : power (curveOver B hX hk f) m ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    (Over.post (X := B.obj hk) B.inclusion).map (powerHomJac B hX hk f σ hσ y) = y :=
  Functor.FullyFaithful.map_preimage _ _

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable]
  [IsAlgClosed k] in
/-- **The Abel–Jacobi class restricted to `C^m` along `y`** is `[Γ_y] - [Γ_{c₀}]`. -/
theorem picardMap_abelJacobiClass {m : ℕ}
    (y : power (curveOver B hX hk f) m ⟶ curveOver B hX hk f) :
    picardMap B hX hk f (powerHomCurve B hX hk f y) (abelJacobiClass B hX hk f σ hσ) =
      (graphFamily (curveOver B hX hk f) m y).picardClass -
        (graphFamily (curveOver B hX hk f) m (y ≫ constantPoint B hX hk f σ hσ)).picardClass := by
  have hy := post_map_powerHomCurve B hX hk f y
  have hb : baseChangeMap B hX hk f (powerHomCurve B hX hk f y) =
      Stacks.Hilbert.familyBaseChangeMap (curveOver B hX hk f) y := by
    rw [baseChangeMap_eq_lift, familyBaseChangeMap_eq, hy]
    rfl
  rw [abelJacobiClass, picardMap, schemePullbackClass_sub, hb]
  have := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
    (curveOver B hX hk f) (𝟙 _)
  have := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
    (curveOver B hX hk f) (constantPoint B hX hk f σ hσ)
  congr 1
  · refine Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass _ _ _ ?_
    exact ((Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap _ y _).trans
      (by rw [Category.comp_id]; rfl)).symm
  · exact Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass _ _ _
      (Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap _ y _).symm

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable]
  [IsAlgClosed k] in
theorem comp_constantPoint {T : Over (Spec (.of k))} (y : T ⟶ curveOver B hX hk f) :
    y ≫ constantPoint B hX hk f σ hσ = toUnit T ≫ curvePowerZeroBasePoint B hX hk f σ hσ := by
  apply Over.OverMorphism.ext
  have hw : y.left ≫ B.inclusion.map f = T.hom := Over.w y
  have hu : (toUnit T).left ≫ (𝟙_ (Over (Spec (.of k)))).hom = T.hom := Over.w (toUnit T)
  simp only [Over.comp_left, constantPoint, curvePowerZeroBasePoint, Over.homMk_left]
  rw [← Category.assoc, hw, ← hu]
  rfl

/-- **The Abel–Jacobi map vanishes at the base point.** -/
theorem curvePowerZeroBasePoint_comp_abelJacobi :
    curvePowerZeroBasePoint B hX hk f σ hσ ≫ abelJacobi B hX hk f σ hσ = 1 := by
  have h := classifyingMap_comp B hX hk f σ hσ
    (powerHomCurve B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ))
    (abelJacobiClass B hX hk f σ hσ) (hasDegreeZero_familyClass_sub B hX hk f σ hσ _ _ _)
  rw [post_map_powerHomCurve] at h
  refine h.trans (Eq.trans ?_ (classifyingMap_zero B hX hk f σ hσ (powerObj B hX hk f 0)))
  congr 1
  rw [picardMap_abelJacobiClass, comp_constantPoint, sub_eq_zero]
  congr 2

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable]
  [IsAlgClosed k] in
/-- The second projection `C^2 ⟶ C^1` is the reindexing by the second coordinate. -/
theorem reindex_one_eq_snd :
    reindex (curveOver B hX hk f) (fun _ : Fin 1 => (1 : Fin 2)) =
      snd (curveOver B hX hk f) (power (curveOver B hX hk f) 1) := by
  refine hom_ext 1 fun i => ?_
  fin_cases i
  rw [reindex_coord]
  rfl

variable
  (L : SheafOfModules.{u} (structureSheafRing (jacobianGrp B hX hk f σ hσ).X.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible (jacobianGrp B hX hk f σ hσ).X.left.presheaf
    (jacobianGrp B hX hk f σ hσ).X.left.ringCatIsSheaf L)

/-- `Q` of a morphism `C^m ⟶ J` factoring through `C^0` vanishes. -/
theorem classQ_toPowerZero_comp {m : ℕ}
    (y : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    classQ (jacobianGrp B hX hk f σ hσ).X L hL
      (Additive.ofMul (toPowerZero (curveOver B hX hk f) m ≫ y)) = 0 := by
  have h := schemePullbackClass_classQ (jacobianGrp B hX hk f σ hσ).X L hL
    (toPowerZero (curveOver B hX hk f) m) (Additive.ofMul y)
  rw [precompHom_apply, toMul_ofMul] at h
  rw [← h, Subsingleton.elim (classQ (jacobianGrp B hX hk f σ hσ).X L hL (Additive.ofMul y)) 0]
  exact (Stacks.Picard.schemePullbackClassHom (toPowerZero (curveOver B hX hk f) m).left).map_zero

/-! #### Classes on `C^2`, all spelled in `picardAt (powerObj 1)` -/

/-- `Δ` on `C^2`, as a point of the Picard functor over `C^1`. -/
abbrev diagP : picardAt B hX hk f (powerObj B hX hk f 1) :=
  (graphFamily (curveOver B hX hk f) 1 (coord (curveOver B hX hk f) 1 0)).picardClass

/-- `F₀ = {c₀} × C` on `C^2`, as a point of the Picard functor over `C^1`. -/
abbrev fibreP : picardAt B hX hk f (powerObj B hX hk f 1) :=
  (graphFamily (curveOver B hX hk f) 1 (toPowerZero (curveOver B hX hk f) 1 ≫
    curvePowerZeroBasePoint B hX hk f σ hσ)).picardClass

/-- The pullback `p₁^* N` of a class on `C^1` to `C^2`. -/
abbrev pullSndP (N : PowerPic (curveOver B hX hk f) 1) :
    picardAt B hX hk f (powerObj B hX hk f 1) :=
  Stacks.Picard.schemePullbackClass (baseChangeProj B hX hk f (powerObj B hX hk f 1)) N

/-- Restriction along the section `x ↦ (c, x)`, as a homomorphism on `picardAt (powerObj 1)`. -/
abbrev sectionRestrict (c : power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f) :
    picardAt B hX hk f (powerObj B hX hk f 1) →+ PowerPic (curveOver B hX hk f) 1 :=
  Stacks.Picard.schemePullbackClassHom (insertPoint (curveOver B hX hk f) c 1 0).left

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem insertPoint_comp_snd (c : power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f) :
    (insertPoint (curveOver B hX hk f) c 1 0).left ≫
      baseChangeProj B hX hk f (powerObj B hX hk f 1) = 𝟙 _ := by
  have h : insertPoint (curveOver B hX hk f) c 1 0 ≫
      (snd (curveOver B hX hk f) (power (curveOver B hX hk f) 1) :
        power (curveOver B hX hk f) (1 + 1) ⟶ power (curveOver B hX hk f) 1) = 𝟙 _ := by
    refine hom_ext 1 fun i => ?_
    fin_cases i
    exact (Category.assoc _ _ _).trans ((insertPoint_coord_succAbove (curveOver B hX hk f) c 1 0
      0).trans (Category.id_comp _).symm)
  exact congrArg Over.Hom.left h

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
theorem sectionRestrict_pullSndP (c : power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f)
    (N : PowerPic (curveOver B hX hk f) 1) :
    sectionRestrict B hX hk f c (pullSndP B hX hk f N) = N := by
  refine (Stacks.Picard.schemePullbackClass_comp (insertPoint (curveOver B hX hk f) c 1 0).left
    (baseChangeProj B hX hk f (powerObj B hX hk f 1)) N).trans ?_
  rw [insertPoint_comp_snd, Stacks.Picard.schemePullbackClass_id]

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable]
  [IsAlgClosed k] in
theorem sectionRestrict_diagP (c : power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f) :
    sectionRestrict B hX hk f c (diagP B hX hk f) = pointClass (curveOver B hX hk f) c :=
  schemePullbackClass_insertPoint_diagClass (curveOver B hX hk f) c

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable]
  [IsAlgClosed k] in
theorem sectionRestrict_fibreP (c : power (curveOver B hX hk f) 0 ⟶ curveOver B hX hk f) :
    sectionRestrict B hX hk f c (fibreP B hX hk f σ hσ) = 0 :=
  schemePullbackClass_insertPoint_fibreClass (curveOver B hX hk f) c _

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable]
  [IsAlgClosed k] in
/-- The restriction of the Abel–Jacobi class along the coordinate `C^1 ⟶ C` is `Δ - F₀`. -/
theorem picardMap_abelJacobiClass_coord :
    picardMap B hX hk f (powerHomCurve B hX hk f (coord (curveOver B hX hk f) 1 0))
        (abelJacobiClass B hX hk f σ hσ) = diagP B hX hk f - fibreP B hX hk f σ hσ := by
  rw [picardMap_abelJacobiClass, comp_constantPoint]
  rfl

/-- **The seesaw on `C^2`.** A class `E` on `C^2 = C × C^1` whose classifying map, as a family
over `C^1`, is `-aj` and which vanishes along the section through `c₀` is `F₀ + F₁ - Δ`. -/
theorem eq_of_classifyingMap_eq_neg_abelJacobi {E : picardAt B hX hk f (powerObj B hX hk f 1)}
    (hE : HasDegreeZero B hX hk f σ hσ _ E)
    (hcE : classifyingMap B hX hk f σ hσ _ E hE =
      (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ)⁻¹)
    (hs : sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ) E = 0) :
    E = pullSndP B hX hk f
        (pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ)) -
      (diagP B hX hk f - fibreP B hX hk f σ hσ) := by
  set R := picardMap B hX hk f (powerHomCurve B hX hk f (coord (curveOver B hX hk f) 1 0))
    (abelJacobiClass B hX hk f σ hσ)
  have hR : HasDegreeZero B hX hk f σ hσ _ R :=
    hasDegreeZero_picardMap B hX hk f σ hσ _ (hasDegreeZero_familyClass_sub B hX hk f σ hσ _ _ _)
  have hcR : classifyingMap B hX hk f σ hσ _ R hR =
      coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ := by
    rw [← classifyingMap_comp, post_map_powerHomCurve]
    rfl
  have hc : classifyingMap B hX hk f σ hσ _ E hE =
      classifyingMap B hX hk f σ hσ _ (-R) (hasDegreeZero_neg B hX hk f σ hσ hR) := by
    rw [classifyingMap_neg B hX hk f σ hσ _ hR, hcR, hcE]
  obtain ⟨N, hN⟩ := (classifyingMap_eq_classifyingMap_iff B hX hk f σ hσ _ hE
    (hasDegreeZero_neg B hX hk f σ hσ hR)).1 hc
  change pullSndP B hX hk f N = E - -R at hN
  have hRv : R = diagP B hX hk f - fibreP B hX hk f σ hσ :=
    picardMap_abelJacobiClass_coord B hX hk f σ hσ
  rw [sub_neg_eq_add, hRv] at hN
  have h2 := congrArg (sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ)) hN
  rw [sectionRestrict_pullSndP, map_add, map_sub, hs, sectionRestrict_diagP,
    sectionRestrict_fibreP, sub_zero, zero_add] at h2
  rw [← h2, hN]
  abel

variable {L hL} (hΛ : HasDegreeZero B hX hk f σ hσ _ (polarizationClass B hX hk f σ hσ L hL))
  (hcl : classifyingMap B hX hk f σ hσ _ _ hΛ = (𝟙 (jacobianGrp B hX hk f σ hσ).X)⁻¹)

include hcl in
/-- **`B(aj ∘ p₀, aj ∘ p₁) = F₀ + F₁ - Δ` on `C × C`**, when the polarization class of `L` has
classifying map `-𝟙_J`: the hypothesis `hE` of
`Stacks.CurvePower.abelianVarietyTrace_eq_curveDeg`. -/
theorem cubeBilin_abelJacobi_eq_graphCorrespondence :
    Stacks.QuadraticMap.cubeBilin (classQ (jacobianGrp B hX hk f σ hσ).X L hL)
        (Additive.ofMul (coord (curveOver B hX hk f) 2 0 ≫ abelJacobi B hX hk f σ hσ))
        (Additive.ofMul (coord (curveOver B hX hk f) 2 1 ≫ abelJacobi B hX hk f σ hσ)) =
      graphCorrespondence (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ) 1 := by
  set g := powerHomJac B hX hk f σ hσ
    (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ)
  have hEq : picardMap B hX hk f g (polarizationClass B hX hk f σ hσ L hL) =
      Stacks.QuadraticMap.cubeBilin (classQ (jacobianGrp B hX hk f σ hσ).X L hL)
        (Additive.ofMul (coord (curveOver B hX hk f) 2 0 ≫ abelJacobi B hX hk f σ hσ))
        (Additive.ofMul (coord (curveOver B hX hk f) 2 1 ≫ abelJacobi B hX hk f σ hσ)) := by
    rw [picardMap_polarizationClass, post_map_powerHomJac]
    congr 2
  have hc := classifyingMap_picardMap_polarizationClass B hX hk f σ hσ hΛ hcl g
  have hg : (Over.post (X := B.obj hk) B.inclusion).map g =
      coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ :=
    post_map_powerHomJac B hX hk f σ hσ _
  rw [hg] at hc
  replace hc := hc.trans (congrArg (fun x => x⁻¹)
    (Category.comp_id (coord (curveOver B hX hk f) 1 0 ≫ abelJacobi B hX hk f σ hσ)))
  -- the restriction along the section through `c₀` vanishes, since `aj(c₀) = 0`
  have hs : sectionRestrict B hX hk f (curvePowerZeroBasePoint B hX hk f σ hσ)
      (picardMap B hX hk f g (polarizationClass B hX hk f σ hσ L hL)) = 0 := by
    rw [hEq]
    refine (schemePullbackClass_cubeBilin_classQ (jacobianGrp B hX hk f σ hσ).X L hL
      (insertPoint (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ) 1 0) _ _).trans ?_
    simp only [precompHom_apply, toMul_ofMul]
    rw [insertPoint_coord_self_assoc, curvePowerZeroBasePoint_comp_abelJacobi, MonObj.comp_one,
      ofMul_one]
    have hQ0 := classQ_toPowerZero_comp B hX hk f σ hσ L hL (m := 1) 1
    rw [MonObj.comp_one, ofMul_one] at hQ0
    rw [Stacks.QuadraticMap.cubeBilin, zero_add, hQ0, sub_zero, sub_self]
  have h := eq_of_classifyingMap_eq_neg_abelJacobi B hX hk f σ hσ
    (hasDegreeZero_picardMap B hX hk f σ hσ g hΛ) hc hs
  rw [hEq] at h
  refine h.trans ?_
  have e0 : Stacks.Picard.schemePullbackClass (reindex (curveOver B hX hk f)
      (fun _ : Fin 1 => (0 : Fin 2))).left
        (pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ)) =
      fibreClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ) 1 :=
    schemePullbackClass_firstProj_pointClass (curveOver B hX hk f)
      (curvePowerZeroBasePoint B hX hk f σ hσ) 1
  have e1 : Stacks.Picard.schemePullbackClass (reindex (curveOver B hX hk f)
      (fun _ : Fin 1 => (1 : Fin 2))).left
        (pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ)) =
      Stacks.Picard.schemePullbackClass (snd (curveOver B hX hk f)
        (power (curveOver B hX hk f) 1)).left
        (pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ)) := by
    rw [reindex_one_eq_snd]
    rfl
  rw [graphCorrespondence, one_smul, e0, e1]
  change _ = fibreP B hX hk f σ hσ +
    pullSndP B hX hk f (pointClass (curveOver B hX hk f) (curvePowerZeroBasePoint B hX hk f σ hσ)) -
      diagP B hX hk f
  abel

end Seesaw

end Stacks.PicardFunctor

end
