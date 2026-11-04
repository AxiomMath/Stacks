/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.PolarizationCriterion
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Representability
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingDiagonal
public import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingCartier
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral

/-!
# The theta divisor of a curve and the polarization it defines

Let `X` be a smooth projective curve of genus `g > 0` over an algebraically closed field `k`, with
base point `c₀`, Jacobian `J` and universal class `ξ` on `X ×_k J` (classifying map `𝟙_J`). The
*theta family* is `θ = -ξ + (g - 1)[c₀]`; its fibres have degree `g - 1`, hence Euler
characteristic zero, and the *theta divisor* `Θ ⊆ J` is the Fitting ideal sheaf of `R¹pr_* θ`.

For a `k`-point `x` of `J` with `N_x = z_x + g[c₀]` normalized (`H¹ = 0`, `H⁰` spanned by a
section `s`), the map `h_x = aj - x : X ⟶ J` pulls `θ` back to `N_x(-Δ)` up to a class from the
base, so `h_x^{-1} Θ = Z(s)` (`Stacks.FamilyFitting.familyFitting_diag_eq_zeroScheme`). Hence
`Θ` is an effective Cartier divisor
(`Stacks.FamilyFitting.isEffectiveCartierDivisor_familyFitting`) and `L = 𝒪(Θ)` satisfies
`(aj - x)^* L = N_x` for every such `x`. The set of these `x` is the set of `k`-points of a
nonempty open of `J`, so its difference set is `J(k)`: these are the hypotheses of
`Stacks.PicardFunctor.fixedPointIntersection_eq_of_translates`, and Weil's formula
([Stacks, Tag 03U1]) follows for curves of positive genus.

## Main definitions

* `Stacks.PicardFunctor.thetaFamily`: `θ = -ξ + (g - 1)[c₀]` on `X ×_k J`.
* `Stacks.PicardFunctor.thetaDivisor`: `Θ = Fit₀ R¹pr_* θ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open CartesianMonoidalCategory Stacks.CurvePower Stacks.FibreCohomology
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

/-! ### The universal class and the theta family -/

/-- The Jacobian as an object of the site. -/
abbrev jacObj : BigFppfOver B (Spec (.of k)) hk := picardSchemeDegreeComponent B hX hk f σ hσ 0

/-- The morphism of test schemes to the base point `C^0`. -/
abbrev toPointObj (T : BigFppfOver B (Spec (.of k)) hk) : T ⟶ powerObj B hX hk f 0 :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage
    (toUnit ((Over.post (X := B.obj hk) B.inclusion).obj T))

/-- **The universal class** on `X ×_k J`: its classifying map is the identity of `J`. -/
def jacUniversalClass : picardAt B hX hk f (jacObj B hX hk f σ hσ) :=
  (exists_classifyingMap_eq B hX hk f σ hσ (jacObj B hX hk f σ hσ) (𝟙 _)).choose

omit [IsAlgClosed k] in
/-- The universal class on `X ×_k J` has degree zero on every fibre. -/
theorem hasDegreeZero_jacUniversalClass :
    HasDegreeZero B hX hk f σ hσ _ (jacUniversalClass B hX hk f σ hσ) :=
  (exists_classifyingMap_eq B hX hk f σ hσ (jacObj B hX hk f σ hσ) (𝟙 _)).choose_spec.choose

omit [IsAlgClosed k] in
/-- The classifying map of the universal class is the identity of `J`. -/
theorem classifyingMap_jacUniversalClass :
    classifyingMap B hX hk f σ hσ _ _ (hasDegreeZero_jacUniversalClass B hX hk f σ hσ) =
      𝟙 (jacobianGrp B hX hk f σ hσ).X :=
  (exists_classifyingMap_eq B hX hk f σ hσ (jacObj B hX hk f σ hσ) (𝟙 _)).choose_spec.choose_spec

/-- The constant family `{c₀} × T` on `X ×_k T`. -/
abbrev pointFamily (T : BigFppfOver B (Spec (.of k)) hk) : picardAt B hX hk f T :=
  picardMap B hX hk f (toPointObj B hX hk f T) (pointP B hX hk f σ hσ)

/-- **The theta family** `θ = -ξ + (g - 1)[c₀]` on `X ×_k J`. -/
abbrev thetaFamily : picardAt B hX hk f (jacObj B hX hk f σ hσ) :=
  -jacUniversalClass B hX hk f σ hσ +
    ((genus (B.inclusion.map f) : ℤ) - 1) • pointFamily B hX hk f σ hσ (jacObj B hX hk f σ hσ)

/-! ### Fibre degrees -/

/-- The fibre degree, as an additive map on classes. -/
def fibreDegreeHom (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : picardAt B hX hk f T →+ ℤ :=
  AddMonoidHom.mk' (fun x => curveFibreDegree B hX hk f σ hσ T (toPicardFunctorHom B hX hk f T x) t)
    fun x y => by
      simp only [curveFibreDegree]
      rw [map_add, fibreDegree_add]

omit [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- The fibre degree of the pullback of a class along `g : T' ⟶ T` at `t` is the fibre degree of
the class at the image of `t`. -/
theorem fibreDegree_picardMap {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (x : picardAt B hX hk f T) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T') :
    curveFibreDegree B hX hk f σ hσ T'
        (toPicardFunctorHom B hX hk f T' (picardMap B hX hk f g x)) t =
      curveFibreDegree B hX hk f σ hσ T (toPicardFunctorHom B hX hk f T x)
        (B.inclusion.map g.left t) := by
  simp only [curveFibreDegree, fibreDegree]
  rw [fibreEuler_zero, fibreEuler_zero, ← picardFunctor_map_toPicardFunctorHom]
  simp only [fibreEuler]
  rw [fibreRank_map, fibreRank_map]

omit [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- The point class has fibre degree one. -/
theorem fibreDegree_pointP (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj
    (powerObj B hX hk f 0)) :
    curveFibreDegree B hX hk f σ hσ _ (toPicardFunctorHom B hX hk f _ (pointP B hX hk f σ hσ)) t =
      1 := by
  have h := curveFibreDegree_familyClass B hX hk f σ hσ (powerObj B hX hk f 0)
    (graphFamily (curveOver B hX hk f) 0 (curvePowerZeroBasePoint B hX hk f σ hσ)) t
  exact_mod_cast h

omit [IsAlgClosed k] in
/-- **The theta family has fibre degree `g - 1`.** -/
theorem fibreDegree_thetaFamily (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj
    (jacObj B hX hk f σ hσ)) :
    fibreDegreeHom B hX hk f σ hσ _ t (thetaFamily B hX hk f σ hσ) =
      (genus (B.inclusion.map f) : ℤ) - 1 := by
  simp only [thetaFamily, map_add, map_neg, map_zsmul]
  have h0 : fibreDegreeHom B hX hk f σ hσ _ t (jacUniversalClass B hX hk f σ hσ) = 0 :=
    hasDegreeZero_jacUniversalClass B hX hk f σ hσ t
  have h1 : fibreDegreeHom B hX hk f σ hσ _ t
      (pointFamily B hX hk f σ hσ (jacObj B hX hk f σ hσ)) = 1 :=
    (fibreDegree_picardMap B hX hk f σ hσ _ _ t).trans (fibreDegree_pointP B hX hk f σ hσ _)
  rw [h0, h1]
  simp

omit [IsAlgClosed k] in
/-- **The theta family has fibre Euler characteristic zero**: `h⁰ = h¹` on every fibre. -/
theorem finrank_fibreCohomology_thetaFamily (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj
    (jacObj B hX hk f σ hσ)) :
    Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
        (jacObj B hX hk f σ hσ)).residueField t)
        (fibreCohomology (baseChangeProj B hX hk f _) (Stacks.PicardCurve.rep
          (thetaFamily B hX hk f σ hσ)) t 0) =
      Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
        (jacObj B hX hk f σ hσ)).residueField t)
        (fibreCohomology (baseChangeProj B hX hk f _) (Stacks.PicardCurve.rep
          (thetaFamily B hX hk f σ hσ)) t 1) := by
  have hd := fibreDegree_thetaFamily B hX hk f σ hσ t
  have he := fibreEuler_zero B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
    (jacObj B hX hk f σ hσ) t
  change fibreEuler B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) _
      (toPicardFunctorHom B hX hk f _ (thetaFamily B hX hk f σ hσ)) t -
    fibreEuler B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) _ 0 t =
      (genus (B.inclusion.map f) : ℤ) - 1 at hd
  rw [he] at hd
  have hE : fibreEuler B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) _
      (toPicardFunctorHom B hX hk f _ (thetaFamily B hX hk f σ hσ)) t = 0 := by omega
  rw [fibreEuler, fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom] at hE
  simp only [Stacks.PicardCurve.classFibreRank] at hE
  omega

/-! ### Classes on `C^1` read on the curve -/

/-- The map of test schemes `X ⟶ C^0`. -/
abbrev curveToPoint : curveObj B hX hk f ⟶ powerObj B hX hk f 0 :=
  toPointObj B hX hk f (curveObj B hX hk f)

/-- The projection `C^1 = X ×_k C^0 ⟶ X` is an isomorphism. -/
instance isIso_fst_power_zero :
    IsIso (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0)) := by
  change IsIso (fst (curveOver B hX hk f) (𝟙_ _))
  rw [← CartesianMonoidalCategory.rightUnitor_hom]
  infer_instance

/-- The isomorphism `X ⟶ C^1 = X ×_k C^0`. -/
abbrev fromCurve : X ⟶ (curveOver B hX hk f ⊗ power (curveOver B hX hk f) 0).left :=
  inv (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0)).left

/-- A class on `C^1`, read on `X`. -/
abbrev classOnX (w : picardAt B hX hk f (powerObj B hX hk f 0)) : Stacks.Picard.ofScheme X :=
  Stacks.Picard.schemePullbackClass (fromCurve B hX hk f) w

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- The base change of `X ⟶ C^0`, followed by the projection `C^1 ⟶ X`, is the first projection
`X ×_k X ⟶ X`. -/
theorem baseChangeMap_curveToPoint_fst :
    baseChangeMap B hX hk f (curveToPoint B hX hk f) ≫
        (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0)).left =
      pullback.fst (B.inclusion.map f) (B.inclusion.map f) := by
  change baseChangeMap B hX hk f (curveToPoint B hX hk f) ≫ pullback.fst _ _ = _
  rw [baseChangeMap, pullback.lift_fst, Category.comp_id]
  rfl

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- The base change of `X ⟶ C^0` is the first projection `X ×_k X ⟶ X` followed by the
isomorphism `X ⟶ C^1`. -/
theorem baseChangeMap_curveToPoint :
    baseChangeMap B hX hk f (curveToPoint B hX hk f) =
      pullback.fst (B.inclusion.map f) (B.inclusion.map f) ≫ fromCurve B hX hk f := by
  rw [← baseChangeMap_curveToPoint_fst, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- **Pulling a class on `C^1` back to `X ×_k X` along `X ⟶ C^0`** is pulling back its
reading on `X` along the first projection. -/
theorem picardMap_curveToPoint (w : picardAt B hX hk f (powerObj B hX hk f 0)) :
    picardMap B hX hk f (curveToPoint B hX hk f) w =
      Stacks.Picard.schemePullbackClass (pullback.fst (B.inclusion.map f) (B.inclusion.map f))
        (classOnX B hX hk f w) := by
  rw [picardMap, baseChangeMap_curveToPoint, ← Stacks.Picard.schemePullbackClass_comp]

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- The square formed by `X ⟶ C^1`, the structure maps of `X` and `C^1` over `k`, and the
identity of `Spec k` is a pullback. -/
theorem isPullback_fromCurve :
    IsPullback (fromCurve B hX hk f) (B.inclusion.map f)
      (baseChangeProj B hX hk f (powerObj B hX hk f 0)) (𝟙 (Spec (.of k))) := by
  have hid : IsIso (𝟙 (Spec (CommRingCat.of k))) := ⟨⟨𝟙 _, by simp, by simp⟩⟩
  refine @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance hid ⟨?_⟩
  have hc := pullback.condition (f := B.inclusion.map f)
    (g := B.inclusion.map (powerObj B hX hk f 0).hom)
  have h1 : fromCurve B hX hk f ≫ pullback.fst (B.inclusion.map f)
      (B.inclusion.map (powerObj B hX hk f 0).hom) = 𝟙 X :=
    IsIso.inv_hom_id (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0)).left
  have h2 : fromCurve B hX hk f ≫ (pullback.snd (B.inclusion.map f)
      (B.inclusion.map (powerObj B hX hk f 0).hom) ≫ B.inclusion.map (powerObj B hX hk f 0).hom) =
      B.inclusion.map f := by
    rw [← hc, ← Category.assoc, h1, Category.id_comp]
  have h3 : pullback.snd (B.inclusion.map f) (B.inclusion.map (powerObj B hX hk f 0).hom) ≫
      B.inclusion.map (powerObj B hX hk f 0).hom =
        pullback.snd (B.inclusion.map f) (B.inclusion.map (powerObj B hX hk f 0).hom) :=
    Category.comp_id _
  rw [h3] at h2
  exact h2.trans (Category.comp_id _).symm

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- **Normalized classes on `C^1` give normalized modules on `X`**, fibre by fibre. -/
theorem finrank_fibreCohomology_classOnX (w : picardAt B hX hk f (powerObj B hX hk f 0))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (powerObj B hX hk f 0)) (n : ℕ) :
    Module.finrank ((Spec (.of k)).residueField t)
        (fibreCohomology (B.inclusion.map f) (Stacks.PicardCurve.rep (classOnX B hX hk f w)) t n) =
      Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
          (powerObj B hX hk f 0)).residueField t)
        (fibreCohomology (baseChangeProj B hX hk f (powerObj B hX hk f 0))
          (Stacks.PicardCurve.rep w) t n) := by
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso (fromCurve B hX hk f) w
  exact finrank_fibreCohomology_eq_of_isPullback _ _ _ _ _ (isPullback_fromCurve B hX hk f) _ e t n

/-- **The point class pulled back to `X ×_k X` is the constant family `{c₀} × X`.** -/
theorem picardMap_curveToPoint_pointP :
    picardMap B hX hk f (curveToPoint B hX hk f) (pointP B hX hk f σ hσ) =
      (constantFamily B hX hk f σ hσ).picardClass := by
  have hy : (Over.post (X := B.obj hk) B.inclusion).map (curveToPoint B hX hk f) =
      toUnit ((Over.post (X := B.obj hk) B.inclusion).obj (curveObj B hX hk f)) :=
    Functor.FullyFaithful.map_preimage _ _
  have hb : baseChangeMap B hX hk f (curveToPoint B hX hk f) =
      Stacks.Hilbert.familyBaseChangeMap (curveOver B hX hk f)
        ((Over.post (X := B.obj hk) B.inclusion).map (curveToPoint B hX hk f)) := by
    rw [baseChangeMap_eq_lift, familyBaseChangeMap_eq]
  rw [picardMap, hb]
  have := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
    (power (curveOver B hX hk f) 0) (curvePowerZeroBasePoint B hX hk f σ hσ)
  refine Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass
    (graphFamily (curveOver B hX hk f) 0 (curvePowerZeroBasePoint B hX hk f σ hσ))
    (constantFamily B hX hk f σ hσ) _ ?_
  refine Eq.trans ?_ (Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap _ _ _).symm
  change Stacks.Hilbert.pointIdeal _ _ (constantPoint B hX hk f σ hσ) = _
  congr 1
  rw [hy]
  exact (Category.id_comp _).symm.trans (comp_constantPoint B hX hk f σ hσ (𝟙 _))

/-! ### The theta divisor and its pullbacks along `aj - x` -/

section Theta

variable (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The theta divisor** `Θ = Fit₀ R¹pr_* θ` on `J`. -/
abbrev thetaDivisor : (B.inclusion.obj (jacObj B hX hk f σ hσ).left).IdealSheafData :=
  Stacks.FamilyFitting.familyFitting (B.inclusion.map f) U hU hUaff
    (B.inclusion.map (jacObj B hX hk f σ hσ).hom)
    (Stacks.PicardCurve.rep (thetaFamily B hX hk f σ hσ))

/-- The theta divisor, as an ideal sheaf on the Jacobian. -/
abbrev thetaDivisorJ : (jacobianGrp B hX hk f σ hσ).X.left.IdealSheafData :=
  thetaDivisor B hX hk f σ hσ U hU hUaff

/-- `aj - x : X ⟶ J` for a `k`-point `x` of `J`. -/
abbrev ajSub (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    curveOver B hX hk f ⟶ (jacobianGrp B hX hk f σ hσ).X :=
  abelJacobi B hX hk f σ hσ * (toUnit (curveOver B hX hk f) ≫ x)⁻¹

/-- `aj - x` as a morphism of test schemes. -/
abbrev ajSubObj (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    curveObj B hX hk f ⟶ jacObj B hX hk f σ hσ :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage (ajSub B hX hk f σ hσ x)

end Theta

/-- The two morphisms `X ⟶ C^0` of test schemes agree. -/
theorem ajSubObj_comp_toPointObj
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    ajSubObj B hX hk f σ hσ x ≫ toPointObj B hX hk f (jacObj B hX hk f σ hσ) =
      curveToPoint B hX hk f :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).map_injective
    (Subsingleton.elim (α := _ ⟶ 𝟙_ (Over (Spec (.of k)))) _ _)

/-- The diagonal class `[Δ]` on `X ×_k X`. -/
abbrev diagCurveP : picardAt B hX hk f (curveObj B hX hk f) :=
  (diagonalFamily B hX hk f).picardClass

/-- The constant family class `[{c₀} × X]` on `X ×_k X`. -/
abbrev constCurveP : picardAt B hX hk f (curveObj B hX hk f) :=
  (constantFamily B hX hk f σ hσ).picardClass

/-- **The seesaw for `(aj - x)^* θ`**: it differs from `pr₁^* (z + g[c₀]) - [Δ]` by a class from
the base, when `z` has classifying map `x`. -/
theorem exists_picardMap_thetaFamily_sub
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X)
    (z : picardAt B hX hk f (powerObj B hX hk f 0)) (hz : HasDegreeZero B hX hk f σ hσ _ z)
    (hzx : classifyingMap B hX hk f σ hσ _ z hz = x) :
    ∃ n : Stacks.Picard.ofScheme X,
      Stacks.Picard.schemePullbackClass (baseChangeProj B hX hk f (curveObj B hX hk f)) n =
        picardMap B hX hk f (ajSubObj B hX hk f σ hσ x) (thetaFamily B hX hk f σ hσ) -
          (picardMap B hX hk f (curveToPoint B hX hk f)
              (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ) -
            diagCurveP B hX hk f) := by
  have hξ := hasDegreeZero_jacUniversalClass B hX hk f σ hσ
  have hP := hasDegreeZero_picardMap B hX hk f σ hσ (ajSubObj B hX hk f σ hσ x) hξ
  have hQ := hasDegreeZero_picardMap B hX hk f σ hσ (curveToPoint B hX hk f) hz
  have hR := hasDegreeZero_familyClass_sub B hX hk f σ hσ (curveObj B hX hk f)
    (diagonalFamily B hX hk f) (constantFamily B hX hk f σ hσ)
  have hcP : classifyingMap B hX hk f σ hσ _ _ hP = ajSub B hX hk f σ hσ x :=
    (classifyingMap_comp B hX hk f σ hσ (ajSubObj B hX hk f σ hσ x) _ hξ).symm.trans
      ((congrArg (fun m => (Over.post (X := B.obj hk) B.inclusion).map
          (ajSubObj B hX hk f σ hσ x) ≫ m) (classifyingMap_jacUniversalClass B hX hk f σ hσ)).trans
        ((Category.comp_id _).trans (Functor.FullyFaithful.map_preimage _ _)))
  have hcQ : classifyingMap B hX hk f σ hσ _ _ hQ = toUnit (curveOver B hX hk f) ≫ x :=
    (classifyingMap_comp B hX hk f σ hσ (curveToPoint B hX hk f) z hz).symm.trans
      ((congrArg (fun m => (Over.post (X := B.obj hk) B.inclusion).map
          (curveToPoint B hX hk f) ≫ m) hzx).trans
        (congrArg (fun m => m ≫ x) (Functor.FullyFaithful.map_preimage _ _)))
  have hcm : classifyingMap B hX hk f σ hσ _ (abelJacobiClass B hX hk f σ hσ) hR =
      classifyingMap B hX hk f σ hσ _ _ (hasDegreeZero_add B hX hk f σ hσ hP hQ) := by
    refine Eq.trans ?_ (classifyingMap_add B hX hk f σ hσ _ hP hQ).symm
    rw [hcP, hcQ]
    exact (inv_mul_cancel_right _ _).symm
  obtain ⟨n, hn⟩ := (classifyingMap_eq_classifyingMap_iff B hX hk f σ hσ _ hR
    (hasDegreeZero_add B hX hk f σ hσ hP hQ)).1 hcm
  refine ⟨n, hn.trans ?_⟩
  have hF : picardMap B hX hk f (ajSubObj B hX hk f σ hσ x)
      (pointFamily B hX hk f σ hσ (jacObj B hX hk f σ hσ)) = constCurveP B hX hk f σ hσ := by
    refine (picardMap_comp B hX hk f _ _ _).symm.trans ?_
    rw [ajSubObj_comp_toPointObj]
    exact picardMap_curveToPoint_pointP B hX hk f σ hσ
  have hθ : picardMap B hX hk f (ajSubObj B hX hk f σ hσ x) (thetaFamily B hX hk f σ hσ) =
      -picardMap B hX hk f (ajSubObj B hX hk f σ hσ x) (jacUniversalClass B hX hk f σ hσ) +
        ((genus (B.inclusion.map f) : ℤ) - 1) • constCurveP B hX hk f σ hσ := by
    rw [← hF]
    change picardMapHom B hX hk f _ (-_ + _ • _) = _
    rw [map_add, map_neg, map_zsmul]
    rfl
  have hw : picardMap B hX hk f (curveToPoint B hX hk f)
      (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ) =
      picardMap B hX hk f (curveToPoint B hX hk f) z +
        (genus (B.inclusion.map f) : ℤ) • constCurveP B hX hk f σ hσ := by
    rw [show constCurveP B hX hk f σ hσ = picardMap B hX hk f (curveToPoint B hX hk f)
      (pointP B hX hk f σ hσ) from (picardMap_curveToPoint_pointP B hX hk f σ hσ).symm]
    change picardMapHom B hX hk f _ (_ + _ • _) = _
    rw [map_add, map_zsmul]
    rfl
  rw [hθ, hw]
  change diagCurveP B hX hk f - constCurveP B hX hk f σ hσ - _ = _
  rw [sub_smul, one_smul]
  abel

/-- The chosen representative of a Picard class on a scheme is invertible. -/
instance isInvertible_rep_zeroScheme {Y : Scheme.{u}} (x : Stacks.Picard.ofScheme Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.PicardCurve.rep x) :=
  (Stacks.Picard.picardRepresentative Y.toRingedSpace x).property

section ThetaComap

variable (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- The ideal sheaf of the diagonal of `X ×_k X` is an effective Cartier divisor. -/
instance isEffectiveCartierDivisor_diagIdeal :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.FamilyFitting.diagIdeal (B.inclusion.map f)) :=
  (diagonalFamily B hX hk f).isEffectiveCartierDivisor_ideal

/-- **The theta divisor pulls back to the divisor of the section** along `aj - x`, when
`z_x + g[c₀]` is normalized with nonzero section `s`. -/
theorem thetaDivisor_comap
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X)
    (z : picardAt B hX hk f (powerObj B hX hk f 0)) (hz : HasDegreeZero B hX hk f σ hσ _ z)
    (hzx : classifyingMap B hX hk f σ hσ _ z hz = x)
    (hN : ∀ t, Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
          (powerObj B hX hk f 0)).residueField t)
        (fibreCohomology (baseChangeProj B hX hk f _) (Stacks.PicardCurve.rep
          (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)) t 1) = 0 ∧
      Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
          (powerObj B hX hk f 0)).residueField t)
        (fibreCohomology (baseChangeProj B hX hk f _) (Stacks.PicardCurve.rep
          (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)) t 0) = 1)
    (s : Γ(Stacks.PicardCurve.rep (classOnX B hX hk f
      (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)), ⊤)) (hs : s ≠ 0) :
    (thetaDivisorJ B hX hk f σ hσ U hU hUaff).comap (ajSub B hX hk f σ hσ x).left =
      AlgebraicGeometry.zeroScheme X (Stacks.PicardCurve.rep (classOnX B hX hk f
        (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ))) s := by
  rw [show (ajSub B hX hk f σ hσ x).left = B.inclusion.map (ajSubObj B hX hk f σ hσ x).left from
    (congrArg Over.Hom.left
      ((fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).map_preimage
        (X := curveObj B hX hk f) (Y := jacObj B hX hk f σ hσ) (ajSub B hX hk f σ hσ x))).symm]
  have : IsSeparated (B.inclusion.map f) := inferInstance
  have : SmoothOfRelativeDimension 1 (B.inclusion.map f) :=
    smoothOfRelativeDimension_one_of_isCurve k _
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso
    (baseChangeMap B hX hk f (ajSubObj B hX hk f σ hσ x)) (thetaFamily B hX hk f σ hσ)
  have htT : B.inclusion.map (ajSubObj B hX hk f σ hσ x).left ≫
      B.inclusion.map (jacObj B hX hk f σ hσ).hom = B.inclusion.map f :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w _))
  refine (Stacks.FamilyFitting.familyFitting_comap (B.inclusion.map f) U hU hUaff _ _
    (B.inclusion.map f) _ htT _ e.symm).trans ?_
  obtain ⟨n, hn⟩ := exists_picardMap_thetaFamily_sub B hX hk f σ hσ x z hz hzx
  have hA : picardMap B hX hk f (ajSubObj B hX hk f σ hσ x) (thetaFamily B hX hk f σ hσ) =
      (picardMap B hX hk f (curveToPoint B hX hk f)
          (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ) - diagCurveP B hX hk f) +
        Stacks.Picard.schemePullbackClass (baseChangeProj B hX hk f (curveObj B hX hk f)) n := by
    rw [hn]; abel
  change Stacks.FamilyFitting.familyFitting (B.inclusion.map f) U hU hUaff (B.inclusion.map f)
    (Stacks.PicardCurve.rep (picardMap B hX hk f (ajSubObj B hX hk f σ hσ x)
      (thetaFamily B hX hk f σ hσ))) = _
  rw [hA]
  refine (Stacks.FamilyFitting.familyFitting_rep_add_pullback (B.inclusion.map f) U hU hUaff
    (B.inclusion.map f) _ n).trans ?_
  refine Stacks.FamilyFitting.familyFitting_diag_eq_zeroScheme (B.inclusion.map f) U hU hUaff
    (Stacks.PicardCurve.rep (classOnX B hX hk f _)) s hs
    (fun t => (finrank_fibreCohomology_classOnX B hX hk f _ t 1).trans (hN t).1)
    (fun t => (finrank_fibreCohomology_classOnX B hX hk f _ t 0).trans (hN t).2) _ ?_
  refine Eq.trans ?_ (congrArg (Stacks.Picard.schemePullbackClass
    (pullback.fst (B.inclusion.map f) (B.inclusion.map f)))
      (Stacks.Picard.classOf_picardRepresentative _ _).symm)
  refine (sub_add_cancel _ _).trans ?_
  exact picardMap_curveToPoint B hX hk f _

end ThetaComap

/-! ### Auxiliary facts on sections and supports -/

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
/-- **A module on `X` with one-dimensional `H⁰` on its fibre over `k` has a nonzero section.** -/
theorem exists_section_ne_zero (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens)
    (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (fibreCohomology (B.inclusion.map f) N t 1) = 0)
    (h0 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (fibreCohomology (B.inclusion.map f) N t 0) = 1) :
    ∃ s : Γ(N, ⊤), s ≠ 0 := by
  classical
  have : N.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule N
  have : IsSeparated (B.inclusion.map f) := inferInstance
  by_contra hall
  push Not at hall
  have hk : IsPullback (𝟙 X) (B.inclusion.map f) (B.inclusion.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from rfl, Spec.map_id]
    have hid : IsIso (𝟙 (Spec (CommRingCat.of k))) := ⟨⟨𝟙 _, by simp, by simp⟩⟩
    have hidX : IsIso (𝟙 X) := ⟨⟨𝟙 _, by simp, by simp⟩⟩
    exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hidX hid
      ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩
  have hd : Function.Surjective (Stacks.TwoAffineCech.cechD (B.inclusion.map f) U N) :=
    Stacks.TwoAffineCech.surjective_cechD_of_isPullback (B.inclusion.map f) U hU hUaff
      (𝟙 X) (B.inclusion.map f) hk N h1
  have hker : ∀ c : LinearMap.ker (Stacks.TwoAffineCech.cechD (B.inclusion.map f) U N), c = 0 := by
    intro c
    obtain ⟨t, rfl⟩ := Stacks.TwoAffineCech.exists_sectionCocycle_eq (B.inclusion.map f) U N hU c
    rw [hall t]
    exact Subtype.ext (Subtype.ext (Stacks.TwoAffineCech.sectionCochain_zero U N))
  have : Subsingleton (LinearMap.ker (Stacks.TwoAffineCech.cechD (B.inclusion.map f) U N)) :=
    ⟨fun a b => (hker a).trans (hker b).symm⟩
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := Stacks.TwoAffineCech.finrank_cohomologyOverField_zero_eq (B.inclusion.map f) U N hU
    hUaff p
  rw [Stacks.TwoAffineCech.finrank_fibre_eq_fibreCohomology] at h
  have e1 := h0 (Stacks.TwoAffineCech.specPoint p)
  have e2 := (Stacks.TwoTermComplex.baseChangeKerEquiv _ hd p.asIdeal.ResidueField).finrank_eq
  have e3 : Module.finrank p.asIdeal.ResidueField (TensorProduct k p.asIdeal.ResidueField
      (LinearMap.ker (Stacks.TwoAffineCech.cechD (B.inclusion.map f) U N))) = 0 :=
    Module.finrank_zero_of_subsingleton
  exact one_ne_zero (e1.symm.trans (h.trans (e2.symm.trans e3)))

/-- An effective Cartier divisor on a nonempty integral scheme is not supported everywhere. -/
theorem exists_not_mem_support {Y : Scheme.{u}} [IsIntegral Y] (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] : ∃ y : Y, y ∉ D.support := by
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  obtain ⟨V, hy₀, g, hg, hgen⟩ :=
    (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor D).1
      inferInstance y₀
  have : Nonempty V.1 := ⟨⟨y₀, hy₀⟩⟩
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  have hne : Y.basicOpen g ≠ ⊥ := fun h => hg0 ((basicOpen_eq_bot_iff g).1 h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  refine ⟨y, fun hmem => ?_⟩
  have hyV : y ∈ V.1 := Y.basicOpen_le g hy
  have h := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hyV).1 hmem
  rw [hgen, Scheme.mem_zeroLocus_iff] at h
  exact h g (Ideal.mem_span_singleton_self g) hy

/-! ### The polarization `𝒪(Θ)` -/

section Polarization

variable (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- The normalization hypothesis on `z + g[c₀]`, on the fibre of `C^1 ⟶ C^0`. -/
abbrev NormalizedAt (w : picardAt B hX hk f (powerObj B hX hk f 0)) : Prop :=
  ∀ t, Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
          (powerObj B hX hk f 0)).residueField t)
        (fibreCohomology (baseChangeProj B hX hk f _) (Stacks.PicardCurve.rep w) t 1) = 0 ∧
      Module.finrank (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
          (powerObj B hX hk f 0)).residueField t)
        (fibreCohomology (baseChangeProj B hX hk f _) (Stacks.PicardCurve.rep w) t 0) = 1

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] [IsAlgClosed k] in
include U hU hUaff in
/-- If `w` is normalized, its reading on `X` has a nonzero global section. -/
theorem exists_section_classOnX (w : picardAt B hX hk f (powerObj B hX hk f 0))
    (hN : NormalizedAt B hX hk f w) :
    ∃ s : Γ(Stacks.PicardCurve.rep (classOnX B hX hk f w), ⊤), s ≠ 0 :=
  exists_section_ne_zero B hX hk f U hU hUaff _
    (fun t => (finrank_fibreCohomology_classOnX B hX hk f w t 1).trans (hN t).1)
    (fun t => (finrank_fibreCohomology_classOnX B hX hk f w t 0).trans (hN t).2)

/-- For normalized `z + g[c₀]`, the pullback of `Θ` along `aj - x` is the effective Cartier divisor
of a nonzero section. -/
private theorem exists_comap_thetaDivisor_eq_zeroScheme
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X)
    (z : picardAt B hX hk f (powerObj B hX hk f 0)) (hz : HasDegreeZero B hX hk f σ hσ _ z)
    (hzx : classifyingMap B hX hk f σ hσ _ z hz = x)
    (hN : NormalizedAt B hX hk f (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)) :
    ∃ (s : Γ(Stacks.PicardCurve.rep (classOnX B hX hk f
        (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)), ⊤)) (_ : s ≠ 0),
      (thetaDivisorJ B hX hk f σ hσ U hU hUaff).comap (ajSub B hX hk f σ hσ x).left =
        AlgebraicGeometry.zeroScheme X (Stacks.PicardCurve.rep (classOnX B hX hk f
          (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ))) s ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (AlgebraicGeometry.zeroScheme X
        (Stacks.PicardCurve.rep (classOnX B hX hk f
          (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ))) s) := by
  obtain ⟨s, hs⟩ := exists_section_classOnX B hX hk f U hU hUaff _ hN
  exact ⟨s, hs, thetaDivisor_comap B hX hk f σ hσ U hU hUaff x z hz hzx hN s hs,
    AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero _ s hs⟩

/-- **`Θ` is an effective Cartier divisor**, given one `k`-point `x` with `z_x + g[c₀]`
normalized. -/
theorem isEffectiveCartierDivisor_thetaDivisor
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X)
    (z : picardAt B hX hk f (powerObj B hX hk f 0)) (hz : HasDegreeZero B hX hk f σ hσ _ z)
    (hzx : classifyingMap B hX hk f σ hσ _ z hz = x)
    (hN : NormalizedAt B hX hk f (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (thetaDivisorJ B hX hk f σ hσ U hU hUaff) := by
  have : IsIntegral (B.inclusion.obj (jacObj B hX hk f σ hσ).left) :=
    (inferInstance : IsIntegral (jacobianGrp B hX hk f σ hσ).X.left)
  obtain ⟨s, hs, hcomap, this⟩ :=
    exists_comap_thetaDivisor_eq_zeroScheme B hX hk f σ hσ U hU hUaff x z hz hzx hN
  obtain ⟨c, hc⟩ := exists_not_mem_support (AlgebraicGeometry.zeroScheme X _ s)
  refine Stacks.FamilyFitting.isEffectiveCartierDivisor_familyFitting (B.inclusion.map f) U hU hUaff
    (B.inclusion.map (jacObj B hX hk f σ hσ).hom)
    (Stacks.PicardCurve.rep (thetaFamily B hX hk f σ hσ))
    (finrank_fibreCohomology_thetaFamily B hX hk f σ hσ)
    ⟨(ajSub B hX hk f σ hσ x).left c, fun hmem => hc ?_⟩
  rw [← hcomap, Scheme.IdealSheafData.support_comap]
  exact hmem

/-- `aj - x` on `C^1 = C ⊗ C^0` is `aj ∘ pr_C - x`. -/
theorem ajOne_add_pointConst_inv
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    ajOne B hX hk f σ hσ + pointConst B hX hk f σ hσ x⁻¹ =
      Additive.ofMul (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0) ≫
        ajSub B hX hk f σ hσ x) := by
  change Additive.ofMul (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0) ≫
      abelJacobi B hX hk f σ hσ * snd _ _ ≫ x⁻¹) = _
  congr 1
  rw [ajSub, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
  exact congrArg (fun m => (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0) ≫
      abelJacobi B hX hk f σ hσ) * m⁻¹)
    ((congrArg (fun m => m ≫ x) (Subsingleton.elim (α := _ ⟶ 𝟙_ (Over (Spec (.of k))))
      (snd (curveOver B hX hk f) (power (curveOver B hX hk f) 0))
      (fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0) ≫
        toUnit (curveOver B hX hk f)))).trans (Category.assoc _ _ _))

/-- **`(aj - x)^* 𝒪(Θ) = z + g[c₀]`** for `x` with `z + g[c₀]` normalized. -/
theorem classQ_thetaDivisor
    [hΘ : Stacks.Divisors.IsEffectiveCartierDivisor (thetaDivisorJ B hX hk f σ hσ U hU hUaff)]
    (x : power (curveOver B hX hk f) 0 ⟶ (jacobianGrp B hX hk f σ hσ).X)
    (z : picardAt B hX hk f (powerObj B hX hk f 0)) (hz : HasDegreeZero B hX hk f σ hσ _ z)
    (hzx : classifyingMap B hX hk f σ hσ _ z hz = x)
    (hN : NormalizedAt B hX hk f (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ)) :
    classQ (jacobianGrp B hX hk f σ hσ).X
        (Stacks.Divisors.invertibleSheaf' (thetaDivisorJ B hX hk f σ hσ U hU hUaff))
        (Stacks.Divisors.isInvertible_invertibleSheaf_picard
          (thetaDivisorJ B hX hk f σ hσ U hU hUaff))
        (ajOne B hX hk f σ hσ + pointConst B hX hk f σ hσ x⁻¹) =
      z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ := by
  obtain ⟨s, hs, hcomap, hZe⟩ :=
    exists_comap_thetaDivisor_eq_zeroScheme B hX hk f σ hσ U hU hUaff x z hz hzx hN
  have := hZe
  have hcE : Stacks.Divisors.IsEffectiveCartierDivisor
      ((thetaDivisorJ B hX hk f σ hσ U hU hUaff).comap (ajSub B hX hk f σ hσ x).left) := by
    rw [hcomap]
    exact hZe
  have : Stacks.Divisors.IsPullbackDefined (ajSub B hX hk f σ hσ x).left
      (thetaDivisorJ B hX hk f σ hσ U hU hUaff) := hcE
  rw [ajOne_add_pointConst_inv]
  change Stacks.SheafOfModules.pullbackPicardClass
      ((fst (curveOver B hX hk f) (power (curveOver B hX hk f) 0)).left ≫
        (ajSub B hX hk f σ hσ x).left) _ _ = _
  have hpb : Stacks.SheafOfModules.pullbackPicardClass (ajSub B hX hk f σ hσ x).left
      (Stacks.Divisors.invertibleSheaf' (thetaDivisorJ B hX hk f σ hσ U hU hUaff))
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard
        (thetaDivisorJ B hX hk f σ hσ U hU hUaff)) =
      Stacks.Picard.schemePullbackClass (ajSub B hX hk f σ hσ x).left
        (Stacks.Divisors.picardClass (thetaDivisorJ B hX hk f σ hσ U hU hUaff)) := by
    have e1 := schemePullbackClass_pullbackPicardClass (ajSub B hX hk f σ hσ x).left (𝟙 _)
      (Stacks.Divisors.invertibleSheaf' (thetaDivisorJ B hX hk f σ hσ U hU hUaff))
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard
        (thetaDivisorJ B hX hk f σ hσ U hU hUaff))
    rw [Category.comp_id, Stacks.SheafOfModules.pullbackPicardClass_id] at e1
    exact e1.symm
  rw [← schemePullbackClass_pullbackPicardClass, hpb,
    Stacks.Divisors.schemePullbackClass_picardClass]
  have hZ : @Stacks.Divisors.picardClass _
      ((thetaDivisorJ B hX hk f σ hσ U hU hUaff).comap (ajSub B hX hk f σ hσ x).left) hcE =
      classOnX B hX hk f (z + (genus (B.inclusion.map f) : ℤ) • pointP B hX hk f σ hσ) :=
    (@Stacks.Divisors.picardClass_congr _ _ _ hcomap hcE hZe).trans
      ((@AlgebraicGeometry.picardClass_zeroScheme _ _
        (Stacks.Picard.picardRepresentative _ _).property _ s hZe).trans
          (Stacks.Picard.classOf_picardRepresentative _ _))
  rw [hZ, classOnX, Stacks.Picard.schemePullbackClass_comp, IsIso.hom_inv_id,
    Stacks.Picard.schemePullbackClass_id]

end Polarization

end Stacks.PicardFunctor

end
