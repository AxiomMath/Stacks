module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.ReductionTypes
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SmoothPlaneConic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicModel
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.StacksAttribute

/-!
# The conic `T₁² + T₂² = πT₀²` over `ℝ[[π]]`

Let `R = ℝ[[π]]` and `X = V(T₁² + T₂² - πT₀²) ⊆ ℙ²_R`. This file proves the claims of
[Stacks, Tag 0CDL] about `X`.

* Its base change to `ℂ[[π]]` is the scheme `V(T₁T₂ - πT₀²)` of [Stacks, Tag 0CA0], because
  `T₁² + T₂² = (T₁ + iT₂)(T₁ - iT₂)` over `ℂ`.
* `X` is regular.
* Its special fibre is irreducible yet singular.
* `X` is a regular proper model of its generic fibre, the smooth projective conic
  `V(T₁² + T₂² - πT₀²) ⊆ ℙ²_K`, with `H⁰ = K` and genus `0`.
* `X` is a minimal model, its special fibre being irreducible ([Stacks, Tag 0CA6]), and the
  unique one: otherwise its special fibre would be `ℙ¹` ([Stacks, Tag 0CDA]) and `X` smooth.
* The generic fibre does not have good reduction over `R` ([Stacks, Tag 0CDI]), so an extension
  of `R` is needed even in genus `0`.

More generally, the second, third and fourth facts hold over any discrete valuation ring `R`
with uniformizer `π` in which `2` is invertible and in whose residue field `-1` is not a square.

## Main definitions

* `Stacks.Models.RealConicModel.situation`: `X` as a regular proper model of its generic fibre,
  in the standing situation `Stacks.Models.RegularProperModelSituation` of [Stacks, Tag 0C61].

## Main results

* `Stacks.Models.RealConicModel.isPullback_complexification`: the base change to `ℂ[[π]]`.
* `Stacks.Models.RealConicModel.isRegular_powerSeries`: `X` is regular.
* `Stacks.Models.RealConicModel.irreducibleSpace_specialFiber_powerSeries` and
  `Stacks.Models.RealConicModel.not_isRegular_specialFiber_powerSeries`: the special fibre is
  irreducible and singular.
* `Stacks.Models.RegularProperModelSituation.isMinimalModel_of_irreducibleSpace`: a regular
  proper model with irreducible special fibre is minimal.
* `Stacks.Models.RealConicModel.isMinimalModel_powerSeries`,
  `Stacks.Models.RealConicModel.exists_iso_of_isMinimalModel_powerSeries`: `X` is the unique
  minimal model.
* `Stacks.Models.RealConicModel.not_hasGoodReduction_powerSeries`: no good reduction over `R`.
* `Stacks.Models.RealConicModel.realConic_example`: [Stacks, Tag 0CDL].

## References

* [Stacks Project, Tag 0CDL](https://stacks.math.columbia.edu/tag/0CDL)
* [Stacks Project, Tag 0CA0](https://stacks.math.columbia.edu/tag/0CA0)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0CA6](https://stacks.math.columbia.edu/tag/0CA6)
* [Stacks Project, Tag 0CDA](https://stacks.math.columbia.edu/tag/0CDA)
* [Stacks Project, Tag 0CDI](https://stacks.math.columbia.edu/tag/0CDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Models.RealConicModel

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The conic as a regular proper model -/

section Situation

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The image of a uniformizer `π` of `R` in the fraction field `K` is nonzero. -/
theorem algebraMap_ne_zero (hπ : Irreducible π) : algebraMap R K π ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- If `2` is a unit in `R`, then `2 ≠ 0` in the fraction field `K`. -/
theorem two_ne_zero_of_isUnit (h2 : IsUnit (2 : R)) : (2 : K) ≠ 0 := by
  have h := h2.map (algebraMap R K)
  rw [map_ofNat] at h
  exact h.ne_zero

/-- The generic fibre of `X = V(T₁² + T₂² - πT₀²)` is the conic `V(T₁² + T₂² - πT₀²) ⊆ ℙ²_K`. -/
def genericFiberIso (π : R) :
    scheme (algebraMap R K π) ≅
      pullback (toSpec π) (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  PlaneCurveModel.schemeCongr (isHomogeneous_equation _) ((isHomogeneous_equation π).map _)
      (map_equation _ π).symm ≪≫
    (PlaneCurveModel.isPullback_mapMap (equation π) (isHomogeneous_equation π)
      (algebraMap R K)).isoPullback

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The identification `genericFiberIso` of the generic fibre is compatible with the structure
morphisms to `Spec K`. -/
theorem genericFiberIso_hom_snd (π : R) :
    (genericFiberIso K π).hom ≫
        pullback.snd (toSpec π) (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      toSpec (algebraMap R K π) := by
  rw [genericFiberIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd,
    PlaneCurveModel.schemeCongr_hom_toSpec]

variable (hπ : Irreducible π) (h2 : IsUnit (2 : R))

/-- **`X = V(T₁² + T₂² - πT₀²)` is a regular proper model of its generic fibre**, a smooth
projective curve with `H⁰ = K`: the standing situation of [Stacks, Tag 0C61]. -/
def situation : RegularProperModelSituation.{u} :=
  have := isCurve_toSpec (algebraMap_ne_zero K hπ) (two_ne_zero_of_isUnit K h2)
  have := smooth_toSpec (algebraMap_ne_zero K hπ) (two_ne_zero_of_isUnit K h2)
  have := isIso_globalSections (algebraMap R K π)
  have := flat_toSpec hπ
  { R := R, K := K, k := IsLocalRing.ResidueField R, residueEquiv := AlgEquiv.refl
    C := scheme (algebraMap R K π), C_to_K := toSpec (algebraMap R K π)
    X := scheme π, X_to_R := toSpec π
    regular := isRegular_scheme hπ h2
    genericFiberIso := genericFiberIso K π
    genericFiberIso_over_K := genericFiberIso_hom_snd K π
    π := π, uniformizer := hπ
    curveProjective := isHProjective_toSpec _ }

/-- The model in `situation` is `X = V(T₁² + T₂² - πT₀²)`. -/
theorem situation_X : (situation K hπ h2).X = scheme π := rfl

/-- The structure morphism of the model in `situation` is `X ⟶ Spec R`. -/
theorem situation_X_to_R : (situation K hπ h2).X_to_R = toSpec π := rfl

end Situation

/-! ### `ℝ[[π]]` -/

section PowerSeries

/-- `2` is a unit in `ℝ[[π]]`. -/
theorem isUnit_two_powerSeries : IsUnit (2 : PowerSeries ℝ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, map_ofNat]
  exact isUnit_iff_ne_zero.mpr two_ne_zero

/-- In the residue field `ℝ` of `ℝ[[π]]`, `-1` is not a square. -/
theorem not_sq_eq_neg_one_residueField (c : IsLocalRing.ResidueField (PowerSeries ℝ)) :
    c ^ 2 ≠ -1 := by
  intro hc
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective c
  have hmem : b ^ 2 + 1 ∈ IsLocalRing.maximalIdeal (PowerSeries ℝ) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_add, map_pow, map_one, hc, neg_add_cancel]
  refine (IsLocalRing.mem_maximalIdeal _).mp hmem ?_
  rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_pow, map_one]
  exact isUnit_iff_ne_zero.mpr (by positivity)

/-- The uniformizer `π` of `ℝ[[π]]` maps to `0` in the residue field. -/
theorem algebraMap_X_residueField :
    algebraMap (PowerSeries ℝ) (IsLocalRing.ResidueField (PowerSeries ℝ)) PowerSeries.X = 0 := by
  have h : IsLocalRing.maximalIdeal (PowerSeries ℝ) = Ideal.span {PowerSeries.X} :=
    Irreducible.maximalIdeal_eq (PowerSeries.X_irreducible (R := ℝ))
  refine (IsLocalRing.residue_eq_zero_iff _).mpr ?_
  rw [h]
  exact Ideal.mem_span_singleton_self _

/-- **`X = V(T₁² + T₂² - πT₀²) ⊆ ℙ²_{ℝ[[π]]}` is regular.** -/
theorem isRegular_powerSeries : IsRegular (scheme (PowerSeries.X : PowerSeries ℝ)) :=
  isRegular_scheme PowerSeries.X_irreducible isUnit_two_powerSeries

/-- **The special fibre of `X` is irreducible.** -/
theorem irreducibleSpace_specialFiber_powerSeries :
    IrreducibleSpace (specialFiber (PowerSeries.X : PowerSeries ℝ)
      (IsLocalRing.ResidueField (PowerSeries ℝ))) :=
  irreducibleSpace_specialFiber _ _ algebraMap_X_residueField not_sq_eq_neg_one_residueField

/-- **The special fibre of `X` is singular.** -/
theorem not_isRegular_specialFiber_powerSeries :
    ¬ IsRegular (specialFiber (PowerSeries.X : PowerSeries ℝ)
      (IsLocalRing.ResidueField (PowerSeries ℝ))) :=
  not_isRegular_specialFiber _ _ algebraMap_X_residueField

/-- **`X` is not smooth over `ℝ[[π]]`**: its special fibre would be smooth over `ℝ`, hence
regular. -/
theorem not_smooth_powerSeries : ¬ Smooth (toSpec (PowerSeries.X : PowerSeries ℝ)) := by
  intro h
  exact not_isRegular_specialFiber_powerSeries (isRegular_of_smooth_over_field
    (pullback.snd (toSpec (PowerSeries.X : PowerSeries ℝ))
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ)
        (IsLocalRing.ResidueField (PowerSeries ℝ)))))))

/-- `i ∈ ℂ[[π]]`. -/
abbrev iPowerSeries : PowerSeries ℂ := algebraMap ℂ (PowerSeries ℂ) Complex.I

/-- `1/2 ∈ ℂ[[π]]`. -/
abbrev halfPowerSeries : PowerSeries ℂ := algebraMap ℂ (PowerSeries ℂ) (1 / 2)

/-- `i² = -1` in `ℂ[[π]]`. -/
theorem iPowerSeries_sq : iPowerSeries ^ 2 = -1 := by
  rw [iPowerSeries, ← map_pow, Complex.I_sq, map_neg, map_one]

/-- `2 · (1/2) = 1` in `ℂ[[π]]`. -/
theorem two_mul_halfPowerSeries : 2 * halfPowerSeries = 1 := by
  rw [halfPowerSeries, show (2 : PowerSeries ℂ) = algebraMap ℂ (PowerSeries ℂ) 2 from
    (map_ofNat _ 2).symm, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

/-- The inclusion `ℝ[[π]] → ℂ[[π]]` sends the variable `π` to `π`. -/
theorem algebraMap_powerSeries_X :
    algebraMap (PowerSeries ℝ) (PowerSeries ℂ) PowerSeries.X = PowerSeries.X :=
  PowerSeries.map_X _

/-- **The base change of `X` to `ℂ[[π]]` is `V(T₁T₂ - πT₀²)`**, the scheme of
[Stacks, Tag 0CA0]: the square formed by the morphism `V(T₁T₂ - πT₀²) ⟶ X` induced by
`T₁ ↦ (T₁ + T₂)/2`, `T₂ ↦ -i(T₁ - T₂)/2`, the two structure morphisms and
`Spec ℂ[[π]] ⟶ Spec ℝ[[π]]` is cartesian. -/
theorem isPullback_complexification :
    IsPullback (splitMap PowerSeries.X (algebraMap (PowerSeries ℝ) (PowerSeries ℂ))
        iPowerSeries_sq two_mul_halfPowerSeries
        (GenusZero.isHomogeneous_conicEquation (PowerSeries.X : PowerSeries ℂ))
        (by rw [algebraMap_powerSeries_X]; rfl) ≫
        PlaneCurveModel.mapMap (equation PowerSeries.X) (isHomogeneous_equation _)
          (algebraMap (PowerSeries ℝ) (PowerSeries ℂ)))
      (GenusZero.conicToSpec (PowerSeries.X : PowerSeries ℂ))
      (toSpec (PowerSeries.X : PowerSeries ℝ))
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) (PowerSeries ℂ)))) :=
  isPullback_split _ _ _ _ _ _

end PowerSeries

/-! ### Minimality -/

/-- **A regular proper model whose special fibre is irreducible is a minimal model.** Its
numerical type has a single component; the multiplicity vector is annihilated by the
intersection matrix, so the self-intersection of that component vanishes and it is not a
`(-1)`-index. The numerical type is minimal, hence so is the model ([Stacks, Tag 0CA6]). -/
theorem _root_.Stacks.Models.RegularProperModelSituation.isMinimalModel_of_irreducibleSpace
    (S : RegularProperModelSituation.{u}) [IrreducibleSpace S.specialFiber] :
    IsMinimalModel S.C_to_K S.X_to_R S.genericFiberIso := by
  classical
  have hcomp : irreducibleComponents S.specialFiber = {Set.univ} :=
    irreducibleComponents_eq_singleton
  let eC : Fin 1 ≃ irreducibleComponents S.specialFiber :=
    { toFun := fun _ ↦ ⟨Set.univ, by rw [hcomp]; rfl⟩
      invFun := fun _ ↦ 0
      left_inv := fun i ↦ Subsingleton.elim _ _
      right_inv := fun Z ↦ by
        obtain ⟨Z, hZ⟩ := Z
        rw [hcomp] at hZ
        exact Subtype.ext hZ.symm }
  refine S.isMinimalModel_of_isMinimal_associatedNumericalType 1 eC ?_
  rintro ⟨i, -, hi⟩
  have hsum := (S.associatedNumericalType 1 eC).intersection_mul_multiplicity i
  have hi0 : ∀ j : Fin (S.associatedNumericalType 1 eC).componentCount, j = i := fun j ↦
    Fin.ext (by have h₁ : j.val < 1 := j.2; have h₂ : i.val < 1 := i.2; omega)
  rw [Fintype.sum_eq_single i (fun j hj ↦ absurd (hi0 j) hj)] at hsum
  have hm := (S.associatedNumericalType 1 eC).multiplicity_pos i
  have hw := (S.associatedNumericalType 1 eC).weight_pos i
  rcases mul_eq_zero.mp hsum with h | h
  · rw [h] at hi
    linarith
  · linarith

section PowerSeriesModel

variable (K : Type) [Field K] [Algebra (PowerSeries ℝ) K] [IsFractionRing (PowerSeries ℝ) K]

/-- The generic fibre of `X` is a curve over `K`. -/
instance isCurve_toSpec_powerSeries :
    IsCurve K (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X)) :=
  isCurve_toSpec (algebraMap_ne_zero K PowerSeries.X_irreducible)
    (two_ne_zero_of_isUnit K isUnit_two_powerSeries)

/-- The generic fibre of `X` is smooth over `K`. -/
instance smooth_toSpec_powerSeries : Smooth (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X)) :=
  smooth_toSpec (algebraMap_ne_zero K PowerSeries.X_irreducible)
    (two_ne_zero_of_isUnit K isUnit_two_powerSeries)

/-- `H⁰ = K` for the generic fibre of `X`. -/
instance isIso_globalSections_powerSeries :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X)).appTop) :=
  isIso_globalSections _

/-- **`X` is a minimal model of its generic fibre**: its special fibre is irreducible. -/
theorem isMinimalModel_powerSeries :
    IsMinimalModel (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X))
      (toSpec (PowerSeries.X : PowerSeries ℝ)) (genericFiberIso K PowerSeries.X) := by
  have : IrreducibleSpace
      (situation K PowerSeries.X_irreducible isUnit_two_powerSeries).specialFiber :=
    irreducibleSpace_specialFiber_powerSeries
  exact RegularProperModelSituation.isMinimalModel_of_irreducibleSpace
    (situation K PowerSeries.X_irreducible isUnit_two_powerSeries)

/-- **`X` is the unique minimal model of its generic fibre**: every minimal model `Y` is
isomorphic to `X` as a model, over `ℝ[[π]]` and compatibly with the identifications of the generic
fibres. Otherwise the special fibre of `X` would be `ℙ¹` over the residue field
([Stacks, Tag 0CDA]), so `X` would be smooth over `ℝ[[π]]`. -/
theorem exists_iso_of_isMinimalModel_powerSeries {Y : Scheme.{0}}
    (pY : Y ⟶ Spec (.of (PowerSeries ℝ)))
    (eY : scheme (algebraMap (PowerSeries ℝ) K PowerSeries.X) ≅
      pullback pY (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) K))))
    (hY : IsMinimalModel (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X)) pY eY) :
    ∃ φ : scheme (PowerSeries.X : PowerSeries ℝ) ≅ Y,
      φ.hom ≫ pY = toSpec (PowerSeries.X : PowerSeries ℝ) ∧
      (genericFiberIso K PowerSeries.X).hom ≫
          pullback.fst (toSpec (PowerSeries.X : PowerSeries ℝ))
            (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) K))) ≫ φ.hom =
        eY.hom ≫ pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) K))) := by
  by_contra h
  have hX := isMinimalModel_powerSeries K
  have hP := isProjectiveLineSpecialFiber_of_isMinimalModel _ (isHProjective_toSpec _)
    inferInstance (genus_toSpec _) ⟨_, Y, _, pY, _, eY, hX, hY, h⟩ _ _ hX
  exact not_smooth_powerSeries
    (smooth_and_isAtWorstNodal_of_isProjectiveLineSpecialFiber _ _ _ hX hP).1

omit [IsFractionRing (PowerSeries ℝ) K] in
/-- The generic fibre of `X` is projective over `K`. -/
theorem isProjective_toSpec_powerSeries :
    IsProjective (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X)) :=
  (isProjective_iff_isProjectiveMorphism_of_isAffine _).mpr (isHProjective_toSpec _)

/-- **The generic fibre of `X` does not have good reduction over `ℝ[[π]]`**: a smooth proper model
would force every minimal model, `X` among them, to be smooth over `ℝ[[π]]`
([Stacks, Tag 0CDI]). -/
theorem not_hasGoodReduction_powerSeries :
    ¬ HasGoodReduction (PowerSeries ℝ) (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X))
      (isProjective_toSpec_powerSeries K) := by
  intro h
  have hsm := ((tfae_hasGoodReduction (R := PowerSeries ℝ) _
    (isProjective_toSpec_powerSeries K)).out 1 3).mp h
  exact not_smooth_powerSeries (hsm _ _ _ (isMinimalModel_powerSeries K))

/-- **Stacks Project, Tag 0CDL.** Let `R = ℝ[[π]]` with fraction field `K`, let
`X = V(T₁² + T₂² - πT₀²) ⊆ ℙ²_R` and let `C = V(T₁² + T₂² - πT₀²) ⊆ ℙ²_K` be its generic fibre.
1. The base change of `X` to `ℂ[[π]]` is the scheme `V(T₁T₂ - πT₀²)` of [Stacks, Tag 0CA0].
2. `X` is regular, and its special fibre is irreducible yet singular.
3. `X` is a minimal model of `C`, and the unique one: every minimal model of `C` is isomorphic to
   `X` as a model.
4. `C` has genus `0` and does not have good reduction over `R`: an extension of `R` is needed even
   in genus `0`. -/
@[stacks 0CDL]
theorem realConic_example :
    IsPullback (splitMap PowerSeries.X (algebraMap (PowerSeries ℝ) (PowerSeries ℂ))
        iPowerSeries_sq two_mul_halfPowerSeries
        (GenusZero.isHomogeneous_conicEquation (PowerSeries.X : PowerSeries ℂ))
        (by rw [algebraMap_powerSeries_X]; rfl) ≫
        PlaneCurveModel.mapMap (equation PowerSeries.X) (isHomogeneous_equation _)
          (algebraMap (PowerSeries ℝ) (PowerSeries ℂ)))
      (GenusZero.conicToSpec (PowerSeries.X : PowerSeries ℂ))
      (toSpec (PowerSeries.X : PowerSeries ℝ))
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) (PowerSeries ℂ)))) ∧
    IsRegular (scheme (PowerSeries.X : PowerSeries ℝ)) ∧
    IrreducibleSpace (specialFiber (PowerSeries.X : PowerSeries ℝ)
      (IsLocalRing.ResidueField (PowerSeries ℝ))) ∧
    ¬ IsRegular (specialFiber (PowerSeries.X : PowerSeries ℝ)
      (IsLocalRing.ResidueField (PowerSeries ℝ))) ∧
    IsMinimalModel (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X))
      (toSpec (PowerSeries.X : PowerSeries ℝ)) (genericFiberIso K PowerSeries.X) ∧
    (∀ (Y : Scheme.{0}) (pY : Y ⟶ Spec (.of (PowerSeries ℝ)))
      (eY : scheme (algebraMap (PowerSeries ℝ) K PowerSeries.X) ≅
        pullback pY (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) K)))),
      IsMinimalModel (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X)) pY eY →
        ∃ φ : scheme (PowerSeries.X : PowerSeries ℝ) ≅ Y,
          φ.hom ≫ pY = toSpec (PowerSeries.X : PowerSeries ℝ) ∧
          (genericFiberIso K PowerSeries.X).hom ≫
              pullback.fst (toSpec (PowerSeries.X : PowerSeries ℝ))
                (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) K))) ≫ φ.hom =
            eY.hom ≫
              pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) K)))) ∧
    genus (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X)) = 0 ∧
    ¬ HasGoodReduction (PowerSeries ℝ) (toSpec (algebraMap (PowerSeries ℝ) K PowerSeries.X))
      (isProjective_toSpec_powerSeries K) :=
  ⟨isPullback_complexification, isRegular_powerSeries, irreducibleSpace_specialFiber_powerSeries,
    not_isRegular_specialFiber_powerSeries, isMinimalModel_powerSeries K,
    fun _ pY eY hY ↦ exists_iso_of_isMinimalModel_powerSeries K pY eY hY,
    genus_toSpec _, not_hasGoodReduction_powerSeries K⟩

end PowerSeriesModel

end Stacks.Models.RealConicModel

end
