module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GloballyGeneratedPowerVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOverField

/-!
# Global generation of a power of the dualizing sheaf on a semistable fibre

Let `Y` be a proper curve over a field `k` with `H⁰(Y, 𝒪_Y) = k`, at-worst-nodal singularities and
genus `g ≥ 1`, and let `ω_Y` be its dualizing sheaf. Put `m = 1` if `g = 1` and `m = 2` if
`g ≥ 2`, and `r = 1` if `g = 1` and `r = 3g - 3` if `g ≥ 2`. This file proves the fibrewise
facts behind the proof of Stacks 0E6Y:

* `dim H⁰(Y, ω_Y^{⊗ m}) ≥ r` (`AlgebraicGeometry.C1590Private.semistableRank_le_finrank`): in
  genus one `H⁰(Y, ω_Y)` is dual to `H¹(Y, 𝒪_Y)`, and in genus at least two by Riemann-Roch,
  `deg ω_Y^{⊗ 2} = 4g - 4`;
* if `Y` has no rational tail, then `ω_Y^{⊗ m}` is globally generated and
  `dim H⁰(Y, ω_Y^{⊗ m}) = r`
  (`AlgebraicGeometry.C1590Private.isGeneratedByGlobalSections_of_noRationalTail`,
  `AlgebraicGeometry.C1590Private.finrank_le_semistableRank`): in genus one `ω_Y ≅ 𝒪_Y`, and in
  genus at least two `ω_Y^{⊗ 2}` is globally generated (Stacks 0E3K) and has no `H¹`;
* conversely, if `ω_Y^{⊗ m}` is globally generated, `Y` has no rational tail
  (`AlgebraicGeometry.C1590Private.noRationalTail_of_isGeneratedByGlobalSections`), `ω_Y`
  having negative degree on a rational tail (Stacks 0E63).

The dimension of `H⁰` is also read on the module of global sections with its `k`-module structure
through the structure morphism (`AlgebraicGeometry.C1590Private.finrank_sections_eq`).

## Implementation notes

Unregistered helpers.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry.C1590Private

/-- The power of the dualizing sheaf used for a fibre of genus `g`: `1` in genus one and `2`
otherwise. -/
abbrev semistablePower (g : ℕ) : ℤ := if g = 1 then 1 else 2

/-- The dimension of the global sections of `ω^{⊗ m}` on a fibre of genus `g` without rational
tails: `1` in genus one and `3g - 3` otherwise. -/
abbrev semistableRank (g : ℕ) : ℕ := if g = 1 then 1 else 3 * g - 3

/-! ### The two module structures on global sections -/

section Sections

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))

/-- **The `k`-dimension of `H⁰(Y, M)` is that of `Γ(Y, M)`** with its `k`-module structure through
the structure morphism. -/
theorem finrank_sections_eq (M : Y.Modules) :
    (letI := Stacks.Cech.sectionsModule f M ⊤
    Module.finrank k Γ(M, ⊤)) = Module.finrank k (cohomologyOverField k f M 0) := by
  let := Stacks.Cech.sectionsModule f M ⊤
  refine Eq.symm (LinearEquiv.finrank_eq ?_)
  refine (cohomologyOverFieldZeroLinearIso k f M).toLinearEquiv.trans
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The `k`-dimension of `H⁰` is invariant under isomorphism. -/
theorem finrank_cohomologyOverField_zero_congr {M N : Y.Modules} (e : M ≅ N) :
    Module.finrank k (cohomologyOverField k f M 0) =
      Module.finrank k (cohomologyOverField k f N 0) :=
  ((ModuleCat.restrictScalars _).mapIso
    (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).rightDerived 0).mapIso
      e)).toLinearEquiv.finrank_eq

end Sections

/-! ### The fibrewise facts -/

section Fibre

variable (k : Type u) [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
  [IsProper (Y ↘ Spec (.of k))] (hdim : topologicalKrullDim Y = 1)
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop)]
  (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k Y)

include hdim hnodal

/-- In genus one, `dim H⁰(Y, ω_Y^{⊗ 1}) = 1`. -/
private theorem finrank_tensorPower_one_dualizingSheafOverField_eq_one
    (h1 : genus (Y ↘ Spec (.of k)) = 1) :
    haveI := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
    Module.finrank k
      (cohomologyOverField k (Y ↘ Spec (.of k)) (tensorPower Y.presheaf Y.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) 1) 0) = 1 := by
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  let S : CohenMacaulayCurveSituation.{u} := ⟨k, Y, Y ↘ Spec (.of k), hdim⟩
  refine (finrank_cohomologyOverField_zero_congr (Y ↘ Spec (.of k))
    (Stacks.SheafOfModules.Invertible.tensorPowerOneIso Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))))).trans ?_
  have h := S.finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one
  change Module.finrank k (cohomologyOverField k (Y ↘ Spec (.of k))
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) 0) =
    Module.finrank k (cohomologyOverField k (Y ↘ Spec (.of k))
      (SheafOfModules.unit Y.ringCatSheaf) 1) at h
  rw [h, finrank_cohomologyOverField_one_unit_eq_genus, h1]

/-- Riemann-Roch for `ω_Y^{⊗ 2}`: `h⁰ - h¹ + 3 = 3g`. -/
private theorem finrank_sub_finrank_tensorPower_two_dualizingSheafOverField
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))] :
    (Module.finrank k (cohomologyOverField k (Y ↘ Spec (.of k)) (tensorPower Y.presheaf
      Y.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) 2) 0) : ℤ) -
      Module.finrank k (cohomologyOverField k (Y ↘ Spec (.of k)) (tensorPower Y.presheaf
        Y.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) 2) 1) + 3 =
      3 * genus (Y ↘ Spec (.of k)) := by
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  have := tensorPower_isInvertible Y.presheaf Y.ringCatSheaf.2
    (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) 2
  have hrr := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k (Y ↘ Spec (.of k))
    hdim.le (tensorPower Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) 2)
  rw [invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one k
      (Y ↘ Spec (.of k)) hdim.le _ 2,
    invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k (Y ↘ Spec (.of k))
      hdim.le] at hrr
  omega

/-- **The lower bound `dim H⁰(Y, ω_Y^{⊗ m}) ≥ r`** on a proper nodal curve of genus `g ≥ 1` with
`H⁰(Y, 𝒪_Y) = k`. In genus one `dim H⁰(Y, ω_Y) = g = 1` by duality; in genus `g ≥ 2`, by
Riemann-Roch `h⁰ - h¹ = deg ω_Y^{⊗ 2} + 1 - g = 3g - 3`. -/
theorem semistableRank_le_finrank (hg : 1 ≤ genus (Y ↘ Spec (.of k))) :
    haveI := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
    semistableRank (genus (Y ↘ Spec (.of k))) ≤ Module.finrank k
      (cohomologyOverField k (Y ↘ Spec (.of k)) (tensorPower Y.presheaf Y.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))
          (semistablePower (genus (Y ↘ Spec (.of k))))) 0) := by
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  by_cases h1 : genus (Y ↘ Spec (.of k)) = 1
  · rw [show semistableRank (genus (Y ↘ Spec (.of k))) = 1 from if_pos h1,
      show semistablePower (genus (Y ↘ Spec (.of k))) = 1 from if_pos h1]
    exact le_of_eq
      (finrank_tensorPower_one_dualizingSheafOverField_eq_one k hdim hnodal h1).symm
  · rw [show semistableRank (genus (Y ↘ Spec (.of k))) = 3 * genus (Y ↘ Spec (.of k)) - 3
        from if_neg h1,
      show semistablePower (genus (Y ↘ Spec (.of k))) = 2 from if_neg h1]
    have := finrank_sub_finrank_tensorPower_two_dualizingSheafOverField k hdim hnodal
    omega

/-- **Without rational tails, `ω_Y^{⊗ m}` is globally generated** (Stacks 0E3K): in genus one
`ω_Y ≅ 𝒪_Y`, and in genus at least two `ω_Y^{⊗ 2}` is globally generated. -/
theorem isGeneratedByGlobalSections_of_noRationalTail (hg : 1 ≤ genus (Y ↘ Spec (.of k)))
    (htail : ∀ C : Y.IdealSheafData, ¬ IsRationalTail k Y C) :
    haveI := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
    SheafOfModules.IsGeneratedByGlobalSections (tensorPower Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))
        (semistablePower (genus (Y ↘ Spec (.of k))))) := by
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  by_cases h1 : genus (Y ↘ Spec (.of k)) = 1
  · rw [show semistablePower (genus (Y ↘ Spec (.of k))) = 1 from if_pos h1]
    obtain ⟨φ⟩ := nonempty_dualizingSheafOverField_iso_unit_of_forall_not_isRationalTail hdim
      hnodal htail h1
    have := AlgebraicGeometry.SheafOfModules.isInvertible_unit Y.presheaf Y.ringCatSheaf.2
    let e := Stacks.SheafOfModules.Invertible.tensorPowerCongr Y.presheaf Y.ringCatSheaf.2 _ _
      φ 1 ≪≫ Stacks.SheafOfModules.Invertible.tensorPowerUnitIso Y.presheaf Y.ringCatSheaf.2 1
    exact Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso e.symm
      ⟨Stacks.AlgebraicGeometry.CoherenceCriteria.unitGeneratingSections⟩
  · rw [show semistablePower (genus (Y ↘ Spec (.of k))) = 2 from if_neg h1]
    exact
      isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail
        hdim hnodal htail (by omega) 2 le_rfl

/-- **Without rational tails, `dim H⁰(Y, ω_Y^{⊗ m}) ≤ r`.** In genus one `dim H⁰(Y, ω_Y) = g = 1`;
in genus `g ≥ 2`, `H¹(Y, ω_Y^{⊗ 2}) = 0` since `ω_Y^{⊗ 2}` is globally generated and `ω_Y` has
positive degree `2g - 2`, so `h⁰ = 3g - 3` by Riemann-Roch. -/
theorem finrank_le_semistableRank (hg : 1 ≤ genus (Y ↘ Spec (.of k)))
    (htail : ∀ C : Y.IdealSheafData, ¬ IsRationalTail k Y C) :
    haveI := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
    Module.finrank k (cohomologyOverField k (Y ↘ Spec (.of k)) (tensorPower Y.presheaf
      Y.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))
        (semistablePower (genus (Y ↘ Spec (.of k))))) 0) ≤
      semistableRank (genus (Y ↘ Spec (.of k))) := by
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  let S : CohenMacaulayCurveSituation.{u} := ⟨k, Y, Y ↘ Spec (.of k), hdim⟩
  have hgen := isGeneratedByGlobalSections_of_noRationalTail k hdim hnodal hg htail
  by_cases h1 : genus (Y ↘ Spec (.of k)) = 1
  · rw [show semistableRank (genus (Y ↘ Spec (.of k))) = 1 from if_pos h1,
      show semistablePower (genus (Y ↘ Spec (.of k))) = 1 from if_pos h1]
    exact le_of_eq
      (finrank_tensorPower_one_dualizingSheafOverField_eq_one k hdim hnodal h1)
  · rw [show semistablePower (genus (Y ↘ Spec (.of k))) = 2 from if_neg h1] at hgen ⊢
    rw [show semistableRank (genus (Y ↘ Spec (.of k))) = 3 * genus (Y ↘ Spec (.of k)) - 3
        from if_neg h1]
    obtain ⟨σ⟩ := hgen
    have : IsReduced Y := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k Y hnodal
    have hequi : TopologicalSpace.Equidimensional Y :=
      equidimensional_of_isIso_globalSections_of_dimension_one k (Y ↘ Spec (.of k)) hdim
    have hdeg := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k
      (Y ↘ Spec (.of k)) hdim.le
    have hg2 : 2 ≤ genus (Y ↘ Spec (.of k)) := by omega
    have hpos : 0 < invertibleCurveDegree k (Y ↘ Spec (.of k)) hdim.le
        (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) := by
      rw [hdeg]
      omega
    have hH1 := S.isZero_cohomologyOverField_one_dualizingSheafOverField_tensorPower hequi hpos
      (m := 2) le_rfl σ
    have hrr := finrank_sub_finrank_tensorPower_two_dualizingSheafOverField k hdim hnodal
    have h0 : Module.finrank k (cohomologyOverField k (Y ↘ Spec (.of k)) (tensorPower Y.presheaf
        Y.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) 2) 1) = 0 :=
      have := ModuleCat.subsingleton_of_isZero hH1
      Module.finrank_zero_of_subsingleton
    omega

/-- **If `ω_Y^{⊗ m}` is globally generated, `Y` has no rational tail.** A globally generated
positive power of `ω_Y` gives `ω_Y` nonnegative degree on every proper integral curve mapping to
`Y`, while `ω_Y` has negative degree on a rational tail (Stacks 0E63). -/
theorem noRationalTail_of_isGeneratedByGlobalSections
    (h : haveI := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
      SheafOfModules.IsGeneratedByGlobalSections (tensorPower Y.presheaf Y.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))
          (semistablePower (genus (Y ↘ Spec (.of k)))))) :
    ∀ C : Y.IdealSheafData, ¬ IsRationalTail k Y C := by
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  obtain ⟨n, hn, hgen⟩ : ∃ n : ℕ, 0 < n ∧ SheafOfModules.IsGeneratedByGlobalSections
      (tensorPower Y.presheaf Y.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) n) := by
    by_cases h1 : genus (Y ↘ Spec (.of k)) = 1
    · rw [show semistablePower (genus (Y ↘ Spec (.of k))) = 1 from if_pos h1] at h
      exact ⟨1, one_pos, h⟩
    · rw [show semistablePower (genus (Y ↘ Spec (.of k))) = 2 from if_neg h1] at h
      exact ⟨2, two_pos, h⟩
  intro C hC
  have hneg := invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail
    hdim hnodal C hC
  have : IsIntegral C.subscheme := hC.isIntegral
  have hnn := invertibleCurveDegree_pullback_nonneg_of_isGeneratedByGlobalSections k
    (C.subschemeι ≫ (Y ↘ Spec (.of k)))
    (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k Y hdim C hC).le
    C.subschemeι _ n hn hgen
  exact absurd hneg (not_lt.mpr hnn)

end Fibre

end AlgebraicGeometry.C1590Private

end
