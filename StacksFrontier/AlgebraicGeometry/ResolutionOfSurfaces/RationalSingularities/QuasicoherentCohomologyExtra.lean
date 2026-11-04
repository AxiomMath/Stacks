module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of quasi-coherent modules on a rational singularity resolution

Let `f : X → Spec(A)` be as in Situation [Stacks, Tag 0B4W]. For a quasi-coherent
`𝒪_X`-module `ℱ`, [Stacks, Tag 0B4X] asserts

1. `Hᵖ(X, ℱ) = 0` for `p ∉ {0, 1}`, and
2. `H¹(X, ℱ) = 0` if `ℱ` is globally generated.

## Main results

* `RationalSingularitySituation.isZero_cohomology_of_notMem_zero_one_unconditional`: clause (1).
* `RationalSingularitySituation.isZero_cohomology_one_of_globallyGenerated_unconditional`:
  clause (2).

## Implementation notes

`CategoryTheory.HasDerivedCategory.standard` is given local priority `2000`, as in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageFibreDimension/GeneralDimensionQuasicoherent.lean`: that import brings another `HasDerivedCategory` instance
into scope, and without the raised priority the `rightDerivedPlus` of these statements would use
a different derived-category universe from the rest of the chapter, so they would not compose.

## References

* [Stacks Project, Tag 0B4X](https://stacks.math.columbia.edu/tag/0B4X)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.AlgebraicGeometry.FibreDimension

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

attribute [local instance 2000] HasDerivedCategory.standard

/-- In Situation [Stacks, Tag 0B4W], the cohomology of a quasi-coherent `𝒪_X`-module vanishes
in every degree outside `{0, 1}`. -/
@[stacks 0B4X "clause (1)"]
theorem isZero_cohomology_of_notMem_zero_one_unconditional
    (F : S.X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : p ∉ ({0, 1} : Set ℤ)) :
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus p).obj F) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp
  obtain ⟨hp0, hp1⟩ := hp
  rcases lt_or_gt_of_ne hp0 with h | h
  · exact CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
      (moduleGlobalSections S.X) F p h
  · have : IsLocallyNoetherian S.base := isLocallyNoetherian_Spec.2 S.noetherian
    have : CompactSpace (S.X : Type u) := QuasiCompact.compactSpace_of_compactSpace S.f
    have : QuasiSeparatedSpace (S.X : Type u) := quasiSeparatedSpace_of_quasiSeparated S.f
    have hp' : (1 : ℤ) < p := by omega
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
      ⟨p.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    exact isZero_rightDerivedPlus_moduleGlobalSections_of_affine_base_of_isQuasicoherent S.f
      (d := 1) S.topologicalKrullDim_fiber_le_natCast_one F (by exact_mod_cast hp')

/-- In Situation [Stacks, Tag 0B4W], a globally generated quasi-coherent `𝒪_X`-module has
vanishing first cohomology. -/
@[stacks 0B4X "clause (2)"]
theorem isZero_cohomology_one_of_globallyGenerated_unconditional
    (F : S.X.Modules) [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj F) := by
  have : CompactSpace (S.X : Type u) := QuasiCompact.compactSpace_of_compactSpace S.f
  have : QuasiSeparatedSpace (S.X : Type u) := quasiSeparatedSpace_of_quasiSeparated S.f
  refine isZero_rightDerivedPlus_one_of_generatingSections F σ
    S.isZero_firstCohomologyStructureSheaf fun G hG => ?_
  have : G.IsQuasicoherent := hG
  exact S.isZero_cohomology_of_notMem_zero_one_unconditional G 2 (by norm_num)

end AlgebraicGeometry.RationalSingularitySituation

end

end
