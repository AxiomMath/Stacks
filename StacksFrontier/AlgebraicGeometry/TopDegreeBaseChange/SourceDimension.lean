module

public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Higher direct images vanish above the dimension of the source

Let `f : X ⟶ Y` be quasi-compact and quasi-separated with `X` a Noetherian space of topological
Krull dimension at most `d`. Then `R^i f_* ℱ = 0` for every quasi-coherent `ℱ` and every
`i > d`. Over an affine open `V ⊆ Y` the higher direct image is the cohomology of `f^{-1}(V)`
([Stacks, Tag 01XK]), which vanishes above `d` by Grothendieck's theorem
([Stacks, Tag 02UZ]), `f^{-1}(V)` being a Noetherian space of dimension at most `d`; vanishing
of a module is checked on stalks.

## Main results

* `…TopDegreeBaseChange.isZero_rightDerivedPlus_moduleGlobalSections_of_topologicalKrullDim_le`:
  `H^i(Z, ℱ) = 0` for `i > d` on a scheme whose underlying space is Noetherian of dimension at
  most `d`.
* `…TopDegreeBaseChange.isZero_rightDerived_pushforward_of_topologicalKrullDim_le`:
  `R^i f_* ℱ = 0` for `i > d`.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **Grothendieck vanishing for a module on a scheme** ([Stacks, Tag 02UZ]): on a scheme whose
underlying space is Noetherian of dimension at most `d`, `H^i(Z, ℱ) = 0` for `i > d`. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_topologicalKrullDim_le
    (Z : Scheme.{u}) [NoetherianSpace Z] (F : Z.Modules) {d i : ℕ}
    (hdim : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (hi : d < i) :
    IsZero (((moduleGlobalSections Z).rightDerivedPlus (i : ℤ)).obj F) := by
  refine (isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup Z F i).mpr ?_
  refine
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
      (J := Opens.grothendieckTopology (Z : Type u)) (R := Z.ringCatSheaf)
      (U := (⊤ : Opens (Z : Type u))) (n := i) (F := F)).mpr ?_
  exact @AddCommGrpCat.isZero_of_subsingleton _
    ((Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj F) i).mp
      (Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
        (d := d) hdim hi _))

/-- **Higher direct images vanish above the dimension of the source**: for `f : X ⟶ Y`
quasi-compact and quasi-separated with `X` Noetherian of dimension at most `d`,
`R^i f_* ℱ = 0` for quasi-coherent `ℱ` and `i > d`. -/
theorem isZero_rightDerivedPlus_pushforward_of_topologicalKrullDim_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [NoetherianSpace X]
    {d : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (F : X.Modules)
    [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine V := hV
  have hdimV : topologicalKrullDim (f ⁻¹ᵁ V).toScheme ≤ (d : WithBot ℕ∞) :=
    (Topology.IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le).trans hdim
  have : NoetherianSpace (f ⁻¹ᵁ V).toScheme :=
    inferInstanceAs (NoetherianSpace (f ⁻¹ᵁ V : Set X))
  exact SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict f V y hyV F
    (by omega) (isZero_rightDerivedPlus_pushforward_of_isZero_cohomology (f ∣_ V) n _
      (isZero_rightDerivedPlus_moduleGlobalSections_of_topologicalKrullDim_le _ _ hdimV
        (by omega)))

/-- `R^n f_* ℱ = 0` for `n > d`, in the `ℕ`-indexed spelling of the higher direct images. -/
theorem isZero_rightDerived_pushforward_of_topologicalKrullDim_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [NoetherianSpace X]
    {d : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hn : d < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) :=
  (isZero_rightDerivedPlus_pushforward_of_topologicalKrullDim_le f hdim F n
    (by exact_mod_cast hn)).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app F)

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
