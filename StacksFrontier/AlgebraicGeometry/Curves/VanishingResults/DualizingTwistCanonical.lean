module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwist
public import StacksFrontier.AlgebraicGeometry.Duality.InvertibleTwistExt
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.GlobalGenerationPairing
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B62 at the canonical dualizing sheaf of a proper curve

In Situation [Stacks, Tag 0B5D] let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of
[Stacks, Tag 0BS2], `Stacks.Duality.dualizingSheafOverField`. [Stacks, Tag 0B62] says that
`H¹(X, ω_X ⊗ ℒ) = 0` for an invertible `ℒ` which is globally generated and not isomorphic to
`𝒪_X`.

`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingTwist.lean` proves the tag for
an arbitrary module `ω` with two carried inputs: duality for `ω` (`DualityVanishing`) and the
pairing step `GlobalGenerationPairsNontrivially`. Both are discharged here at `ω_X`: the pairing
step is `AlgebraicGeometry.exists_globalSectionsMulNegOne_ne_zero`, and duality for `ω_X` follows
from Serre duality for `Ext¹` into `ω_X` together with the twist by `ℒ`.

## Main results

All in the namespace `AlgebraicGeometry.CohenMacaulayCurveSituation`:

* `subsingleton_globalSections_inverse_of_generatingSections`: `H⁰(X, ℒ^{⊗ -1}) = 0` for `ℒ`
  globally generated and nontrivial, with nothing carried.
* `dualityVanishing_dualizingSheafOverField`: `DualityVanishing ω_X`.
* `isZero_firstCohomology_dualizingSheafOverField_tensor`: **[Stacks, Tag 0B62]** at `ω_X`.

## References

* [Stacks Project, Tag 0B62](https://stacks.math.columbia.edu/tag/0B62)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (IsInvertible IsTrivial)
open Stacks.SheafOfModules.Invertible (tensorPowerModule globalSectionsMulNegOne)

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable {S : CohenMacaulayCurveSituation.{u}}

/-- **`H⁰(X, ℒ^{⊗ -1}) = 0`** for an invertible `ℒ` which is globally generated and not
isomorphic to `𝒪_X`. A nonzero global section of `ℒ^{⊗ -1}` pairs nontrivially with some global
section of `ℒ` (`AlgebraicGeometry.exists_globalSectionsMulNegOne_ne_zero`), and such a pair
trivializes `ℒ`. -/
public theorem subsingleton_globalSections_inverse_of_generatingSections (L : S.X.Modules)
    [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L]
    (σ : L.GeneratingSections)
    (hne : ¬ IsTrivial S.X.presheaf S.X.ringCatSheaf.property L) :
    Subsingleton Γ(tensorPowerModule L (-1), ⊤) := by
  have key : ∀ t : Γ(tensorPowerModule L (-1), ⊤), t = 0 := by
    intro t
    by_contra ht
    obtain ⟨s, hs⟩ := exists_globalSectionsMulNegOne_ne_zero L σ t ht
    exact hne (isTrivial_of_globalSectionsMulNegOne_ne_zero L s t hs)
  exact ⟨fun t t' => (key t).trans (key t').symm⟩

variable (S)

/-- **Duality holds for the canonical dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))`**: for an
invertible `ℒ` with `H⁰(X, ℒ^{⊗ -1}) = 0` one has `H¹(X, ω_X ⊗ ℒ) = 0`.

The vanishing `H⁰(X, ℒ^{⊗ -1}) = 0` gives `Ext^1_{𝒪_X}(ℒ^{⊗ -1}, ω_X) = 0` by Serre duality
(`Stacks.Duality.subsingleton_zExt_one_dualizingSheafOverField_of_subsingleton`), tensoring by
`ℒ` carries that group onto `Ext^1_{𝒪_X}(𝒪_X, ω_X ⊗ ℒ)`
(`AlgebraicGeometry.zExtInverseTensorAddEquiv`), and extensions of the structure sheaf are sheaf
cohomology (`Stacks.Duality.subsingleton_cohomologyOverField_of_subsingleton_zExt`). -/
public theorem dualityVanishing_dualizingSheafOverField :
    S.DualityVanishing (Stacks.Duality.dualizingSheafOverField S.f) := by
  intro M _ hM
  have hq : (tensorPowerModule M (-1)).IsQuasicoherent :=
    Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible S.X (tensorPowerModule M (-1))
  have h1 : Subsingleton (Abelian.zExt (tensorPowerModule M (-1))
      (Stacks.Duality.dualizingSheafOverField S.f) 1) :=
    Stacks.Duality.subsingleton_zExt_one_dualizingSheafOverField_of_subsingleton S.f
      (le_of_eq S.dimension_one) _ hq hM
  exact ModuleCat.isZero_iff_subsingleton.2
    (Stacks.Duality.subsingleton_cohomologyOverField_of_subsingleton_zExt S.k S.f _ 1
      ((Equiv.subsingleton_congr
        (zExtInverseTensorAddEquiv M
          (Stacks.Duality.dualizingSheafOverField S.f) 1).toEquiv).mp h1))

/-- **Stacks Project, Tag 0B62**, at the dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` of
[Stacks, Tag 0BS2]. In Situation [Stacks, Tag 0B5D], if `ℒ` is an invertible `𝒪_X`-module which
is generated by its global sections and is not isomorphic to `𝒪_X`, then `H¹(X, ω_X ⊗ ℒ) = 0`.

By duality (`dualityVanishing_dualizingSheafOverField`) the tag reduces to
`H⁰(X, ℒ^{⊗ -1}) = 0`, which is `subsingleton_globalSections_inverse_of_generatingSections`. -/
@[stacks 0B62 "at the dualizing sheaf H^{-1}(f^×(𝒪_{Spec k})) of Tag 0BS2, nothing carried"]
public theorem isZero_firstCohomology_dualizingSheafOverField_tensor
    (L : S.X.Modules) [IsInvertible S.X.presheaf S.X.ringCatSheaf.property L]
    (σ : L.GeneratingSections)
    (hne : ¬ IsTrivial S.X.presheaf S.X.ringCatSheaf.property L) :
    IsZero (cohomologyOverField S.k S.f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
          (S.X.ringCatSheaf.property)⟩).obj
        (Stacks.Duality.dualizingSheafOverField S.f)).obj L)) 1) :=
  S.dualityVanishing_dualizingSheafOverField L
    (subsingleton_globalSections_inverse_of_generatingSections L σ hne)

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
