module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison

/-!
# Module-sheaf cohomology over an object and Mathlib's cohomology presheaf

Let `J` be a Grothendieck topology on a small category, let `R` be a sheaf of rings for `J` and
let `U` be an object of the site. The cohomology of a sheaf of `R`-modules over `U`, computed by
deriving sections over `U` in the category of `R`-module sheaves, agrees with the value at `U` of
Mathlib's cohomology presheaf of the underlying abelian sheaf.

Both identifications used here already exist: deriving sections of a module sheaf and then
forgetting agrees with forgetting first and deriving there, and the right-derived functors of
sections over `U` of abelian sheaves are the `Ext`-functors out of the free abelian sheaf on
`yoneda.obj U`, which is the object Mathlib's cohomology presheaf takes `Ext` out of. This file
only composes the two, so that vanishing statements proved in one model can be used in the other.

## Main definitions

* `Stacks.Cohomology.ModuleComparison.rightDerivedSectionsIsoCohomologyPresheaf`: the composite
  comparison.

## Main results

* `Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf`:
  the two models vanish together.

## Implementation notes

The abelian half of the comparison is only available as a choice, so no compatibility in degree
zero with the canonical map to the right-derived functor is claimed; the intended use is the
transport of vanishing.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.ModuleComparison

section Site

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]

/-- Cohomology of a sheaf of modules over an object `U` of the site, computed by deriving
sections over `U` in module sheaves, is Mathlib's degree-`n` sheaf cohomology of `U` with values
in the underlying abelian sheaf.

This is the composite of `ModuleSheafCohomology.sectionsComparisonIso`, which forgets the module
structure, with `Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections`, which
identifies `Ext` out of the free abelian sheaf on `yoneda.obj U` with right-derived sections. The
second factor is a choice, so no normalization in degree zero is claimed. -/
def rightDerivedSectionsIsoCohomologyPresheaf (U : C) (n : ℕ) (F : SheafOfModules.{u} R) :
    ((SheafOfModules.toSheaf.{u} R ⋙
        (sheafSections J AddCommGrpCat.{u}).obj (op U)).rightDerived n).obj F ≅
      Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf.{u} R).obj F) n U :=
  (ModuleSheafCohomology.sectionsComparisonIso J R U n).app F ≪≫
    (SiteSections.cohomologyIsoRightDerivedSections J
      ((SheafOfModules.toSheaf.{u} R).obj F) n U).symm

/-- The two models of the cohomology of a sheaf of modules over an object of the site vanish
together. -/
theorem isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
    (U : C) (n : ℕ) (F : SheafOfModules.{u} R) :
    IsZero (((SheafOfModules.toSheaf.{u} R ⋙
        (sheafSections J AddCommGrpCat.{u}).obj (op U)).rightDerived n).obj F) ↔
      IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf.{u} R).obj F) n U) :=
  ⟨fun h ↦ h.of_iso (rightDerivedSectionsIsoCohomologyPresheaf J R U n F).symm,
    fun h ↦ h.of_iso (rightDerivedSectionsIsoCohomologyPresheaf J R U n F)⟩

end Site

end Stacks.Cohomology.ModuleComparison

end
