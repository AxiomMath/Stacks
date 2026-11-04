module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsAtATerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso

/-!
# Derived global sections of a scheme and of its ringed site

Let `X` be a scheme. Two unbounded derived global-sections functors on `D(𝒪_X)` are in use in
this library. One is a total right derived functor `RΓ` of
`Stacks.Cohomology.sectionsFunctor X ⊤`, valued in `D(Γ(X, ⊤))`; it is the one the statements of
[Stacks, Tag 09M4] in `StacksFrontier.AlgebraicGeometry.DerivedQCoh.PerfectHomVanishingWindow` are
phrased with, and it enters there as a pair of a functor and its structure morphism. The other
is `Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections` of the ringed site of opens of
`X`, valued in `D(Ab)`; it is the one the derived internal Hom cluster — in particular
`Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap` and
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsDegreeEquiv` — is phrased with.

This file identifies them: the second is the first followed by the forgetful functor, and in
consequence a hypercohomology group of one vanishes exactly when the corresponding group of the
other does.

## Main definitions

* `AlgebraicGeometry.derivedModuleGlobalSectionsIso`:
  `RΓ_site ≅ RΓ ⋙ (forget₂ _ Ab).mapDerivedCategory`.

## Main results

* `AlgebraicGeometry.isZero_homology_derivedModuleGlobalSections_iff`: a hypercohomology group
  of the ringed site vanishes exactly when the corresponding one of `RΓ` does.

## Implementation notes

The comparison is a chain of three steps. The site half is
`AlgebraicGeometry.RingedSite.derivedModuleGlobalSectionsAtTerminalIso` at the terminal object
`⊤` of the site of opens, which rewrites derived global sections of the site as the total right
derived functor of sections over `⊤`. The module-structure half is the step already used in
`AlgebraicGeometry.isLE_rightDerivedSections_obj_of_isQuasicoherent`: a total right derived
functor postcomposed with an exact functor derives the composite
(`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`), and
forgetting the module structure on global sections is the abelian-group-valued sections functor
on the nose (`AlgebraicGeometry.sectionsFunctor_top_comp_forget₂`). The third step is the
uniqueness of total right derived functors, which replaces the canonical model of `RΓ` by the
given one.

Two spellings of the category of `𝒪_X`-modules meet here, the scheme-level `X.Modules` and the
ringed-site-level
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite
X.sheaf).O)`. They are equal by `rfl` — `X.ringCatSheaf` and
`Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf of the site of opens reach the
same sheaf of rings by different routes — but instance search does not cross
them. That is why each of the three steps above is stated entirely inside one of the two
spellings and they are spliced by `Iso.trans`, whose only demand is a definitional unification
of the two middle functors: composing the steps in any way that makes instance search straddle
the boundary fails, and no `IsLocalization` or `IsRightDerivedFunctor` instance stated across
the boundary is found.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology (sectionsFunctor)
open Stacks.Cohomology.ModuleSections (derivedModuleGlobalSections)
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedMapDerivedCategoryIso)
open StacksDraft.PseudoCoherence (mapDerivedCategoryCompHomologyFunctorIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (X : Scheme.{u})

variable (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
  (α : (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]

include α in
/-- **Derived global sections of the ringed site of opens of `X` are derived global sections on
`X` with the module structure forgotten.** -/
def derivedModuleGlobalSectionsIso :
    derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf) ≅
      RΓ ⋙ (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).mapDerivedCategory :=
  RingedSite.derivedModuleGlobalSectionsAtTerminalIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) isTerminalTop ≪≫
    (totalRightDerivedMapDerivedCategoryIso (sectionsFunctor X ⊤)
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})).symm ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedUnique RΓ
      (((sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
      α
      (((sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))).symm
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).mapDerivedCategory

include α in
/-- **A hypercohomology group of the ringed site of opens of `X` vanishes exactly when the
corresponding group of `RΓ` does.** The two are carried into one another by
`AlgebraicGeometry.derivedModuleGlobalSectionsIso` and the forgetful functor, which both
preserves and reflects zero objects. -/
theorem isZero_homology_derivedModuleGlobalSections_iff (Z : DerivedCategory X.Modules) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf)).obj Z)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) n).obj (RΓ.obj Z)) := by
  let T := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}
  let e : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections (Stacks.SheafOfModules.ringedSite X.sheaf)).obj Z) ≅
      T.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) n).obj (RΓ.obj Z)) :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
        ((derivedModuleGlobalSectionsIso X RΓ α).app Z) ≪≫
      (mapDerivedCategoryCompHomologyFunctorIso T n).app (RΓ.obj Z)
  constructor
  · intro h
    exact isZero_of_isZero_forget₂ _ (h.of_iso e.symm)
  · intro h
    exact IsZero.of_iso
      (AddCommGrpCat.isZero_iff_subsingleton.mpr (ModuleCat.isZero_iff_subsingleton.mp h)) e

end AlgebraicGeometry

end
