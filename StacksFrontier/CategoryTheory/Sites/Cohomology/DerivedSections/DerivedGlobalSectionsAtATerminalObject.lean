module

public import StacksFrontier.CategoryTheory.Functor.Derived.RightDerivedOfAnIsomorphicFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalSectionsAtATerminalObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules

/-!
# Derived global sections on a ringed site with a terminal object

Let `(C, O)` be a ringed site whose underlying category has a terminal object `T`. Unbounded
derived global sections `RΓ(C, -)` of sheaves of `O`-modules, in the spelling
`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections` that takes compatible families of
sections over all the objects of `C`, is then the total right derived functor of sections
over `T`.

## Main definitions

* `AlgebraicGeometry.RingedSite.moduleSectionsAt`: sections of a sheaf of modules over an object,
  as an abelian group.
* `AlgebraicGeometry.RingedSite.moduleGlobalSectionsAtTerminalIso`: the underived comparison.
* `AlgebraicGeometry.RingedSite.derivedModuleGlobalSectionsAtTerminalIso`: the derived one.

## Implementation notes

The underived comparison is
`AlgebraicGeometry.RingedSite.globalSectionsAtTerminalIso` whiskered with the forgetful functor
from sheaves of modules to abelian sheaves. The derived one follows from it because a total
right derived functor of a functor is a total right derived functor of any isomorphic functor
(`Stacks.DerivedFunctorTransport.isRightDerivedFunctor_of_natIso`), together with the uniqueness
of total right derived functors.

Everything is stated at the one spelling
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)` of the category of modules. The
consumer of this file is a *scheme*, where the same category is also spelled `X.Modules`, and
instance search does not cross the two spellings; keeping the comparison inside one spelling makes
the crossing a single definitional unification at the point of use rather than a search.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.ModuleSections (moduleGlobalSections derivedModuleGlobalSections
  derivedModuleGlobalSectionsUnit)
open Stacks.DerivedFunctorTransport
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSite

variable (Y : RingedSite.{u, u, u}) {T : Y.C} (hT : IsTerminal T)

/-- **Sections of a sheaf of modules over an object, as an abelian group.** -/
abbrev moduleSectionsAt (U : Y.C) : SheafOfModules.{u} (ringSheaf Y.O) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringSheaf Y.O) ⋙ (sheafSections Y.J AddCommGrpCat.{u}).obj (op U)

/-- The functor of sections of abelian sheaves over an object is additive. -/
instance sheafSections_additive (U : Y.C) :
    ((sheafSections Y.J AddCommGrpCat.{u}).obj (op U)).Additive where
  map_add := by intros; rfl

/-- Sections of sheaves of modules over an object form an additive functor. -/
instance moduleSectionsAt_additive (U : Y.C) : (moduleSectionsAt Y U).Additive :=
  inferInstanceAs ((SheafOfModules.toSheaf (ringSheaf Y.O) ⋙
    (sheafSections Y.J AddCommGrpCat.{u}).obj (op U)).Additive)

/-- Global sections of sheaves of modules form an additive functor. -/
instance moduleGlobalSections_additive : (moduleGlobalSections Y).Additive :=
  inferInstanceAs ((SheafOfModules.toSheaf (ringSheaf Y.O) ⋙
    abelianGlobalSectionsFunctor Y).Additive)

/-- **Global sections of modules on a site with a terminal object are sections over it.** -/
def moduleGlobalSectionsAtTerminalIso :
    moduleGlobalSections Y ≅ moduleSectionsAt Y T :=
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf (ringSheaf Y.O))
    (globalSectionsAtTerminalIso Y hT)

/-- **Unbounded derived global sections of modules on a site with a terminal object are the
total right derived functor of sections over that object.** -/
def derivedModuleGlobalSectionsAtTerminalIso :
    derivedModuleGlobalSections Y ≅
      ((moduleSectionsAt Y T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringSheaf Y.O)) (ComplexShape.up ℤ)) := by
  let eHot := Functor.isoWhiskerRight
    (mapHomotopyCategoryIso (moduleGlobalSectionsAtTerminalIso Y hT) (ComplexShape.up ℤ))
    DerivedCategory.Qh
  haveI : (derivedModuleGlobalSections Y).IsRightDerivedFunctor
      (eHot.inv ≫ derivedModuleGlobalSectionsUnit Y)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
    isRightDerivedFunctor_of_natIso _ eHot _
  exact Functor.rightDerivedUnique (derivedModuleGlobalSections Y)
    (((moduleSectionsAt Y T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringSheaf Y.O)) (ComplexShape.up ℤ)))
    (eHot.inv ≫ derivedModuleGlobalSectionsUnit Y)
    (((moduleSectionsAt Y T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringSheaf Y.O)) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringSheaf Y.O)) (ComplexShape.up ℤ))

end AlgebraicGeometry.RingedSite

end
