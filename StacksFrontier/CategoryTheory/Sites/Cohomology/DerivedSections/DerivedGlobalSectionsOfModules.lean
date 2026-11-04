module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections and derived sections of modules on a ringed site

Let `(C, O)` be a ringed site. Taking global sections of a sheaf of `O`-modules, and taking its
sections over an object `U` of `C`, are left exact functors to abelian groups once the module
structure is forgotten. This file names the global sections functor and its unbounded right
derived functor, and records for both of them — and for the sections over an object, whose
underived and derived forms are already available as
`Stacks.Cohomology.Localization.sectionsOverObject` and
`Stacks.Cohomology.Localization.derivedSectionsOverObject` — that sections compute derived
sections on a K-injective complex.

That last statement is what makes derived sections computable at all: a complex of `O`-modules
is K-injective exactly when it may be used in place of a resolution, so the unit of the derived
functor is invertible there. It is the specialisation to these two functors of
`Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective`, which is in turn Stacks 07A5
over the Grothendieck abelian category of sheaves of modules.

## Main definitions

* `Stacks.Cohomology.ModuleSections.moduleGlobalSections`: global sections of a sheaf of
  `O`-modules with the module structure forgotten.
* `Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections`: its unbounded right derived
  functor `RΓ(C, -) : D(O) ⥤ D(Ab)`, with unit
  `Stacks.Cohomology.ModuleSections.derivedModuleGlobalSectionsUnit`.
* `Stacks.Cohomology.ModuleSections.derivedSectionsOverObjectUnit`: the unit of the derived
  functor `RΓ(U, -)` of `Stacks.Cohomology.Localization.derivedSectionsOverObject`.

## Main results

* `Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso` and
  `Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso`: on a K-injective complex `I` the
  complexes of sections `Γ(C, I)` and `Γ(U, I)` already compute `RΓ(C, I)` and `RΓ(U, I)`.
* `Stacks.Cohomology.ModuleSections.moduleGlobalSections_mapHomologicalComplex` and
  `Stacks.Cohomology.ModuleSections.sectionsOverObject_mapHomologicalComplex`: the degreewise
  images of a complex under these functors are the complexes of sections
  `AlgebraicGeometry.RingedSite.globalSectionsComplex` and
  `AlgebraicGeometry.RingedSite.sectionComplex` of Stacks 0A8Z, which is what lets the
  identifications of Stacks 0A94 be read against the derived functors here.

## Implementation notes

Global sections are taken as `AlgebraicGeometry.RingedSite.abelianGlobalSectionsFunctor`, the
compatible families of sections used in Stacks 0A8Z, rather than as Mathlib's `Sheaf.Γ`, the
right adjoint of the constant sheaf functor. The two are isomorphic, both being the limit of the
underlying presheaf, but only the first makes
`moduleGlobalSections_mapHomologicalComplex` hold by `rfl`, and that identity is what the
consumers need: the complex-level computations of Stacks 0A8Z and 0A94 are stated for
`AlgebraicGeometry.RingedSite.globalSectionsComplex`, so a comparison across the two spellings
would have to be carried through every such statement.

Nothing is introduced for sections over an object: `sectionsOverObject` is already definitionally
the composite of forgetting the module structure with evaluation of the underlying sheaf, which
`sectionsOverObject_eq_toSheaf_comp_sheafSections` records, and its derived functor is
`derivedSectionsOverObject`. Only the unit and the K-injective comparison are added.

The `HasRightDerivedFunctor` hypotheses of the derived functors are not stated: sheaves of
`O`-modules on a ringed site with coinciding universes form a Grothendieck abelian category, so
`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck` supplies them.

## References

* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.Cohomology.ModuleSections

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- Global sections of a sheaf of modules on a ringed site, with the module structure
forgotten: the compatible families of sections of the underlying sheaf of abelian groups. -/
noncomputable abbrev moduleGlobalSections :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    RingedSite.abelianGlobalSectionsFunctor X

/-- The degreewise global sections of a complex of modules are the complex of global sections of
Stacks 0A8Z. -/
theorem moduleGlobalSections_mapHomologicalComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K =
      RingedSite.globalSectionsComplex X K :=
  rfl

/-- The degreewise sections over `U` of a complex of modules are the complex of sections of
Stacks 0A8Z. -/
theorem sectionsOverObject_mapHomologicalComplex (U : X.C)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (((Localization.sectionsOverObject X U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K =
      RingedSite.sectionComplex X K U :=
  rfl

/-- Sections over `U` of a sheaf of modules are the sections at `U` of the underlying sheaf of
abelian groups: evaluating the module sheaf and forgetting the module structure is the same as
forgetting it first. -/
theorem sectionsOverObject_eq_toSheaf_comp_sheafSections (U : X.C) :
    Localization.sectionsOverObject X U =
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (sheafSections X.J AddCommGrpCat.{u}).obj (op U) :=
  rfl

/-- Global sections of complexes of modules, followed by localization at the
quasi-isomorphisms. -/
noncomputable abbrev homotopyModuleGlobalSections :
    HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (moduleGlobalSections X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Unbounded derived global sections `RΓ(C, -)` of modules on a ringed site. -/
noncomputable abbrev derivedModuleGlobalSections :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (homotopyModuleGlobalSections X).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- The unit comparing global sections of a complex with derived global sections of its class. -/
noncomputable abbrev derivedModuleGlobalSectionsUnit :
    homotopyModuleGlobalSections X ⟶
      DerivedCategory.Qh ⋙ derivedModuleGlobalSections X :=
  (homotopyModuleGlobalSections X).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- The unit comparing sections over `U` of a complex with derived sections over `U` of its
class. -/
noncomputable abbrev derivedSectionsOverObjectUnit (U : X.C) :
    Localization.homotopySectionsOverObject X U ⟶
      DerivedCategory.Qh ⋙ Localization.derivedSectionsOverObject X U :=
  (Localization.homotopySectionsOverObject X U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

/-- **Global sections compute derived global sections on a K-injective complex.** The class of
the complex of global sections of a K-injective complex `I` is `RΓ(C, I)`: the unit of the
derived functor is invertible there, and the three remaining steps are the canonical
identifications of the localization and of `Functor.mapHomotopyCategory` with
`Functor.mapHomologicalComplex`. -/
noncomputable def globalSectionsKInjectiveIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.obj (RingedSite.globalSectionsComplex X I) ≅
      (derivedModuleGlobalSections X).obj (DerivedCategory.Q.obj I) :=
  ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
        (RingedSite.globalSectionsComplex X I)).symm ≪≫
    DerivedCategory.Qh.mapIso
        (((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm ≪≫
      @asIso _ _ _ _ ((derivedModuleGlobalSectionsUnit X).app
            ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj I))
          (Localization.derivedUnit_isIsoOnKInjective
            (homotopyModuleGlobalSections X) (derivedModuleGlobalSections X)
            (derivedModuleGlobalSectionsUnit X) I) ≪≫
        (derivedModuleGlobalSections X).mapIso
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app I)

/-- **Sections over an object compute derived sections on a K-injective complex.** The class of
the complex of sections over `U` of a K-injective complex `I` is `RΓ(U, I)`, by the same
argument as `globalSectionsKInjectiveIso`. -/
noncomputable def sectionsKInjectiveIso (U : X.C)
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.obj (RingedSite.sectionComplex X I U) ≅
      (Localization.derivedSectionsOverObject X U).obj (DerivedCategory.Q.obj I) :=
  ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
        (RingedSite.sectionComplex X I U)).symm ≪≫
    DerivedCategory.Qh.mapIso
        (((Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app I).symm ≪≫
      @asIso _ _ _ _ ((derivedSectionsOverObjectUnit X U).app
            ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj I))
          (Localization.derivedUnit_isIsoOnKInjective
            (Localization.homotopySectionsOverObject X U)
            (Localization.derivedSectionsOverObject X U)
            (derivedSectionsOverObjectUnit X U) I) ≪≫
        (Localization.derivedSectionsOverObject X U).mapIso
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app I)

end Stacks.Cohomology.ModuleSections

end
