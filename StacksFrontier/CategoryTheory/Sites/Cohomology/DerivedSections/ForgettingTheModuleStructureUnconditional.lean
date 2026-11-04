module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardUnconditional
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructure
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructure

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Localization.HomBijective
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpersUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting the module structure: morphisms into K-injective complexes

For a sheaf of rings on a site, with values in an arbitrary universe, morphisms from a sectionwise
torsion-free abelian sheaf, placed in degree zero, into a shift of the underlying abelian complex
of a K-injective complex of modules are computed in the homotopy category. We also record global
sections of a sheaf of modules with the module structure forgotten.

## Main definitions

* `moduleGlobalSectionsUnconditional`: Global sections of a sheaf of modules on a ringed site, as
  an abelian group.

## Main results

* `qh_map_bijective_single_of_isKInjective_general`: For a sectionwise torsion-free abelian sheaf
  `A₀` and a K-injective complex of modules `I`, the localization map from morphisms
  `A₀[0] ⟶ I⟦n⟧` in the homotopy category to morphisms in the derived category is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ZeroObject

namespace Stacks.Cohomology.ForgetModule

universe u

attribute [local instance] HasDerivedCategory.standard

section Machinery

open ModuleSheafCohomology

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (O : Sheaf J RingCat.{w}) [EnoughInjectives (SheafOfModules.{w} O)]

/-- For a sheaf of abelian groups `A₀` whose sections are torsion-free and a K-injective complex
of modules `I`, the map `DerivedCategory.Qh.map` from morphisms `A₀[0] ⟶ I⟦n⟧` in the homotopy
category of abelian sheaves, where `I` is regarded as a complex of abelian sheaves, to the
corresponding morphisms in the derived category is bijective, for every `n : ℤ`. -/
theorem qh_map_bijective_single_of_isKInjective_general
    (A₀ : Sheaf J AddCommGrpCat.{w})
    (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V))
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) [I.IsKInjective] (n : ℤ) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{w}) 0).obj A₀) ⟶
          (HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)).obj
            ((((SheafOfModules.toSheaf O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) := by
  let : (I⟦n⟧).IsKInjective := inferInstance
  have hbij := toSheaf_localization_map_bijective_of_isLE_general J O
    ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{w}) 0).obj A₀) 0
    (torsionFree_single_general J A₀ hA₀ 0) (I⟦n⟧)
  refine DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)).mapIso
      (((SheafOfModules.toSheaf O).mapCochainComplexShiftIso n).app I)) hbij

end Machinery

section SmallSiteUnit

open ModuleSheafCohomology

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

end SmallSiteUnit

section Statements

open ModuleSheafCohomology

variable (X : RingedSite.{u, u, u})

/-- Global sections of a sheaf of modules, with the module structure forgotten. -/
abbrev moduleGlobalSectionsUnconditional : SheafOfModules.{u} X.ringSheaf ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringSheaf ⋙ abelianGlobalSections X

/-- The global sections functor `moduleGlobalSectionsUnconditional X` is additive. -/
instance moduleGlobalSections_additive_general : (moduleGlobalSectionsUnconditional X).Additive :=
  inferInstanceAs ((SheafOfModules.toSheaf X.ringSheaf ⋙ abelianGlobalSections X)).Additive

end Statements

end Stacks.Cohomology.ForgetModule

end
