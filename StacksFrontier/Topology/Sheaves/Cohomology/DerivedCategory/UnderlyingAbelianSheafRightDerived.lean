module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaf cohomology of a sheaf of modules, computed in abelian sheaves

Let `O` be a sheaf of rings on a topological space `T` and let `U` be an open of `T`. The group
`Hⁿ(U, M)` of a sheaf of `O`-modules `M` can be reached in several ways, and a statement about
sheaf cohomology is phrased in whichever of them its source used:

* as the degree-`n` cohomology of an unbounded derived sections functor
  `RΓ(U, -) : D(SheafOfModules O) ⥤ D(ModuleCat (O(U)))` at `M` placed in degree `0` — the form
  in which the spectral sequences of filtered complexes of sheaves are stated;
* as Mathlib's classical `ℕ`-indexed right derived functor
  `(SheafOfModules.evaluation O (op U)).rightDerived n` at `M`, an `O(U)`-module;
* as the same classical right derived functor of sections of *abelian* sheaves,
  `(sectionsFunctor T U).rightDerived n`, at the underlying abelian sheaf of `M` — the form in
  which Hodge cohomology and the pages of the Hodge-to-de Rham spectral sequence are stated.

This file identifies all three.

## Main definitions

* `Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetIso`: the comparison of
  [Stacks, Tag 0D5Y] as an isomorphism of functors.

## Main results

* `Stacks.Cohomology.UnderlyingAbelianSheaf.rightDerivedSectionsOnOpenForgetObjIso`:
  `Hⁿ(U, M)` taken as the `n`-th right derived functor of the `AddCommGrp`-valued sections of
  sheaves of modules is `Hⁿ(U, M_ab)` taken as the `n`-th right derived functor of sections of
  abelian sheaves.
* `Stacks.Cohomology.UnderlyingAbelianSheaf.rightDerivedEvaluationForgetObjIso`: the same with
  the module-valued sections functor on the left, the `O(U)`-module structure being forgotten
  afterwards.
* `Stacks.Cohomology.UnderlyingAbelianSheaf.homologyDerivedSectionsSingleIsoRightDerived` and
  `Stacks.Cohomology.UnderlyingAbelianSheaf.homologyDerivedSectionsSingleIsoRightDerivedAbelian`:
  for any right derived functor `RΓ(U, -)` of sections on the unbounded derived
  category, `Hⁿ(RΓ(U, M[0]))` is `Hⁿ(U, M)` in the classical module-valued form, and, after
  forgetting the module structure, `Hⁿ(U, M_ab)` in the classical abelian form.

## References

* [Stacks Project, Tag 0D5Y](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.OpenSubspace (sectionsOnOpen homotopySectionsOnOpen derivedSectionsOnOpen)

universe u

namespace Stacks.Cohomology.UnderlyingAbelianSheaf

attribute [local instance] HasDerivedCategory.standard

variable {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (U : Opens T)

/-! ### The two unbounded derived sections functors exist -/

/-- Sections of abelian sheaves over an open, read on the unbounded homotopy category, have a
pointwise right derived functor. -/
instance hasPointwiseRightDerivedFunctor_homotopyAbelianSectionsOnOpen :
    (homotopyAbelianSectionsOnOpen T U).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (AbelianSheaf T) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective
    (homotopyAbelianSectionsOnOpen T U) Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- Sections of sheaves of modules over an open with the module structure forgotten, read on the
unbounded homotopy category, have a pointwise right derived functor. -/
instance hasPointwiseRightDerivedFunctor_homotopySectionsOnOpen :
    (homotopySectionsOnOpen O U).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective
    (homotopySectionsOnOpen O U) Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- The unit `Γ(U, -) ⟶ RΓ(U, -)` of the unbounded derived sections of abelian sheaves. -/
abbrev derivedAbelianSectionsOnOpenUnit (T' : TopCat.{u}) (V : Opens T') :
    (sectionsFunctor T' V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianSectionsOnOpen T' V :=
  (homotopyAbelianSectionsOnOpen T' V).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (AbelianSheaf T') (ComplexShape.up ℤ))

/-- The unit `Γ(U, -) ⟶ RΓ(U, -)` of the unbounded derived sections of sheaves of modules, with
the module structure forgotten. -/
abbrev derivedSectionsOnOpenUnit :
    (sectionsOnOpen O U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsOnOpen O U :=
  (homotopySectionsOnOpen O U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} O) (ComplexShape.up ℤ))

/-- **The comparison of [Stacks, Tag 0D5Y] as an isomorphism**: unbounded derived sections of a
complex of sheaves of modules are the unbounded derived sections of the underlying complex of
abelian sheaves. -/
def sectionsForgetIso :
    derivedSectionsOnOpen O U ≅ underlyingDerivedSheaf O ⋙ derivedAbelianSectionsOnOpen T U :=
  have := sectionsForgetComparison_isIso O U
  asIso (sectionsForgetComparison O U)

/-! ### `Hⁿ(U, -)` is the same before and after forgetting the module structure -/

/-- **Forgetting the module structure does not change sheaf cohomology**, in Mathlib's classical
`ℕ`-indexed form: for a sheaf of `O`-modules `M` the group `Hⁿ(U, M)` computed as the `n`-th
right derived functor of sections of sheaves of modules is the group `Hⁿ(U, M_ab)` computed as
the `n`-th right derived functor of sections of abelian sheaves, applied to the underlying
abelian sheaf of `M`. -/
def rightDerivedSectionsOnOpenForgetObjIso (M : _root_.SheafOfModules.{u} O) (n : ℕ) :
    ((sectionsOnOpen O U).rightDerived n).obj M ≅
      ((sectionsFunctor T U).rightDerived n).obj ((_root_.SheafOfModules.toSheaf O).obj M) :=
  ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (sectionsOnOpen O U)
      (derivedSectionsOnOpen O U) (derivedSectionsOnOpenUnit O U)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective n).app M).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).mapIso
      ((sectionsForgetIso O U).app
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} O) 0).obj M)) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).mapIso
      ((derivedAbelianSectionsOnOpen T U).mapIso
        (((_root_.SheafOfModules.toSheaf O).mapDerivedCategorySingleFunctor 0).app M)) ≪≫
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (sectionsFunctor T U)
      (derivedAbelianSectionsOnOpen T U) (derivedAbelianSectionsOnOpenUnit T U)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective n).app
        ((_root_.SheafOfModules.toSheaf O).obj M)

/-- **`Hⁿ(U, M)` is the same computed in modules and in abelian sheaves.** Deriving the
module-valued sections functor `Γ(U, -) : SheafOfModules O ⥤ ModuleCat (O(U))` `n` times and then
forgetting the module structure gives the same group as deriving sections of abelian sheaves `n`
times and evaluating at the underlying abelian sheaf. -/
@[ega "0 12.1.1" "partial", sga "4 V 3.5"]
def rightDerivedEvaluationForgetObjIso (M : _root_.SheafOfModules.{u} O) (n : ℕ) :
    (forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).obj
        (((_root_.SheafOfModules.evaluation O (op U)).rightDerived n).obj M) ≅
      ((sectionsFunctor T U).rightDerived n).obj ((_root_.SheafOfModules.toSheaf O).obj M) :=
  (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (_root_.SheafOfModules.evaluation O (op U))
      (forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u})
      (sectionsOnOpen O U) (Iso.refl _) n).app M ≪≫
    rightDerivedSectionsOnOpenForgetObjIso O U M n

/-! ### From an unbounded derived sections functor to the classical derived functors -/

/-- **`Hⁿ(RΓ(U, M[0])) ≅ Hⁿ(U, M)`.** For any right derived functor `RΓ(U, -)` of the
module-valued sections over `U` on the unbounded derived category, the degree-`n` cohomology of
`RΓ(U, -)` at a sheaf of modules placed in degree `0` is Mathlib's classical `n`-th right derived
functor of sections. -/
def homologyDerivedSectionsSingleIsoRightDerived
    (RΓ : DerivedCategory (_root_.SheafOfModules.{u} O) ⥤
      DerivedCategory (ModuleCat.{u} (O.obj.obj (op U))))
    (α : (_root_.SheafOfModules.evaluation O (op U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (M : _root_.SheafOfModules.{u} O) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (O.obj.obj (op U))) (n : ℤ)).obj
        (RΓ.obj ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} O) 0).obj M)) ≅
      ((_root_.SheafOfModules.evaluation O (op U)).rightDerived n).obj M :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (_root_.SheafOfModules.evaluation O (op U)) RΓ α
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective n).app M

/-- **`Hⁿ(RΓ(U, M[0])) ≅ Hⁿ(U, M_ab)`.** The degree-`n` cohomology of an unbounded derived
sections functor at a sheaf of `O`-modules `M` placed in degree `0`, with its `O(U)`-module
structure forgotten, is the group `Hⁿ(U, M_ab)` computed as Mathlib's classical `n`-th right
derived functor of sections of abelian sheaves at the underlying abelian sheaf of `M`. -/
def homologyDerivedSectionsSingleIsoRightDerivedAbelian
    (RΓ : DerivedCategory (_root_.SheafOfModules.{u} O) ⥤
      DerivedCategory (ModuleCat.{u} (O.obj.obj (op U))))
    (α : (_root_.SheafOfModules.evaluation O (op U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (M : _root_.SheafOfModules.{u} O) (n : ℕ) :
    (forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (O.obj.obj (op U))) (n : ℤ)).obj
          (RΓ.obj ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} O) 0).obj M))) ≅
      ((sectionsFunctor T U).rightDerived n).obj ((_root_.SheafOfModules.toSheaf O).obj M) :=
  (forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).mapIso
      (homologyDerivedSectionsSingleIsoRightDerived O U RΓ α M n) ≪≫
    rightDerivedEvaluationForgetObjIso O U M n

end Stacks.Cohomology.UnderlyingAbelianSheaf

end
