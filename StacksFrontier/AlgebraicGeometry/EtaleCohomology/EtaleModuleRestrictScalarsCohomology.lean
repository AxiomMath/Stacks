module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AnnihilationLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftFirstCohomology

/-!
# Étale cohomology of a sheaf of modules does not depend on the coefficient ring

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `M` a sheaf of `Λ'`-modules on the
small étale site of a scheme `X`. The cohomology `Hⁱ(X, M)`, computed with injective sheaves of
`Λ'`-modules, is the cohomology of `M` read as a sheaf of `Λ`-modules:

`res_ρ Hⁱ(X, M) ≅ Hⁱ(X, res_ρ M)`.

This is the degreewise form of
`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsRestrictScalars`, and for `Λ = ℤ` it
says that the cohomology of a sheaf of `ℤ/ℓⁿ`-modules is the cohomology of its underlying sheaf
of abelian groups, the comparison needed to read `Hⁱ(Y, ℤ/ℓⁿ)` in Step 9 of the proof of
[Stacks, Tag 03UG] through the Kummer sequence. In terms of `Ext` out of the constant sheaf
(`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt`) it is
`Ext^i_{Λ'}(Λ'_X, M) ≅ Ext^i_Λ(Λ_X, res_ρ M)`.

## Main definitions

* `Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIso`:
  `res_ρ Hⁱ(X, M) ≅ Hⁱ(X, res_ρ M)` as `Λ`-modules.
* `Stacks.EtaleCohomology.extConstantRestrictScalarsIso`:
  `Ext^i(Λ'_X, M) ≅ Ext^i(Λ_X, res_ρ M)` as abelian groups.
* `Stacks.EtaleCohomology.etaleModuleUnderlyingAbelian`: the underlying sheaf of abelian groups.
* `Stacks.EtaleCohomology.extConstantIntAddEquivSheafH` and
  `Stacks.EtaleCohomology.extConstantAddEquivSheafH`: `Ext^i(Λ_X, M) ≃+ Hⁱ(X, M)` with Mathlib's
  `CategoryTheory.Sheaf.H` of the underlying sheaf of abelian groups on the right.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- **`res_ρ Hⁱ(X, M) ≅ Hⁱ(X, res_ρ M)`**: the cohomology of a sheaf of `Λ'`-modules on the small
étale site, read as a `Λ`-module, is the cohomology of the sheaf read as a sheaf of
`Λ`-modules. -/
def rightDerivedPlusRestrictScalarsIso (M : EtaleModules.{u, 0} Λ' X) (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} ρ).obj
        (((etaleModuleGlobalSections.{u, 0} Λ' X).rightDerivedPlus i).obj M) ≅
      ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerivedPlus i).obj
        ((etaleModuleRestrictScalars ρ X).obj M) :=
  (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso
      (ModuleCat.restrictScalars.{u + 1} ρ) i _).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ i).mapIso
      ((etaleModuleDerivedGlobalSectionsRestrictScalars ρ X).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≪≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ X).mapIso
        (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleRestrictScalars ρ X) M))

/-- **`Ext^i(Λ'_X, M) ≅ Ext^i(Λ_X, res_ρ M)`** as abelian groups, for a sheaf `M` of
`Λ'`-modules on the small étale site of `X`: étale cohomology of a sheaf of modules, as `Ext`
out of the constant sheaf, does not depend on the coefficient ring. -/
def extConstantRestrictScalarsIso (M : EtaleModules.{u, 0} Λ' X) (i : ℕ) :
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ'
        X.smallEtaleTopology) i).obj M ≅
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        X.smallEtaleTopology) i).obj ((etaleModuleRestrictScalars ρ X).obj M) :=
  (etaleModuleRightDerivedPlusIsoExt Λ' X M i).symm ≪≫
    (Iso.refl _ : (forget₂ (ModuleCat.{u + 1} Λ') AddCommGrpCat.{u + 1}).obj
        (((etaleModuleGlobalSections.{u, 0} Λ' X).rightDerivedPlus (i : ℤ)).obj M) ≅
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((ModuleCat.restrictScalars.{u + 1} ρ).obj
          (((etaleModuleGlobalSections.{u, 0} Λ' X).rightDerivedPlus (i : ℤ)).obj M))) ≪≫
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
      (rightDerivedPlusRestrictScalarsIso ρ X M i) ≪≫
    etaleModuleRightDerivedPlusIsoExt Λ X _ i

section Abelian

/-- The sheaf of abelian groups underlying a sheaf of `Λ`-modules on the small étale site. -/
abbrev etaleModuleUnderlyingAbelian (Λ : Type) [Ring Λ] :
    EtaleModules.{u, 0} Λ X ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Sheaves of `ℤ`-modules on the small étale site are sheaves of abelian groups. -/
instance etaleModuleUnderlyingAbelian_int_isEquivalence :
    (etaleModuleUnderlyingAbelian X ℤ).IsEquivalence := by
  let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : (etaleModuleUnderlyingAbelian X ℤ).EssSurj := by
    refine ⟨fun G => ⟨(sheafCompose X.smallEtaleTopology F.inv).obj G, ?_⟩⟩
    exact ⟨ObjectProperty.isoMk _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G.obj F.asEquivalence.counitIso ≪≫
      Functor.rightUnitor G.obj)⟩
  exact { }

/-- The constant sheaf of `ℤ`-modules underlies the constant sheaf of abelian groups on `ℤ`, the
source of `CategoryTheory.Sheaf.H`. -/
def etaleModuleUnderlyingAbelianConstantIso :
    (etaleModuleUnderlyingAbelian X ℤ).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ X.smallEtaleTopology) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} ℤ X.smallEtaleTopology).app _

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- `Ext` groups of sheaves of `ℤ`-modules on the small étale site are the `Ext` groups of the
underlying sheaves of abelian groups. -/
def etaleModuleUnderlyingAbelianExtAddEquiv (A N : EtaleModules.{u, 0} ℤ X) (i : ℕ) :
    Ext.{u + 1} A N i ≃+ Ext.{u + 1} ((etaleModuleUnderlyingAbelian X ℤ).obj A)
      ((etaleModuleUnderlyingAbelian X ℤ).obj N) i :=
  haveI : (etaleModuleUnderlyingAbelian X ℤ).Additive :=
    ⟨fun {_ _ _ _} => by
      ext U : 3
      exact (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map_add⟩
  AddEquiv.ofBijective ((etaleModuleUnderlyingAbelian X ℤ).mapExtAddHom A N i)
    ((etaleModuleUnderlyingAbelian X ℤ).mapExt_bijective_of_preservesInjectiveObjects A N i)

/-- **`Ext^i(ℤ_X, N) ≅ Hⁱ(X, N)`** for a sheaf `N` of `ℤ`-modules on the small étale site: the
`Ext` out of the constant sheaf in sheaves of `ℤ`-modules is Mathlib's sheaf cohomology
`CategoryTheory.Sheaf.H` of the underlying sheaf of abelian groups. -/
def extConstantIntAddEquivSheafH (N : EtaleModules.{u, 0} ℤ X) (i : ℕ) :
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ
        X.smallEtaleTopology) i).obj N ≃+
      Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian X ℤ).obj N) i :=
  (etaleModuleUnderlyingAbelianExtAddEquiv X _ N i).trans
    (Stacks.Sheaves.UniverseLift.extPrecompIsoAddEquiv
      (etaleModuleUnderlyingAbelianConstantIso.{u} X).symm i)

/-- **`Ext^i_Λ(Λ_X, M) ≅ Hⁱ(X, M)`** for a sheaf `M` of modules over a commutative ring `Λ` on
the small étale site: the cohomology of `M` computed in sheaves of `Λ`-modules, as `Ext` out of
the constant sheaf, is Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H` of the underlying
sheaf of abelian groups. -/
def extConstantAddEquivSheafH (M : EtaleModules.{u, 0} Λ X) (i : ℕ) :
    (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        X.smallEtaleTopology) i).obj M ≃+
      Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian X Λ).obj M) i :=
  (extConstantRestrictScalarsIso (Int.castRingHom Λ) X M i).addCommGroupIsoToAddEquiv.trans
    (extConstantIntAddEquivSheafH X _ i)

end Abelian

end Stacks.EtaleCohomology

end
