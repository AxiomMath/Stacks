module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.LowerShriekRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedExtensionOfScalars

/-!
# Bookkeeping for the second diagram of Remark 0GL6

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso_inv_fac`: the
  square `Rg_* ∘ res ≅ res ∘ Rg_*` on a complex, through the units of the two derived direct
  images.
* `Stacks.EtaleCohomology.coefficientSheafComplexIso`: `Λ̲₂[0]` is the derived constant sheaf of
  `Λ₂`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **The square of derived direct images and restriction of coefficients on a complex**: the
unit of `Rg_*` for `Λ₁` at `res J`, followed by `Rg_*` of `Q(res J) ≅ res(Q J)` and the square,
is `Q(res g_*J) ≅ res(Q g_*J)` followed by `res` of the unit of `Rg_*` for `Λ₂`. -/
theorem etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso_inv_fac {X Y : Scheme.{u}}
    (g : X ⟶ Y) (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ) :
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ g).app
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex _).obj J) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g).map
        ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app J) ≫
      (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv.app
        (DerivedCategory.Q.obj J) =
    (etaleModuleRestrictScalarsUniv.{u, r} φ Y).mapDerivedCategoryFactors.inv.app
        (((etaleModuleDirectImage.{u, r} Λ₂ g).mapHomologicalComplex _).obj J) ≫
      (etaleModuleDerivedRestrictScalars.{u, r} φ Y).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₂ g).app J) := by
  have h := Stacks.DerivedSquare.rightDerivedExactChangeIso_hom_fac
    (etaleModuleDirectImage.{u, r} Λ₂ g) (etaleModuleDirectImage.{u, r} Λ₁ g)
    (etaleModuleRestrictScalarsUniv.{u, r} φ X) (etaleModuleRestrictScalarsUniv.{u, r} φ Y)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₂ g)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ g)
    (eqToIso (etaleModuleDirectImage_comp_restrictScalars.{u, r} φ g))
    (isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_restrictScalars.{u, r} φ g) J
  have h' := congrArg (· ≫
    (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv.app
      (DerivedCategory.Q.obj J)) h
  dsimp only [etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso] at h' ⊢
  simp only [Category.assoc, Iso.hom_inv_id_app] at h'
  simp only [Stacks.DerivedSquare.exactChangeUnitDerivedFirst,
    Stacks.DerivedSquare.exactChangeUnitChangeFirst, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] at h'
  erw [DerivedCategory.Q.map_id] at h'
  refine Eq.trans ?_ (h'.symm.trans ?_)
  · exact ((Category.id_comp _).trans (Category.id_comp _)).symm
  · exact (Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.comp_id _))

/-- `Λ₂`, as a `Λ₁`-module placed in degree zero, in `D(Λ₁)`. -/
abbrev coefficientModuleComplex : DerivedCategory (ModuleCat.{max (u + 1) r} Λ₁) :=
  DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (coefficientModule.{u} φ))

/-- The constant sheaf `Λ̲₂` in degree zero is the derived constant sheaf of `Λ₂`. -/
def coefficientSheafComplexIso (X : Scheme.{u}) :
    DerivedCategory.Q.obj (coefficientSheafComplex.{u, r} φ X) ≅
      (etaleModuleDerivedConstantSheaf.{u, r} Λ₁ X).obj (coefficientModuleComplex.{u} φ) :=
  DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleConstantSheafFunctor.{u, r} Λ₁ X) (ComplexShape.up ℤ) 0).app
        (coefficientModule.{u} φ)).symm ≪≫
    ((etaleModuleConstantSheafFunctor.{u, r} Λ₁ X).mapDerivedCategoryFactors.app _).symm

end Stacks.EtaleCohomology

end
