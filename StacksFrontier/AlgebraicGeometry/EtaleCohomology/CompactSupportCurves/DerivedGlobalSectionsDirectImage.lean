module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived

/-!
# Global sections of a derived direct image, on unbounded derived categories

Let `g : X ⟶ Y` be a morphism of schemes and `Λ` a ring. On the unbounded derived categories
`D(-_étale, Λ)` of sheaves of `Λ`-modules on the small étale sites, the derived global sections of
the derived direct image are the derived global sections upstairs, `RΓ(Y, Rg_* K) ≅ RΓ(X, K)`,
the identification of [Stacks, Tag 08J6] for the total derived functors on unbounded complexes.
The degree-`n` cohomology of `RΓ(X, -)` at a sheaf placed in degree `0` is Mathlib's classical
right derived functor `Rⁿ Γ(X, -)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedDirectImageIso`:
  `RΓ(X, -) ≅ Rg_* ⋙ RΓ(Y, -)`.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedSingleIso`:
  `Hⁿ(RΓ(X, ℱ[0])) ≅ Rⁿ Γ(X, ℱ)`, naturally in `ℱ`.

## Implementation notes

`Rg_* ⋙ RΓ(Y, -)` is a right derived functor of `g_* ⋙ Γ(Y, -) ≅ Γ(X, -)`: on a K-injective
complex `I` both derivation units are invertible, `g_* I` being K-injective because `g_*` has the
exact left adjoint `g^{-1}`. This is the argument of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedDerivedCompIso`, with global
sections in place of the second direct image.

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Injectives.KInjectiveResolution (invertsQuasiIso_mapHomologicalComplex_comp_Q
  isRightDerivedFunctor_iff_isIso_app_of_isKInjective homotopyCategoryUnit)

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section DirectImage

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The comparison `Γ(X, -) ⋙ Q ⟶ Q ⋙ Rg_* ⋙ RΓ(Y, -)` making `Rg_* ⋙ RΓ(Y, -)` a derived
functor of global sections on `X`: the composite of the derivation units of `RΓ(Y, -)` (at
`g_* K`) and of `Rg_*`, preceded by `Γ(X, -) ≅ g_* ⋙ Γ(Y, -)`. -/
def etaleModuleDerivedGlobalSectionsUnboundedDirectImageUnit :
    (etaleModuleGlobalSections.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y) :=
  Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
      (etaleModuleGlobalSectionsDirectImageIso.{u, r} g Λ) (ComplexShape.up ℤ)).inv
      DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ Y) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g) _ ≫
    (Functor.associator _ _ _).hom

/-- `Rg_* ⋙ RΓ(Y, -)` is a right derived functor of global sections on `X`. -/
instance etaleModuleDerivedGlobalSectionsUnboundedDirectImage_isRightDerivedFunctor :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y).IsRightDerivedFunctor
      (etaleModuleDerivedGlobalSectionsUnboundedDirectImageUnit.{u, r} Λ g)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q _)]
  intro I hI
  have : CochainComplex.IsKInjective
      (((etaleModuleDirectImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (etaleModuleInverseImageAdj.{u, r} Λ g) I
  have := isIso_etaleModuleDerivedGlobalSectionsUnboundedUnit_app.{u, r} Λ Y _ this
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ g I hI
  simp only [etaleModuleDerivedGlobalSectionsUnboundedDirectImageUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- **Global sections of a derived direct image**: `RΓ(X, -) ≅ Rg_* ⋙ RΓ(Y, -)` on
`D(X_étale, Λ)`, for an arbitrary morphism of schemes `g : X ⟶ Y`. -/
def etaleModuleDerivedGlobalSectionsUnboundedDirectImageIso :
    etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X ≅
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y :=
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ X)
    (etaleModuleDerivedGlobalSectionsUnboundedDirectImageUnit.{u, r} Λ g)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

end DirectImage

/-- **The cohomology of `RΓ(X, -)` at a sheaf in degree `0` is the classical right derived
functor**: `Hⁿ(RΓ(X, ℱ[0])) ≅ Rⁿ Γ(X, ℱ)`, naturally in `ℱ`. -/
def etaleModuleDerivedGlobalSectionsUnboundedSingleIso (X : Scheme.{u}) (n : ℕ) :
    DerivedCategory.singleFunctor (EtaleModules.{u, r} Λ X) 0 ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) (n : ℤ) ≅
      (etaleModuleGlobalSections.{u, r} Λ X).rightDerived n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (etaleModuleGlobalSections.{u, r} Λ X) (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X)
    (homotopyCategoryUnit _ _ (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ X))
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) n

end Stacks.EtaleCohomology

end
