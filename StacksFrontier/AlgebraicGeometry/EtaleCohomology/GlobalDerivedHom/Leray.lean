module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageCompositionUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# Leray for unbounded derived global sections on small étale sites

For a morphism of schemes `f : X ⟶ Y` and a ring `Λ`, the unbounded derived global sections of
sheaves of `Λ`-modules on small étale sites satisfy

`RΓ(X, -) = RΓ(Y, Rf_* -)`

on the whole of `D(X_étale, Λ)`. Global sections of a direct image are global sections upstairs
(`Stacks.EtaleCohomology.etaleModuleGlobalSectionsDirectImageIso`), and `f_*` carries K-injective
complexes to K-injective complexes, being right adjoint to the exact `f^{-1}`; so the composite
`Rf_* ⋙ RΓ(Y, -)` is again a right derived functor of `Γ(X, -)`, its unit being invertible at
every K-injective complex.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedLerayUnit`: the unit exhibiting
  `Rf_* ⋙ RΓ(Y, -)` as a right derived functor of `Γ(X, -)`.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedLerayIso`: the Leray
  isomorphism `RΓ(X, -) ≅ Rf_* ⋙ RΓ(Y, -)`.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Injectives.KInjectiveResolution (invertsQuasiIso_mapHomologicalComplex_comp_Q
  isRightDerivedFunctor_iff_isIso_app_of_isKInjective)

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit exhibiting `Rf_* ⋙ RΓ(Y, -)` as a right derived functor of `Γ(X, -)`: the
identification `Γ(Y, f_* -) = Γ(X, -)`, followed by the units of `RΓ(Y, -)` and of `Rf_*`. -/
def etaleModuleDerivedGlobalSectionsUnboundedLerayUnit :
    (etaleModuleGlobalSections.{u, r} Λ X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y :=
  (Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      (etaleModuleGlobalSectionsDirectImageIso.{u, r} f Λ) (ComplexShape.up ℤ)).symm
      DerivedCategory.Q).hom ≫
    Functor.whiskerLeft ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex
      (ComplexShape.up ℤ)) (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ Y) ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
      (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y)

/-- The Leray unit is invertible at every K-injective complex. -/
theorem isIso_etaleModuleDerivedGlobalSectionsUnboundedLerayUnit_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hK : K.IsKInjective) :
    IsIso ((etaleModuleDerivedGlobalSectionsUnboundedLerayUnit.{u, r} Λ f).app K) := by
  have h₁ : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) :=
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f K hK
  have h₂ : IsIso ((etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ Y).app
      (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    isIso_etaleModuleDerivedGlobalSectionsUnboundedUnit_app.{u, r} Λ Y _
      (isKInjective_etaleModuleDirectImage_mapHomologicalComplex.{u, r} Λ f K hK)
  simp only [etaleModuleDerivedGlobalSectionsUnboundedLerayUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- `Rf_* ⋙ RΓ(Y, -)` is a right derived functor of `Γ(X, -)` on `D(X_étale, Λ)`. -/
instance etaleModuleDerivedGlobalSectionsUnboundedLeray_isRightDerivedFunctor :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y).IsRightDerivedFunctor
      (etaleModuleDerivedGlobalSectionsUnboundedLerayUnit.{u, r} Λ f)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) :=
  (isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (etaleModuleGlobalSections.{u, r} Λ X))).2
    (isIso_etaleModuleDerivedGlobalSectionsUnboundedLerayUnit_app.{u, r} Λ f)

/-- **Leray for unbounded derived global sections**: `RΓ(X, -) ≅ RΓ(Y, Rf_* -)` on
`D(X_étale, Λ)`, both being right derived functors of `Γ(X, -)`. -/
def etaleModuleDerivedGlobalSectionsUnboundedLerayIso :
    etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X ≅
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y :=
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, r} Λ X)
    (etaleModuleDerivedGlobalSectionsUnboundedLerayUnit.{u, r} Λ f)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

end Stacks.EtaleCohomology

end
