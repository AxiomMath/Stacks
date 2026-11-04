module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness

/-!
# Leray for the unbounded derived direct image on small étale sites

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the unbounded derived direct image of
sheaves of `Λ`-modules on small étale sites satisfies

`R(g ∘ f)_* = Rg_* ∘ Rf_*`

on `D(X_étale, Λ)`. The direct image `f_*` is right adjoint to the exact inverse image `f^{-1}`,
so it carries K-injective complexes to K-injective complexes, and the composite of the two
derived functors is then a right derived functor of `(g ∘ f)_*`: its unit is invertible at every
K-injective complex.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedLerayUnit`: the unit exhibiting
  `Rf_* ⋙ Rg_*` as a right derived functor of `(g ∘ f)_*`.
* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedLerayIso`: the Leray isomorphism
  `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Injectives.KInjectiveResolution (invertsQuasiIso_mapHomologicalComplex_comp_Q
  isIso_app_of_isKInjective isRightDerivedFunctor_iff_isIso_app_of_isKInjective)

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
  (hfg : fg = f ≫ g)

/-- Direct image of sheaves of `Λ`-modules carries K-injective complexes to K-injective
complexes. -/
theorem isKInjective_etaleModuleDirectImage_mapHomologicalComplex
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hK : K.IsKInjective) :
    CochainComplex.IsKInjective
      (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  have := hK
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ f
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ f
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (etaleModuleInverseImageAdj.{u, r} Λ f) K

/-- The unit exhibiting `Rf_* ⋙ Rg_*` as a right derived functor of `(g ∘ f)_*`. -/
def etaleModuleDerivedDirectImageUnboundedLerayUnit :
    (etaleModuleDirectImage.{u, r} Λ fg).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g :=
  (Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg) (ComplexShape.up ℤ)).symm
      DerivedCategory.Q).hom ≫
    Functor.whiskerLeft ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex
      (ComplexShape.up ℤ)) (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g) ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g)

/-- The unit `etaleModuleDerivedDirectImageUnboundedLerayUnit` is an isomorphism at every
K-injective complex. -/
theorem isIso_etaleModuleDerivedDirectImageUnboundedLerayUnit_app
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (hK : K.IsKInjective) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedLerayUnit.{u, r} Λ f g fg hfg).app K) := by
  have h₁ : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) :=
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f K hK
  have h₂ : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app
      (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ g _
      (isKInjective_etaleModuleDirectImage_mapHomologicalComplex.{u, r} Λ f K hK)
  simp only [etaleModuleDerivedDirectImageUnboundedLerayUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- `Rf_* ⋙ Rg_*`, with the unit `etaleModuleDerivedDirectImageUnboundedLerayUnit`, is a right
derived functor of `(g ∘ f)_*` with respect to quasi-isomorphisms. -/
instance etaleModuleDerivedDirectImageUnboundedLeray_isRightDerivedFunctor :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).IsRightDerivedFunctor
      (etaleModuleDerivedDirectImageUnboundedLerayUnit.{u, r} Λ f g fg hfg)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) :=
  (isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (etaleModuleDirectImage.{u, r} Λ fg))).2
    (isIso_etaleModuleDerivedDirectImageUnboundedLerayUnit_app.{u, r} Λ f g fg hfg)

/-- **Leray for the unbounded derived direct image**: `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` on
`D(X_étale, Λ)`. -/
def etaleModuleDerivedDirectImageUnboundedLerayIso :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ fg ≅
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g :=
  Functor.rightDerivedUnique _ _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg)
    (etaleModuleDerivedDirectImageUnboundedLerayUnit.{u, r} Λ f g fg hfg)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ))

end Stacks.EtaleCohomology

end
