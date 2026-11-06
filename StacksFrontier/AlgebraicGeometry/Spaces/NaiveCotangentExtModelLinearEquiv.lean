module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentExtUniverseComparison

/-!
# `Ext` out of `NL_{X/Y}` at the universe of its sections is `Ext` on the model

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, and let a ring `R` act on `𝒪_X` through
`φ : R →+* Γ(X, 𝒪_X)`. The naive cotangent complex `NL_{X/Y}` of Stacks 0D0V has its sections in
`Type (u + 1)`; on the `Type u`-presented model of the small étale site of `X` it is formed with
sections in `Type u` (`AlgebraicGeometry.Space.modelNaiveCotangentComplex`). This file proves

`Hom_{D(𝒪_model)}(NL_model, 𝒪_model[i]) ≃ₗ[R] Ext^i_{𝒪_X}(NL_{X/Y}, 𝒪_X)`

for every `i`, the right side in any model of the derived category of `𝒪_X`-modules with sections
in `Type (u + 1)`, the unit module raised to that universe. The steps are those of
`AlgebraicGeometry.Space.moduleFinite_naiveCotangentExt_of_moduleFinite_modelHom`: restriction to
the model is an equivalence at the universe `u + 1` and carries `NL_{X/Y}` to the universe lift of
`NL_model`, and raising the universe of the sections on the model is bijective on morphisms into
the bounded below object `𝒪[i]`. Every step is `R`-linear.

## Main definitions

* `AlgebraicGeometry.Space.modelHomLinearEquivNaiveCotangentExt`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {R : Type*} [CommRing R]
  (φ : R →+* GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))

set_option maxHeartbeats 800000 in
/-- **`Ext^i(NL_{X/Y}, 𝒪_X)` is `Hom(NL_model, 𝒪_model[i])`, `R`-linearly.** -/
def modelHomLinearEquivNaiveCotangentExt
    [HasDerivedCategory.{w}
      (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))] (i : ℤ) :
    letI : Linear R (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2))) := Stacks.SheafOfModules.linearOver _ φ
    letI : Linear R (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
      Stacks.SheafOfModules.linearOver _ ((modelRestrictGlobalSections B S hS X).comp φ)
    (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f) ⟶
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (modelRingSheaf B S hS X)) 0).obj
          (SheafOfModules.unit (modelRingSheaf B S hS X)))⟦i⟧) ≃ₗ[R]
      DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B S hS f))
        ((DerivedCategory.singleFunctor _ 0).obj (Stacks.SheafOfModules.uliftUnit.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)))) i :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (modelRingSheaf B S hS X))
  let φm := (modelRestrictGlobalSections B S hS X).comp φ
  letI L1 : Linear R (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
    (structureSheaf B S hS X.1 X.2))) := Stacks.SheafOfModules.linearOver _ φ
  letI L2 : Linear R (SheafOfModules.{u + 1} (modelRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.linearOver _ φm
  letI L3 : Linear R (SheafOfModules.{u} (modelRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.linearOver _ φm
  let E' := smallEtaleModelModulesEquivULift B S hS X
  let U := modelULift B S hS X
  haveI : E'.functor.Linear R := smallEtaleModelModulesEquivULift_functor_linear B S hS φ
  haveI : U.Linear R := modelULift_linear B S hS φm
  haveI : E'.functor.IsEquivalence := E'.isEquivalence_functor
  haveI : E'.functor.mapDerivedCategory.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence E'.functor
  let NL := naiveCotangentComplex B S hS f
  let NLm := modelNaiveCotangentComplex B S hS f
  let uX := Stacks.SheafOfModules.uliftUnit.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))
  let Om := SheafOfModules.unit (modelRingSheaf B S hS X)
  -- raising the universe of the sections on the model
  let UD := U.mapDerivedCategory
  haveI : EnoughInjectives (RestrictedModelModules B S hS X) :=
    EnoughInjectives.of_equivalence (modelModulesEquiv B S hS X).inverse
  haveI : U.PreservesInjectiveObjects :=
    SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects.{u, u, u, u + 1}
      (modelRingSheaf B S hS X)
  haveI : PreservesFiniteLimits U :=
    SheafOfModules.uliftForPresentationFunctor_preservesFiniteLimits
  haveI : (((DerivedCategory.singleFunctor (RestrictedModelModules B S hS X) 0).obj Om)⟦i⟧).IsGE
      (-i) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 i (-i) (by omega)
  let e3 := LinearEquiv.ofBijective (UD.mapLinearMap R :
    (DerivedCategory.Q.obj NLm ⟶ ((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) →ₗ[R] _)
    (U.mapDerivedCategory_map_bijective_of_isGE (DerivedCategory.Q.obj NLm)
      (((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) (-i))
  -- the restriction of `NL_{X/Y}` and of the unit to the model
  let E'D := E'.functor.mapDerivedCategory
  let iNL : E'D.obj (DerivedCategory.Q.obj NL) ≅ UD.obj (DerivedCategory.Q.obj NLm) :=
    E'.functor.mapDerivedCategoryFactors.app NL ≪≫
      DerivedCategory.Q.mapIso (restrictedNaiveCotangentComplexIso B S hS f) ≪≫
      (U.mapDerivedCategoryFactors.app NLm).symm
  let iU : E'D.obj (((DerivedCategory.singleFunctor _ 0).obj uX)⟦i⟧) ≅
      UD.obj (((DerivedCategory.singleFunctor _ 0).obj Om)⟦i⟧) :=
    (E'D.commShiftIso i).app _ ≪≫ (shiftFunctor _ i).mapIso
      ((E'.functor.mapDerivedCategorySingleFunctor 0).app uX ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (smallEtaleModelULiftUnitIso B S hS X) ≪≫
        ((U.mapDerivedCategorySingleFunctor 0).app Om).symm) ≪≫
      ((UD.commShiftIso i).app _).symm
  let e2 := Linear.homCongr R iNL iU
  -- restriction to the model is an equivalence
  let e1 := LinearEquiv.ofBijective (E'D.mapLinearMap R :
    (DerivedCategory.Q.obj NL ⟶ ((DerivedCategory.singleFunctor _ 0).obj uX)⟦i⟧) →ₗ[R] _)
    ⟨E'D.map_injective, E'D.map_surjective⟩
  e3.trans (e2.symm.trans e1.symm)

end AlgebraicGeometry.Space

end
