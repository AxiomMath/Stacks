module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# The derived pushforward on bounded below derived categories of a ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The pushforward
`f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` is an additive (indeed left exact) functor between abelian
categories, and `Mod(𝒪_X)` has enough injectives. It therefore has a right derived functor on
bounded below derived categories, the *derived pushforward*
`Rf_* : D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)`. It is computed on a bounded below complex of injective
`𝒪_X`-modules by applying `f_*` termwise.

## Main definitions

* `AlgebraicGeometry.RingedSpace.derivedPushforwardPlus`: the derived pushforward
  `Rf_* : D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)`, the right derived functor of `f_*` on bounded below derived
  categories.
* `AlgebraicGeometry.RingedSpace.derivedPushforwardPlusObjIsoOfInjective`: for a bounded below
  complex `I` of injective `𝒪_X`-modules, the isomorphism `Rf_* I ≅ f_* I`.

## Main results

* `AlgebraicGeometry.RingedSpace.derivedPushforwardPlusObjIsoOfInjective_inv`: the inverse of
  that isomorphism is the canonical comparison map `f_* I ⟶ Rf_* I`.

## Implementation notes

The category of `𝒪_X`-modules is `SheafOfModules (structureSheafRing X)`, and `f_*` is
`RingedSpaceModuleAdjunction.modulePushforward f`. The derived pushforward is Mathlib's
`CategoryTheory.Functor.rightDerivedFunctorPlus` of `f_*`, so the whole of the API of that
construction (its comparison map `Functor.rightDerivedFunctorPlusUnith` and the fact that it is a
right derived functor) applies to it. The universes of the two derived categories are instance
arguments rather than fixed to the standard choice.

## References

* [Stacks Project, Tag 0718](https://stacks.math.columbia.edu/tag/0718)
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace

universe u w₁ w₂

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

/-- The derived pushforward `Rf_* : D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)` along a morphism of ringed spaces
`f : X ⟶ Y`: the right derived functor of the pushforward `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` on
bounded below derived categories, which exists because `Mod(𝒪_X)` has enough injectives. -/
@[stacks 0718 "derived pushforward `Rf_* : D⁺(X) → D⁺(Y)`"]
abbrev derivedPushforwardPlus :
    DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing Y)) :=
  (modulePushforward f).rightDerivedFunctorPlus

/-- For a bounded below complex `I` of injective `𝒪_X`-modules, the derived pushforward of `I`
is the termwise pushforward `f_* I`: `Rf_* I ≅ f_* I` in `D⁺(𝒪_Y)`. -/
def derivedPushforwardPlusObjIsoOfInjective
    (I : CochainComplex.Plus (InjectiveObject (SheafOfModules.{u} (structureSheafRing X)))) :
    (derivedPushforwardPlus f).obj (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient _).obj
          ((InjectiveObject.ι _).mapCochainComplexPlus.obj I))) ≅
      DerivedCategory.Plus.Qh.obj ((modulePushforward f).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj
          ((InjectiveObject.ι _).mapCochainComplexPlus.obj I))) :=
  (asIso ((modulePushforward f).rightDerivedFunctorPlusUnith.app _)).symm

/-- The inverse of `derivedPushforwardPlusObjIsoOfInjective` is the canonical comparison map
`f_* I ⟶ Rf_* I` from the termwise pushforward to the derived pushforward. -/
@[simp]
theorem derivedPushforwardPlusObjIsoOfInjective_inv
    (I : CochainComplex.Plus (InjectiveObject (SheafOfModules.{u} (structureSheafRing X)))) :
    (derivedPushforwardPlusObjIsoOfInjective f I).inv =
      (modulePushforward f).rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient _).obj
          ((InjectiveObject.ι _).mapCochainComplexPlus.obj I)) :=
  rfl

end AlgebraicGeometry.RingedSpace
