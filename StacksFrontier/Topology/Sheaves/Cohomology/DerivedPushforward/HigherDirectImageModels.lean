module

public import StacksFrontier.Homology.DerivedCategory.PlusModelTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison

/-!
# Higher direct images of a sheaf of modules, at any model of the derived categories

For a morphism of ringed spaces `f : X ⟶ Y` and an `𝒪_X`-module `ℱ`, the `q`-th higher direct
image `R^q f_* ℱ` has two descriptions: the cohomology sheaf `H^q(Rf_*(ℱ[0]))` of the unbounded
derived direct image, and the value at `ℱ` of the `q`-th right derived functor
`(f_*).rightDerivedPlus q`, built from injective resolutions on the bounded below derived
categories. Each depends on a choice of model of the derived categories involved. This file
identifies them, at one model (`homologyDerivedPushforwardSingleIso`) and across models
(`rightDerivedPlusModelIso`), and records the consequence for vanishing: whether `R^q f_* ℱ`
is zero does not depend on the description or on the models.

## Main definitions

* `StacksDraft.DerivedModel.PlusTransport.homologyFullFunctorObjIso`: the comparison of two
  models of `D(𝒜)` commutes with cohomology.
* `StacksDraft.DerivedModel.PlusTransport.rightDerivedPlusModelIso`: `R^q F` at two models.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.homologyDerivedPushforwardSingleIso`:
  `H^q(Rf_*(ℱ[0])) ≅ R^q f_* ℱ`, at one model.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isZero_homology_derivedPushforward_iff`:
  `H^q(Rf_*(ℱ[0])) = 0` at one choice of models exactly when `R^q f_* ℱ = 0` at another.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.DerivedModel.PlusTransport

section Homology

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w₁} C) (h₂ : HasDerivedCategory.{w₂} C)

/-- **The comparison of two models of `D(𝒜)` commutes with cohomology**: every object is the
image of a complex, the comparison carries the image of a complex in the first model to its image
in the second, and in either model the cohomology of the image of a complex is the cohomology of
the complex. -/
def homologyFullFunctorObjIso (n : ℤ) (X : @DerivedCategory C _ _ h₁) :
    (@DerivedCategory.homologyFunctor C _ _ h₂ n).obj ((fullFunctor h₁ h₂).obj X) ≅
      (@DerivedCategory.homologyFunctor C _ _ h₁ n).obj X :=
  let K := (@DerivedCategory.Qh C _ _ h₁).objPreimage X
  let e := (@DerivedCategory.Qh C _ _ h₁).objObjPreimageIso X
  (@DerivedCategory.homologyFunctor C _ _ h₂ n).mapIso
      ((fullFunctor h₁ h₂).mapIso e.symm ≪≫ (fullQhIso h₁ h₂).app K) ≪≫
    (@DerivedCategory.homologyFunctorFactorsh C _ _ h₂ n).app K ≪≫
    ((@DerivedCategory.homologyFunctorFactorsh C _ _ h₁ n).app K).symm ≪≫
    (@DerivedCategory.homologyFunctor C _ _ h₁ n).mapIso e

/-- The comparison of two models of `D⁺(𝒜)` commutes with cohomology. -/
def homologyPlusFunctorObjIso (n : ℤ) (X : @DerivedCategory.Plus C _ _ h₁) :
    (@DerivedCategory.Plus.homologyFunctor C _ _ h₂ n).obj ((plusFunctor h₁ h₂).obj X) ≅
      (@DerivedCategory.Plus.homologyFunctor C _ _ h₁ n).obj X :=
  homologyFullFunctorObjIso h₁ h₂ n ((@DerivedCategory.Plus.ι C _ _ h₁).obj X)

end Homology

section RightDerived

universe wC₁ wC₂ wD₁ wD₂ vC uC vD uD

variable {C : Type uC} [Category.{vC} C] [Abelian C] {D : Type uD} [Category.{vD} D] [Abelian D]
  (hC₁ : HasDerivedCategory.{wC₁} C) (hC₂ : HasDerivedCategory.{wC₂} C)
  (hD₁ : HasDerivedCategory.{wD₁} D) (hD₂ : HasDerivedCategory.{wD₂} D)

/-- **`R^q F` at two models**: the `q`-th right derived functor of an additive functor does not
depend, up to isomorphism, on the models of the bounded below derived categories it is built
from. -/
def rightDerivedPlusModelIso (F : C ⥤ D) [F.Additive] [EnoughInjectives C] (q : ℤ) (X : C) :
    (@Functor.rightDerivedPlus C D _ _ _ _ hC₁ hD₁ F _ _ q).obj X ≅
      (@Functor.rightDerivedPlus C D _ _ _ _ hC₂ hD₂ F _ _ q).obj X :=
  (homologyPlusFunctorObjIso hD₁ hD₂ q _).symm ≪≫
    (@DerivedCategory.Plus.homologyFunctor D _ _ hD₂ q).mapIso
      ((rightDerivedIso hC₁ hC₂ hD₁ hD₂ F).app _ ≪≫
        (@Functor.rightDerivedFunctorPlus C D _ _ _ _ hC₂ hD₂ F _ _).mapIso
          (plusSingleObjIso hC₁ hC₂ 0 X))

end RightDerived

end StacksDraft.DerivedModel.PlusTransport

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u w₁ w₂ w₃ w₄

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **`H^q(Rf_*(ℱ[0])) ≅ R^q f_* ℱ`**, at one choice of models: the unbounded derived direct image
restricts to the bounded below one (`boundedDerivedPushforwardIso`), and the cohomology of the
bounded below derived category is that of the unbounded one. -/
def homologyDerivedPushforwardSingleIso
    [HasDerivedCategory.{w₁} (_root_.SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (_root_.SheafOfModules.{u} (structureSheafRing Y))]
    [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X))] (q : ℤ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      ((modulePushforward f).rightDerivedPlus q).obj F :=
  (DerivedCategory.homologyFunctor _ q).mapIso
    ((boundedDerivedPushforwardIso f).app ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm

/-- **Vanishing of a higher direct image does not depend on the models**: `H^q(Rf_*(ℱ[0])) = 0`
at one choice of models of `D(𝒪_X)` and `D(𝒪_Y)` exactly when `R^q f_* ℱ = 0`, the right derived
functor being built at another. -/
theorem isZero_homology_derivedPushforward_iff
    (hX₁ : HasDerivedCategory.{w₁} (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hY₁ : HasDerivedCategory.{w₂} (_root_.SheafOfModules.{u} (structureSheafRing Y)))
    (hX₂ : HasDerivedCategory.{w₃} (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hY₂ : HasDerivedCategory.{w₄} (_root_.SheafOfModules.{u} (structureSheafRing Y)))
    [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing X))] (q : ℤ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ hY₁ q).obj
        ((@derivedPushforward X Y f hX₁ hY₁).obj
          ((@DerivedCategory.singleFunctor _ _ _ hX₁ 0).obj F))) ↔
      IsZero ((@Functor.rightDerivedPlus _ _ _ _ _ _ hX₂ hY₂ (modulePushforward f) _ _ q).obj F) :=
  (Iso.isZero_iff (@homologyDerivedPushforwardSingleIso X Y f hX₁ hY₁ _ q F)).trans
    (Iso.isZero_iff (StacksDraft.DerivedModel.PlusTransport.rightDerivedPlusModelIso hX₁ hX₂ hY₁
      hY₂ (modulePushforward f) q F))

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
