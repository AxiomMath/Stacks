module

public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# Leray over the base ring at the locally small model

For a scheme `f : X ⟶ Spec A` the derived global sections over `A` factor through the derived
direct image: `RΓ(X, -) ≅ RΓ(Spec A, Rf_* -)` ([Stacks, Tag 0D5W]). The base proves this as
`AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso` at the standard model
`HasDerivedCategory.standard` of the three derived categories. The duality statements of this
library, among them the twisted inverse image of [Stacks, Tag 0A9E], live at the locally small
model, so this file transports the isomorphism there.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIsoLocallySmall`: the natural
  isomorphism `RΓ(X, -) ≅ RΓ(Spec A, -) ∘ Rf_*` of functors `D(𝒪_X) ⥤ D(A)` at the locally small
  models, with `Rf_*` spelled `Stacks.Duality.derivedPushforward`.

## Implementation notes

All three functors are total right derived functors, so each is carried from one model to the
other by `StacksDraft.DerivedModel.rightDerivedModelIso`, and the standard-model isomorphism is
conjugated by the three comparison equivalences. Every `HasDerivedCategory` instance is spelled
out, as the module documentation of
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean` requires.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedModel

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- `RΓ(X, -)` read at the two models: the standard-model functor followed by the comparison of
`D(A)` is the comparison of `D(𝒪_X)` followed by the locally small functor. -/
def derivedGlobalSectionsOverStandardGrothendieckModelIso :
    @derivedGlobalSectionsOver A _ X f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor ⋙
        derivedGlobalSectionsOver f :=
  rightDerivedModelIso
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (@derivedGlobalSectionsOverUnit A _ X f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _))
    (derivedGlobalSectionsOverUnit f)
    (shrinkComparisonQhIso X.Modules).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (shrinkComparisonQhIso (ModuleCat.{u} A)).symm)

/-- `Rf_*` read at the two models, in the scheme spelling `Stacks.Duality.derivedPushforward`. -/
def dualityDerivedPushforwardModelIso {Y : Scheme.{u}} (g : X ⟶ Y) :
    @Stacks.Duality.derivedPushforward X Y g (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u} Y.Modules).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor ⋙
        Stacks.Duality.derivedPushforward g :=
  rightDerivedModelIso
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    ((@Stacks.Duality.homotopyPushforward X Y g
        (HasDerivedCategory.standard _)).totalRightDerivedUnit
      (@DerivedCategory.Qh X.Modules _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    ((Stacks.Duality.homotopyPushforward g).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (shrinkComparisonQhIso X.Modules).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (shrinkComparisonQhIso Y.Modules).symm)

/-- The standard-model Leray isomorphism, conjugated to the locally small models: the two
functors `D(𝒪_X) ⥤ D(A)` agree after precomposition with the comparison of `D(𝒪_X)`. -/
def derivedGlobalSectionsOverPushforwardIsoWhiskered :
    (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor ⋙
        derivedGlobalSectionsOver f ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor ⋙
        (Stacks.Duality.derivedPushforward f ⋙
          derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))) :=
  (derivedGlobalSectionsOverStandardGrothendieckModelIso f).symm ≪≫
    Functor.isoWhiskerRight
      (@derivedGlobalSectionsOverPushforwardIso A _ X f)
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (derivedGlobalSectionsOverStandardGrothendieckModelIso (𝟙 (Spec (CommRingCat.of A)))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dualityDerivedPushforwardModelIso f) _ ≪≫
    Functor.associator _ _ _

/-- **[Stacks, Tag 0D5W] over the base ring, at the locally small models.** For a scheme
`f : X ⟶ Spec A` the `A`-linear derived global sections of `X` are the `A`-linear derived global
sections of `Spec A` applied to the derived direct image, `RΓ(X, -) ≅ RΓ(Spec A, Rf_* -)`, as
functors `D(𝒪_X) ⥤ D(A)` at the locally small models. -/
def derivedGlobalSectionsOverPushforwardIsoLocallySmall :
    derivedGlobalSectionsOver f ≅
      Stacks.Duality.derivedPushforward f ⋙
        derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A))) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedGlobalSectionsOverPushforwardIsoWhiskered f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).counitIso _ ≪≫
    Functor.leftUnitor _

end AlgebraicGeometry

end
