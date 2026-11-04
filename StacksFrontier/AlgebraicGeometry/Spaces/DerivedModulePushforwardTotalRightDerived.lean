module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage

/-!
# The two spellings of the derived direct image of algebraic spaces

The derived direct image `Rf_*` of a morphism `f : X ⟶ Y` of algebraic spaces is the total right
derived functor of the degreewise direct image of modules. It is written either as
`Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)` or as
`AlgebraicGeometry.Space.derivedModulePushforward B S hS f` (the derived direct image of the
morphism of small étale ringed topoi); the two functors are equal.

## Main results

* `CategoryTheory.Functor.totalRightDerived_eq_of_eq`: equal functors have equal total right
  derived functors.
* `AlgebraicGeometry.Space.totalRightDerived_modulePushforward_eq`: the two spellings of `Rf_*`
  agree.
-/

@[expose] public section

open CategoryTheory

universe u

/-- Equal functors have equal total right derived functors. -/
theorem CategoryTheory.Functor.totalRightDerived_eq_of_eq {C D H : Type*} [Category C]
    [Category D] [Category H] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : C ⥤ H} (h : F = G) [hF : F.HasRightDerivedFunctor W]
    [hG : G.HasRightDerivedFunctor W] :
    F.totalRightDerived L W = G.totalRightDerived L W := by
  subst h
  rfl

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The two spellings of `Rf_*` agree**: the total right derived functor of the direct image of
modules is the derived direct image of the morphism of small étale ringed topoi. -/
theorem totalRightDerived_modulePushforward_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) =
      derivedModulePushforward B S hS f :=
  Functor.totalRightDerived_eq_of_eq _ _ (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS f)
    (hG := inferInstanceAs ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f)).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (ComplexShape.up ℤ))))

end AlgebraicGeometry.Space

end
