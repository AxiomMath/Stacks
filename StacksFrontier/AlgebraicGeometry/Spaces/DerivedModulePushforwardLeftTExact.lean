module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage

/-!
# Left t-exactness of the derived direct image of algebraic spaces

The canonical derived direct image `AlgebraicGeometry.Space.derivedModulePushforward` of a
morphism `f : X ⟶ Y` of algebraic spaces and the total right derived functor of
`AlgebraicGeometry.Space.modulePushforward` are both right derived functors of the direct image
of modules along the quasi-isomorphisms, so they are isomorphic. The second is left t-exact by
`AlgebraicGeometry.Space.isGE_derivedModulePushforward_obj`; hence so is the first.

## Main results

* `AlgebraicGeometry.Space.derivedModulePushforwardIsoTotalRightDerived`: `Rf_*` is the total
  right derived functor of `modulePushforward`.
* `AlgebraicGeometry.Space.isGE_derivedModulePushforward_obj_of_isGE`: if `K ∈ D^{≥ n}(𝒪_X)`
  then `Rf_*K ∈ D^{≥ n}(𝒪_Y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*` is the total right derived functor of the direct image of modules**
`modulePushforward`, up to a canonical isomorphism. -/
def derivedModulePushforwardIsoTotalRightDerived (f : X ⟶ Y) :
    derivedModulePushforward B S hS f ≅
      Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) :=
  Functor.rightDerivedUnique _ _ (derivedModulePushforwardUnit B S hS f)
    ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- **`Rf_*` is left t-exact** for every morphism `f : X ⟶ Y` of algebraic spaces: if `K` has no
cohomology below degree `n`, neither has `Rf_*K`. -/
theorem isGE_derivedModulePushforward_obj_of_isGE (f : X ⟶ Y)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ) (hK : K.IsGE n) :
    ((derivedModulePushforward B S hS f).obj K).IsGE n :=
  have := isGE_derivedModulePushforward_obj B S hS f K n hK
  DerivedCategory.TStructure.t.isGE_of_iso
    ((derivedModulePushforwardIsoTotalRightDerived B S hS f).app K).symm n

end AlgebraicGeometry.Space

end
