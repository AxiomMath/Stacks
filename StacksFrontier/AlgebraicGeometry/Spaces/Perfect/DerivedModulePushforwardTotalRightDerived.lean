module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# The two spellings of `Rf_*` for a morphism of algebraic spaces agree

For a morphism `f : X ⟶ Y` of algebraic spaces, the total right derived functor
`Stacks.DerivedFunctor.totalRightDerived (AlgebraicGeometry.Space.modulePushforward f)` of the
direct image of modules (the spelling of Stacks 08IS, 0DKJ, 0DKK) and the derived direct image
`AlgebraicGeometry.Space.derivedModulePushforward f` of the morphism of small étale ringed topoi
(the spelling of Stacks 08IN and of the Leray identification) are both right derived functors of
the same functor on the homotopy category, so they are canonically isomorphic.

## Main definitions

* `AlgebraicGeometry.Space.totalRightDerivedModulePushforwardIso`: the isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **The two spellings of `Rf_*` agree**: the total right derived functor of the direct image of
modules is the derived direct image of the morphism of small étale ringed topoi, both being right
derived functors of `f_*` with respect to the quasi-isomorphisms. -/
def totalRightDerivedModulePushforwardIso (f : X ⟶ Y) :
    Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) ≅
      derivedModulePushforward B S hS f :=
  Functor.rightDerivedUnique _ _
    ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    (derivedModulePushforwardUnit B S hS f)
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

end AlgebraicGeometry.Space

end
