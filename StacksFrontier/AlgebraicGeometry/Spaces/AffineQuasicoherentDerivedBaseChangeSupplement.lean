module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleKFlat
public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangePathComparison
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import all StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange

/-!
# The ring map of global functions along a morphism of affine objects

For a morphism `g : U' ⟶ U` of objects of the big fppf site over `S` whose underlying schemes are
affine, this file defines the induced map of rings of global functions `Γ(U, 𝒪) ⟶ Γ(U', 𝒪)`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineRingCatHom`: the map `Γ(U, 𝒪) ⟶ Γ(U', 𝒪)` induced
  by `g`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- The map of rings of global functions `Γ(U, 𝒪) ⟶ Γ(U', 𝒪)` induced by `g : U' ⟶ U`. -/
abbrev representedAffineRingCatHom :
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⟶ Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
  Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map g)

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

end AlgebraicGeometry.Space
