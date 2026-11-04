module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite

/-!
# A monomorphism of `𝒪_F`-modules is injective on the sections over a chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`. A
monomorphism of `𝒪_F`-modules is injective on the sections over every object of the small étale
site of `F`: the functor to presheaves of modules preserves monomorphisms, and a monomorphism of
presheaves of modules is sectionwise injective.

This is the small étale ringed site's instance of
`Stacks.SheafOfModules.injective_val_app_of_mono`, which says the same over an arbitrary site.
It is stated here, in one place, because consumers want it in the `𝒪_F`-module vocabulary of
`AlgebraicGeometry.Space.Modules` rather than in the general one.

## Main results

* `AlgebraicGeometry.Space.injective_val_app_of_mono`: the map on sections over a chart induced
  by a monomorphism of `𝒪_F`-modules is injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A monomorphism of `𝒪_F`-modules is injective on the sections over every object of the small
étale site of `F`. -/
theorem injective_val_app_of_mono {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {M N : Modules.{u, u} B S hS F hF} (p : M ⟶ N) [Mono p]
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    Function.Injective (p.val.app U) :=
  Stacks.SheafOfModules.injective_val_app_of_mono p U

end AlgebraicGeometry.Space

end
