module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# `Rf_*` commutes with derived limits on algebraic spaces

For a morphism `f : X ⟶ Y` of algebraic spaces, the derived direct image
`Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` carries a derived limit `K = R lim Kₙ` of a countable inverse system to
a derived limit of the image system (Stacks 0A07): `Rf_*` is exact, and it is a right adjoint, of
`Lf^*`, so it preserves the countable product.

## Main results

* `AlgebraicGeometry.Space.isDerivedLimit_spaceDerivedPushforward`: Stacks 0A07 for a morphism of
  algebraic spaces.

## References

* [Stacks Project, Tag 0A07](https://stacks.math.columbia.edu/tag/0A07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-- **`Rf_*` carries derived limits to derived limits** (Stacks 0A07 for a morphism of algebraic
spaces): it is exact and a right adjoint. -/
theorem isDerivedLimit_spaceDerivedPushforward {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : ℕᵒᵖ ⥤ spaceDerivedCategory B S hS X) [HasProduct fun n : ℕ => M.obj ⟨n⟩]
    (K : spaceDerivedCategory B S hS X) (hK : IsDerivedLimit M K) :
    ∃ _ : HasProduct (fun n : ℕ => (spaceDerivedPushforward B S hS f).obj (M.obj ⟨n⟩)),
      IsDerivedLimit (M ⋙ spaceDerivedPushforward B S hS f)
        ((spaceDerivedPushforward B S hS f).obj K) :=
  have := (smallEtaleDerivedPullPushAdjunction B S hS f).isRightAdjoint
  Stacks.Injectives.isDerivedLimit_map_rightAdjoint _ M K hK

end AlgebraicGeometry.Space

end
