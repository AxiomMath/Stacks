module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation
import all StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation

/-!
# Relative approximation from small Noetherian approximations

The construction proving Stacks 0GS3 in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation` aligns a small Noetherian
approximation of the source with one of the target. This file states it for any two given small
approximations, with no hypothesis on the other spaces of the site: a morphism `f : X ⟶ Y` of
algebraic spaces over `Spec ℤ` whose source and target have small Noetherian approximations is the
limit of an inverse system of morphisms of quasi-separated algebraic spaces of finite type over
`Spec ℤ` with affine transition morphisms.

## Main results

* `AlgebraicGeometry.Space.hasRelativeApproximation_of_hasSmallNoetherianApproximation`.

## References

* [Stacks Project, Tag 0GS3](https://stacks.math.columbia.edu/tag/0GS3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Relative approximation from small Noetherian approximations of the source and the target.**
A morphism `f : X ⟶ Y` of algebraic spaces over `Spec ℤ` whose source and target are limits of
inverse systems of quasi-separated algebraic spaces of finite type over `Spec ℤ` with affine
transition morphisms, indexed by sets small for the site, is the limit of an inverse system of such
morphisms (the conclusion of Stacks 0GS3). -/
theorem hasRelativeApproximation_of_hasSmallNoetherianApproximation (B : BigFppfSite.{u})
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hAX : HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)
    (hAY : HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ Y) :
    HasRelativeApproximation B hZ f := by
  obtain ⟨A, hA⟩ := hAX
  obtain ⟨C, hC⟩ := hAY
  exact ⟨relativeApproximationOfStageSystems f hX (stageSystem B hZ A hA)
    (stageSystem B hZ C hC)⟩

end AlgebraicGeometry.Space

end
