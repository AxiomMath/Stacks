module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersionSupplement

/-!
# Algebraic spaces with a surjective closed immersion from an affine scheme

`AlgebraicGeometry.FormalSpace.IsAffineOfSurjectiveClosedImmersion` is the proposition that an
algebraic space receiving a surjective closed immersion from an affine scheme of the site is
affine. It follows from
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineOfSurjectiveClosedImmersion`: an algebraic space
  receiving a surjective closed immersion from an affine scheme of the site is affine.

## References

* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
-/

@[expose] public section

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over `S` receiving a surjective closed immersion from an object of the site
with affine underlying scheme is affine. -/
theorem isAffineOfSurjectiveClosedImmersion : IsAffineOfSurjectiveClosedImmersion B S hS :=
  fun {_ T} c hF hT hsurj hci ↦
    Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace B S hS c
      (isAlgebraicSpace_yoneda B S hS T) hF hci hsurj ⟨T, hT, ⟨CategoryTheory.Iso.refl _⟩⟩

end AlgebraicGeometry.FormalSpace

end
