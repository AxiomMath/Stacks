module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# The range of a surjective closed immersion is a thickening

A closed immersion of algebraic spaces `c : F ⟶ X` over `S` is a monomorphism, so `F` is
identified with its range, a closed subspace of `X`; when `c` is surjective on points, that
closed subspace has all the points of `X`, which is to say it is a thickening of `X`
(Stacks 05ZK, part (1)). If `F` is affine, so is the range.

This is the form in which the statement that an algebraic space receiving a surjective closed
immersion from an affine scheme is affine is reduced to a statement about thickenings.

## Main results

* `AlgebraicGeometry.Space.isThickening_range_of_isSurjective_of_isClosedImmersion`: the range
  of a surjective closed immersion with algebraic source is a thickening.
* `AlgebraicGeometry.Space.isAffineSpace_range_of_isClosedImmersion`: the range of a closed
  immersion with affine source is affine.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The range of a surjective closed immersion is a thickening.** A closed immersion `c` from
an algebraic space has closed range, and every point of the target is the image of a point of
the source, which factors through the range. -/
theorem isThickening_range_of_isSurjective_of_isClosedImmersion
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (X : AlgebraicSpaces B S hS) (c : F ⟶ X.1)
    (hF : IsAlgebraicSpace B S hS F) (hsurj : IsSurjective B S hS c)
    (hci : IsClosedImmersion B S hS c) :
    IsThickening B S hS X (Subfunctor.range c) := by
  refine ⟨isClosedSubspace_range_of_isClosedImmersion B S hS c hF hci, fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  refine ⟨pointsMap B S hS F (Subfunctor.toRange c) y, ?_⟩
  rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]

/-- **The range of a closed immersion with affine source is affine.** A closed immersion is a
monomorphism, so its source is isomorphic to its range. -/
theorem isAffineSpace_range_of_isClosedImmersion
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : F ⟶ X)
    (hF : IsAffineSpace B S hS F) (hci : IsClosedImmersion B S hS c) :
    IsAffineSpace B S hS (Subfunctor.range c).toFunctor := by
  have : Mono c := mono_of_isClosedImmersion B S hS c hci
  exact hF.of_iso (asIso (Subfunctor.toRange c))

end AlgebraicGeometry.Space

end
