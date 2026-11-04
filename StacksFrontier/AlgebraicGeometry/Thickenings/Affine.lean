module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromFiniteSurjective
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Affineness of a thickening

Any thickening of an affine scheme is affine. A thickening is a closed immersion, hence a finite
morphism, and it is surjective, so the target of a finite surjective morphism with affine source
is affine.

## Main results

* `Stacks.Thickenings.isAffine_of_isThickening`: the ambient scheme of a thickening of an affine
  scheme is affine.
* `Stacks.Thickenings.forall_isAffine_of_isThickening`: the same statement with all its data
  universally quantified.

## References

* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

/-- **A thickening of an affine scheme is affine.** A closed immersion is a finite morphism, and
a thickening is surjective, so this is the affineness of the target of a finite surjective
morphism with affine source. -/
@[stacks 06AD]
theorem isAffine_of_isThickening {X X' : Scheme.{u}} {i : X ⟶ X'} (hi : IsThickening i)
    [IsAffine X] : IsAffine X' :=
  have := hi.1
  have : Surjective i := ⟨hi.2⟩
  AffineFromFiniteSurjective.isAffine_of_finite_surjective i

/-- A thickening of an affine scheme is affine, with the two schemes and the morphism
universally quantified and affineness of the closed subscheme an explicit hypothesis. -/
theorem forall_isAffine_of_isThickening :
    ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z' :=
  fun _ _ _ hk hZ ↦ @isAffine_of_isThickening _ _ _ hk hZ

end Stacks.Thickenings

end
