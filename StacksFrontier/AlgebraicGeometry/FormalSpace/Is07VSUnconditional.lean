module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersionSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection

/-!
# The affineness hypothesis `Is07VS` of the formal-space tree holds

`AlgebraicGeometry.FormalSpace.Is07VS` is the shape in which the formal-space tree states
**Stacks 07VS**: an algebraic space over `S` receiving a surjective finite morphism from an affine
scheme of the site is an affine scheme. It is the representable-source case of the library's
Stacks 07VS, `AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`, which
carries no hypothesis, so `Is07VS` holds with nothing granted.

## Main results

* `AlgebraicGeometry.FormalSpace.is07VS`: `Is07VS` holds.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`AlgebraicGeometry.FormalSpace.Is07VS` holds**, with nothing granted: it is the
representable-source case of the library's Stacks 07VS,
`AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective`, the source being an
algebraic space by Stacks 025Z and an affine algebraic space because its underlying scheme is
affine. -/
theorem is07VS : Is07VS B S hS := by
  intro F T c hF hTaff hsurj hfin
  exact Space.isAffineSpace_target_of_isFinite_of_isSurjective B S hS c
    (isAlgebraicSpace_yoneda B S hS T) hF hsurj hfin (Space.isAffineSpace_yoneda B S hS T hTaff)

end AlgebraicGeometry.FormalSpace

end
