module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.RestrictionArrows

/-!
# Invariant subspaces of a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`.
A subspace of `U` is *invariant* when it is stable under the groupoid, that is when an arrow
whose source lies in it has its target in it too. The condition takes three forms, for an open
subspace, for a locally closed subspace, and for an arbitrary monomorphism into the object
space.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantOpen`: invariance of an open
  subspace, `s⁻¹(W) ≤ t⁻¹(W)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantLocallyClosed`: invariance of a
  locally closed subspace, `t⁻¹(Z) = s⁻¹(Z)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantMonomorphism`: invariance of a
  monomorphism, an isomorphism over `R` between its two base changes.

All three are imported from
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubspaces` and re-exported here, so
that the stabilizer development can use them alongside
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.fiberProductFst` and `fiberProductSnd`, in terms
of which `IsInvariantMonomorphism` reads as an isomorphism between the two chosen fibre
products.

## Implementation notes

For an open subspace one inclusion of inverse images suffices: an arrow of a groupoid has an
inverse, so stability under the source-to-target direction already forces equality. For a
locally closed subspace the source definition asks for equality, and that is what is stated.

The inverse images are `CategoryTheory.Subfunctor.preimage`, taken along the source and target
morphisms of presheaves, so that the condition can be read directly on the points of any test
object. For a monomorphism the two base changes are the chosen fibre products of `i` with the
target and of the source with `i`, each with its projection to `R`; equality of subspaces of
`R` is an isomorphism in the slice over `R`, and the monomorphism hypothesis makes such an
isomorphism unique when it exists, so the condition is a proposition in substance as well as
in form.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
-/
