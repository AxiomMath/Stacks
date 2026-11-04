module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard smooth coverings

A standard smooth covering of an affine scheme is a finite family of standard smooth morphisms
from affine schemes whose images cover the target. These are the covering families of the big
affine smooth site.

## Main definitions

* `AlgebraicGeometry.IsStandardSmoothCovering` — a finite family of morphisms between affine
  schemes is componentwise standard smooth and jointly surjective.

## Implementation notes

The family is indexed by an arbitrary finite type. Affineness of its members and of its target
is recorded by typeclass assumptions, since standard smoothness is only defined for a morphism
of affine schemes, while joint surjectivity is expressed by the union of the set-theoretic
ranges of the underlying continuous maps.

## References

* [Stacks Project, Tag 0223](https://stacks.math.columbia.edu/tag/0223)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- A finite family `fᵢ : Uᵢ ⟶ T` of morphisms between affine schemes is a
**standard smooth covering** if every `fᵢ` is standard smooth and their images
cover `T`. -/
@[stacks 0223] public abbrev IsStandardSmoothCovering {T : Scheme.{u}} [IsAffine T]
    {I : Type v} [Finite I] (U : I → Scheme.{u}) [∀ i, IsAffine (U i)]
    (f : ∀ i, U i ⟶ T) : Prop :=
  (∀ i, IsStandardSmooth (f i)) ∧ (⋃ i, Set.range (f i)) = Set.univ

end AlgebraicGeometry
