module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Invariant closed subspaces of a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, in the sense of Stacks 043W. A subspace of the space of objects of `G` is *invariant*
when its two inverse images along the source and the target map agree, as in Stacks 044F. This
file adds the *closed* case of that notion, which Stacks 044F does not itself spell out: it
states invariance for open subspaces, for locally closed subspaces, and for monomorphisms.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantClosed`: invariance of a closed
  subspace of the object space.

## Main results

* `AlgebraicGeometry.Space.isLocallyClosedSubspace_of_isClosedSubspace`: a closed subspace is a
  locally closed subspace.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInvariantLocallyClosed_of_isInvariantClosed`:
  an invariant closed subspace is an invariant locally closed subspace, so this notion refines
  Stacks 044F part (2) rather than standing beside it.

## Implementation notes

The definition follows its locally closed sibling `IsInvariantLocallyClosed` exactly, with
closedness of the subspace in place of local closedness and the same equality of inverse images;
like that sibling it *includes* the condition that the subfunctor be a subspace of the relevant
kind, and is not the bare inverse-image condition.

The refinement result is the presheaf-level transport of the containment of scheme morphism
properties `AlgebraicGeometry.Space.isClosedImmersion_le_isImmersion`, taken from
`StacksFrontier/AlgebraicGeometry/Spaces/SeparatedVariants.lean` and pushed through
`CategoryTheory.MorphismProperty.monotone_inverseImage` and then through
`CategoryTheory.MorphismProperty.relative_monotone`. It is stated for subspaces of an arbitrary
presheaf rather than only for object spaces of a groupoid, since nothing in it is about the
groupoid.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}

namespace Space

/-- A closed subspace of a presheaf on the big fppf site of `S` is a locally closed subspace:
the inclusion of a closed subspace is a closed immersion, hence an immersion. -/
theorem isLocallyClosedSubspace_of_isClosedSubspace
    {F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F)
    (h : IsClosedSubspace site S hS G) : IsLocallyClosedSubspace site S hS G :=
  ⟨h.1, MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage _ isClosedImmersion_le_isImmersion) _ h.2⟩

end Space

namespace GroupoidInAlgebraicSpaces

variable {B : AlgebraicSpaces site S hS}

/-- A closed subspace of the object space of a groupoid in algebraic spaces is *invariant* when
its inverse images under the source and the target map agree as subspaces of the space of
arrows. This is the closed case of the invariance of Stacks 044F. -/
abbrev IsInvariantClosed (G : GroupoidInAlgebraicSpaces site S hS B)
    (Z : Subfunctor G.objects.obj) : Prop :=
  Space.IsClosedSubspace site S hS Z ∧
    Z.preimage G.target.hom = Z.preimage G.source.hom

/-- An invariant closed subspace is an invariant locally closed subspace, so the closed case
refines Stacks 044F part (2). -/
theorem isInvariantLocallyClosed_of_isInvariantClosed
    (G : GroupoidInAlgebraicSpaces site S hS B) (Z : Subfunctor G.objects.obj)
    (h : IsInvariantClosed G Z) : IsInvariantLocallyClosed G Z :=
  ⟨Space.isLocallyClosedSubspace_of_isClosedSubspace Z h.1, h.2⟩

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
