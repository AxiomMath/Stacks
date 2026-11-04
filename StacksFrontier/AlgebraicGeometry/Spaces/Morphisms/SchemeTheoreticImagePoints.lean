module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# Points of the scheme-theoretic image

The scheme-theoretic image of Stacks 082X is a closed subspace of the target, so its set of
points is closed in the point space of Tag 03BU by Stacks 04CD; since the morphism factors
through it, that point set contains the closure of the image of the point map. This is the
inclusion which the identification of the image of a morphism out of a reduced algebraic space
with the reduced closed subspace on that closure consumes, and it holds with no reducedness
hypothesis at all.

Degenerate sources are the other extreme. The sheafification of the bottom subfunctor is the
open subspace with no points, and it is in addition a *closed* subspace of an algebraic space:
it is the subspace cut out by the empty set of points, which is clopen, so the criterion of
Stacks 02YU for the pieces of a clopen decomposition applies. Minimality of the
scheme-theoretic image then puts the image of a morphism whose source has no points inside it,
and monotonicity of the point set along containment of subfunctors shows that any subfunctor so
contained has no points.

## Main results

  the closure of the image of the point map of a morphism is contained in the set of points of
  its scheme-theoretic image.
* `AlgebraicGeometry.Space.isClosedSubspace_sheafify_bot`: the sheafified bottom subfunctor is
  a closed subspace of an algebraic space.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_le_sheafify_bot_of_isEmpty_points`:
  the scheme-theoretic image of a morphism whose source has no points is contained in the
  sheafified bottom subfunctor.
* `AlgebraicGeometry.Space.range_pointsMap_ι_eq_empty_of_le_sheafify_bot`: a subfunctor
  contained in the sheafified bottom subfunctor has no points.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 0830](https://stacks.math.columbia.edu/tag/0830)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The sheafification of the bottom subfunctor of an algebraic space is a closed subspace: it
is the subspace cut out by the empty set of points, which is both open and closed. -/
theorem isClosedSubspace_sheafify_bot (hY : IsAlgebraicSpace B S hS Y) :
    IsClosedSubspace B S hS ((⊥ : Subfunctor Y).sheafify (BigFppfOver.topology B S hS)) := by
  rw [← openSubspaceOfPoints_empty B S hS Y]
  exact isClosedSubspace_openSubspaceOfPoints B S hS hY _ isOpen_empty isClosed_empty

/-- The scheme-theoretic image of a morphism whose source has no points is contained in the
sheafified bottom subfunctor, the empty closed subspace of the target: the morphism factors
through the subspace cut out by the image of its point map, which is the empty set. -/
theorem schemeTheoreticImageSubfunctor_le_sheafify_bot_of_isEmpty_points
    (f : X ⟶ Y) (hY : IsAlgebraicSpace B S hS Y) (hX : IsEmpty (points B S hS X)) :
    schemeTheoreticImageSubfunctor B S hS f ≤
      (⊥ : Subfunctor Y).sheafify (BigFppfOver.topology B S hS) := by
  refine schemeTheoreticImageSubfunctor_le B S hS f (isClosedSubspace_sheafify_bot B S hS hY) ?_
  have h := range_le_openSubspaceOfPoints_range_pointsMap f
  rwa [Set.range_eq_empty_iff.2 hX, openSubspaceOfPoints_empty B S hS Y] at h

/-- A subfunctor contained in the sheafified bottom subfunctor has no points, the point set of
a subspace growing with the subspace. -/
theorem range_pointsMap_ι_eq_empty_of_le_sheafify_bot {Z : Subfunctor Y}
    (hZ : Z ≤ (⊥ : Subfunctor Y).sheafify (BigFppfOver.topology B S hS)) :
    Set.range (pointsMap B S hS Z.toFunctor Z.ι) = ∅ := by
  have h := range_pointsMap_ι_le B S hS hZ
  rwa [range_pointsMap_ι_sheafify_bot B S hS Y, Set.subset_empty_iff] at h

end AlgebraicGeometry.Space

end
