module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoidRestriction

/-!
# The restriction square along an invariant subspace is cartesian

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, in the sense of Stacks 043W, and let `Z` be an invariant subspace of its space of
objects in the sense of Stacks 044F. The restriction of `G` along the inclusion of `Z`
(Stacks 044B) has as its space of arrows the arrows of `G` with both endpoints lifted to `Z`, and
invariance makes each of the two lifts redundant: the space of restricted arrows is the inverse
image of `Z` under the source map, and also the inverse image of `Z` under the target map.

This file upgrades those two identifications from isomorphisms of algebraic spaces to the two
cartesian squares they say exist:

```
R_Z ⟶ R        R_Z ⟶ R
 |     |         |     |
 s     s         t     t
 v     v         v     v
 Z  ⟶  U        Z  ⟶  U
```

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_restrictionSource_of_preimage_le` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_restrictionTarget_of_preimage_le`: the
  two squares, each from the one inclusion of inverse images that it needs.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_restrictionSource_of_isInvariantOpen`,
  and, in the namespace `AlgebraicGeometry.GroupoidInAlgebraicSpaces`,
  `isPullback_restrictionSource_of_isInvariantLocallyClosed` and
  `isPullback_restrictionTarget_of_isInvariantLocallyClosed`: the same squares from the invariance
  hypotheses of Stacks 044F as they are stated there.

## What this is for

The square with the source maps is **exactly the hypothesis of Stacks 04ZN**, which asks of a
morphism of groupoids in algebraic spaces that the square formed by its map on arrows, its map on
objects and the two source maps be cartesian, and concludes that the square of quotient stacks
obtained from it is a 2-fibre product. Stacks 04ZN itself is
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare_of_isPullback`, and the general
identification of the 2-fibre product of a 1-morphism of quotient stacks with the projection of
the target on which the source's proof of it rests, Stacks 04Y4, is
`AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare`. Nothing
here concludes anything about quotient stacks. What is settled here is the one input to
Stacks 04ZN that is unconditional, the geometry of the restriction.

Stacks 04ZN's proof begins by applying the inverse morphisms of the two groupoids to the
cartesian square of its hypothesis to obtain the square with the target maps, which is why both
squares are proved here rather than only the first.

## Implementation notes

The two isomorphisms are
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_fiberProductSnd_restrictionArrows` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_fiberProductFst_restrictionArrows`, each a
projection of the space of restricted arrows onto one of the two inverse images, and each already
proved from the corresponding one-sided invariance condition. So each square here is the
cartesian square of
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` transported along that isomorphism,
and the two legs of the restriction are the two projections of the inverse image read through it —
the source and target lifts by definition, and the map to the arrows of `G` by the defining
compatibility of the fibre product of the two inverse images.

The isomorphism is formed with `@CategoryTheory.asIso` applied to the `IsIso` hypothesis by name
rather than left to instance search: the domain of that morphism is the fibre product written out,
while the square being proved is stated with
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows`, and the two agree only after
unfolding that definition, which instance search does not do.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}
  (G : GroupoidInAlgebraicSpaces C S hS B) (Z : Subfunctor G.objects.obj)
  (hZ : IsAlgebraicSpace C S hS Z.toFunctor)

/-- The space of arrows of the restriction of a groupoid in algebraic spaces along the inclusion
of a subspace `Z` of its object space satisfying `s⁻¹(Z) ≤ t⁻¹(Z)` is the inverse image of `Z`
under the source map: the square formed by the projection to the arrows of the groupoid, the
source map of the restriction, the source map of the groupoid and the inclusion of `Z` is
cartesian.

This is the hypothesis of Stacks 04ZN for the restriction of a groupoid along an invariant
subspace. -/
theorem isPullback_restrictionSource_of_preimage_le
    (hinv : Z.preimage G.source.hom ≤ Z.preimage G.target.hom) :
    IsPullback (restrictionArrowsToArrows G (subspaceInclusion G Z hZ))
      (restrictionSource G (subspaceInclusion G Z hZ)) G.source
      (subspaceInclusion G Z hZ) := by
  have h := isIso_fiberProductSnd_restrictionArrows G Z hZ hinv
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source
      (subspaceInclusion G Z hZ)).of_iso' (@asIso _ _ _ _ _ h)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Category.comp_id, Iso.refl_hom]
    exact (fiberProduct_condition (fiberProductSnd (subspaceInclusion G Z hZ) G.target)
      (fiberProductFst G.source (subspaceInclusion G Z hZ))).symm
  all_goals simp <;> rfl

/-- The space of arrows of the restriction of a groupoid in algebraic spaces along the inclusion
of a subspace `Z` of its object space satisfying `t⁻¹(Z) ≤ s⁻¹(Z)` is the inverse image of `Z`
under the target map: the square formed by the projection to the arrows of the groupoid, the
target map of the restriction, the target map of the groupoid and the inclusion of `Z` is
cartesian.

This is the square Stacks 04ZN's proof obtains from the square of its hypothesis by applying the
inverse morphisms of the two groupoids. -/
theorem isPullback_restrictionTarget_of_preimage_le
    (hinv : Z.preimage G.target.hom ≤ Z.preimage G.source.hom) :
    IsPullback (restrictionArrowsToArrows G (subspaceInclusion G Z hZ))
      (restrictionTarget G (subspaceInclusion G Z hZ)) G.target
      (subspaceInclusion G Z hZ) := by
  have h := isIso_fiberProductFst_restrictionArrows G Z hZ hinv
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (subspaceInclusion G Z hZ) G.target).flip.of_iso' (@asIso _ _ _ _ _ h)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp <;> rfl

/-- **The hypothesis of Stacks 04ZN for an invariant open subspace.** For an invariant open
subspace of the object space of a groupoid in algebraic spaces (Stacks 044F, part (1)) the square
formed by the two source maps and the restriction is cartesian. Only the one-sided invariance
condition that part (1) states is used. -/
theorem isPullback_restrictionSource_of_isInvariantOpen (hZ : IsInvariantOpen G Z) :
    IsPullback (restrictionArrowsToArrows G (subspaceInclusion G Z hZ.1.1))
      (restrictionSource G (subspaceInclusion G Z hZ.1.1)) G.source
      (subspaceInclusion G Z hZ.1.1) :=
  isPullback_restrictionSource_of_preimage_le G Z hZ.1.1 hZ.2

/-- **The hypothesis of Stacks 04ZN for an invariant locally closed subspace.** For an invariant
locally closed subspace of the object space of a groupoid in algebraic spaces (Stacks 044F,
part (2)) the square formed by the two source maps and the restriction is cartesian. -/
theorem isPullback_restrictionSource_of_isInvariantLocallyClosed
    (hZ : IsInvariantLocallyClosed G Z) :
    IsPullback (restrictionArrowsToArrows G (subspaceInclusion G Z hZ.1.1))
      (restrictionSource G (subspaceInclusion G Z hZ.1.1)) G.source
      (subspaceInclusion G Z hZ.1.1) :=
  isPullback_restrictionSource_of_preimage_le G Z hZ.1.1 hZ.2.ge

/-- For an invariant locally closed subspace of the object space of a groupoid in algebraic spaces
(Stacks 044F, part (2)) the square formed by the two **target** maps and the restriction is
cartesian. Unlike the open case this needs the full equality of inverse images, which is what
part (2) states. -/
theorem isPullback_restrictionTarget_of_isInvariantLocallyClosed
    (hZ : IsInvariantLocallyClosed G Z) :
    IsPullback (restrictionArrowsToArrows G (subspaceInclusion G Z hZ.1.1))
      (restrictionTarget G (subspaceInclusion G Z hZ.1.1)) G.target
      (subspaceInclusion G Z hZ.1.1) :=
  isPullback_restrictionTarget_of_preimage_le G Z hZ.1.1 hZ.2.le

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
