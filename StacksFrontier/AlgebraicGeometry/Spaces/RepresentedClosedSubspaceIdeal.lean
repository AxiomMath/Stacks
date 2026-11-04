module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimageSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingAffineSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# A closed subscheme of a scheme in the site, as a closed subspace of the space it represents

Let `S` be a scheme contained in a big fppf site `B` and let `j : R ⟶ V` be a morphism of the
big fppf category over `S` whose underlying morphism of schemes is a closed immersion.  By
`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map` the range of `yoneda.map j` is a
closed subspace of `yoneda.obj V`.  This file packages that construction and identifies its
inclusion.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceRange`: the range of `yoneda.map j`, bundled as an
  element of `AlgebraicGeometry.Space.ClosedSubspaces`.
* `AlgebraicGeometry.Space.rangeSpaceIso`: the isomorphism of algebraic spaces between
  `yoneda.obj R` and that closed subspace.

## Main results

* `AlgebraicGeometry.Space.rangeSpaceIso_hom_comp_subspaceInclusion`: **the inclusion of the
  closed subspace, composed with that isomorphism, is the represented morphism.**  This is what
  lets a statement about `AlgebraicGeometry.Space.subspaceInclusion` of the range be read as a
  statement about `AlgebraicGeometry.Space.representedSpaceMap`, which is the form the
  comparison with the small étale site of the representing scheme is stated at.

## Implementation notes

Both halves below are extracted from the proof of
`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`, which establishes them inline and
discards them: that `yoneda.map j` is a monomorphism, so that
`CategoryTheory.Subfunctor.toRange` is an isomorphism, and that the inverse of that isomorphism
followed by `yoneda.map j` is the inclusion of the range.  Five call sites of that theorem
rebuild the closed-subspace witness inline rather than naming it; `closedSubspaceRange` is the
bundled form.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison of the Yoneda image of a closed immersion of the site with its range is an
isomorphism**, that image being a monomorphism. -/
theorem isIso_toRange_yoneda_map {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    IsIso (Subfunctor.toRange (yoneda.map j)) :=
  have := mono_yoneda_map_of_isClosedImmersion j hj
  inferInstance

/-- **A closed subscheme of a scheme in the site, as a closed subspace of the algebraic space
that scheme represents.**  The bundled form of
`AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map`. -/
noncomputable def closedSubspaceRange {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    ClosedSubspaces B S hS (yoneda.obj V) :=
  ⟨Subfunctor.range (yoneda.map j), isClosedSubspace_range_yoneda_map B S hS j hj⟩

/-- The algebraic space underlying `AlgebraicGeometry.Space.closedSubspaceRange`. -/
noncomputable abbrev closedSubspaceRangeSpace {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    AlgebraicSpaces B S hS :=
  ⟨(closedSubspaceRange B S hS j hj).1.toFunctor,
    (closedSubspaceRange B S hS j hj).2.1⟩

/-- **The presheaf represented by `R` is the range of `yoneda.map j`.**  The comparison
`CategoryTheory.Subfunctor.toRange` is an isomorphism because `yoneda.map j` is a
monomorphism. -/
noncomputable def rangeIsoPresheaf {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    yoneda.obj R ≅ (Subfunctor.range (yoneda.map j)).toFunctor :=
  haveI : Mono (yoneda.map j) := mono_yoneda_map_of_isClosedImmersion j hj
  asIso (Subfunctor.toRange (yoneda.map j))

/-- The forward map of `AlgebraicGeometry.Space.rangeIsoPresheaf` is
`CategoryTheory.Subfunctor.toRange`. -/
@[simp]
theorem rangeIsoPresheaf_hom {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    (rangeIsoPresheaf B S hS j hj).hom = Subfunctor.toRange (yoneda.map j) :=
  rfl

/-- **The algebraic space represented by `R` is the closed subspace cut out by `j`.**  The
isomorphism is `AlgebraicGeometry.Space.rangeIsoPresheaf`, read in the full subcategory of
algebraic spaces. -/
noncomputable def rangeSpaceIso {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    (⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩ : AlgebraicSpaces B S hS) ≅
      closedSubspaceRangeSpace B S hS j hj where
  hom := ObjectProperty.homMk (rangeIsoPresheaf B S hS j hj).hom
  inv := ObjectProperty.homMk (rangeIsoPresheaf B S hS j hj).inv
  hom_inv_id := (ObjectProperty.ι (IsAlgebraicSpace B S hS)).map_injective
    (rangeIsoPresheaf B S hS j hj).hom_inv_id
  inv_hom_id := (ObjectProperty.ι (IsAlgebraicSpace B S hS)).map_injective
    (rangeIsoPresheaf B S hS j hj).inv_hom_id

/-- The underlying morphism of presheaves of `AlgebraicGeometry.Space.rangeSpaceIso` is
`CategoryTheory.Subfunctor.toRange`. -/
@[simp]
theorem rangeSpaceIso_hom_hom {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    (rangeSpaceIso B S hS j hj).hom.hom = Subfunctor.toRange (yoneda.map j) :=
  rfl

/-- **The inclusion of the closed subspace cut out by `j`, read as the represented morphism.**
Composing the inclusion of `AlgebraicGeometry.Space.closedSubspaceRange` with the isomorphism
`AlgebraicGeometry.Space.rangeSpaceIso` gives the morphism of algebraic spaces represented by
`j`.

This is the form a consumer needs.  The conormal module and the defining ideal sheaf of a closed
subspace are stated against `AlgebraicGeometry.Space.subspaceInclusion`, while the comparison of
the small étale site of a representable algebraic space with the small étale site of the
representing scheme is stated against `AlgebraicGeometry.Space.representedSpaceMap`; this is the
identification that carries a statement from either shape to the other. -/
theorem rangeSpaceIso_hom_comp_subspaceInclusion {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)) :
    (rangeSpaceIso B S hS j hj).hom ≫
        subspaceInclusion B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
          (closedSubspaceRange B S hS j hj) =
      representedSpaceMap B S hS j :=
  (ObjectProperty.ι (IsAlgebraicSpace B S hS)).map_injective (Subfunctor.toRange_ι (yoneda.map j))

end AlgebraicGeometry.Space

end
