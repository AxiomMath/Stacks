module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Étale morphisms are open on the points of an algebraic space

Tag 03BX characterizes the topology on the point sets of the algebraic spaces over a scheme
`S` by three properties: it restricts on a scheme to the usual topology, every morphism of
algebraic spaces is continuous on points, and an étale morphism from a scheme is open on
points. The topology itself is constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/PointsTopology.lean` as
`AlgebraicGeometry.Space.pointTopology`, where the first two properties are proved. This
file proves the third.

## Main results

* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafEtale` is clause (3) of Tag 03BX:
  a morphism of presheaves each of whose represented base changes is étale is open on
  points.
* `AlgebraicGeometry.Space.isQuotientMap_pointsMap_of_presheafEtale` and
  `AlgebraicGeometry.Space.pointTopology_eq_coinduced_of_presheafEtale`: such a morphism
  which is in addition surjective on points is a quotient map on points, so the point
  topology of the target is the quotient topology of an étale atlas.

## Implementation notes

The hypothesis is stated for an arbitrary morphism of presheaves, not only for one out of a
represented presheaf as in the source: representability of the *source* is never used, only
relative representability of the morphism, which is part of
`CategoryTheory.MorphismProperty.presheaf`. Clause (3) of Tag 03BX is the instance of
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafEtale` at a representable source,
and the algebraicity hypothesis on the target that the source carries is not needed either,
because `AlgebraicGeometry.Space.pointTopology` is defined for every presheaf.

No declaration here carries `@[stacks 03BX]`, for the reason given in
`StacksFrontier/AlgebraicGeometry/Spaces/PointsTopology.lean`: the content of that tag is the
existence *and uniqueness* of the family of topologies, and a single clause of the
characterization is not that statement. What this file adds is that the three clauses are
now all available for `AlgebraicGeometry.Space.pointTopology`, so that construction is a
family of the kind Tag 03BX asserts to exist. The quotient-topology description that follows
is the uniqueness argument's one geometric step: an étale atlas is open and continuous on
points, hence a quotient map as soon as it is surjective on points, which for an atlas of an
algebraic space is Tag 03H5
(`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`). Any family of
topologies satisfying the three clauses therefore agrees with `pointTopology` on every
algebraic space, since both are the quotient topology of one and the same atlas.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of presheaves on the big fppf site of `S` each of whose represented base
changes is étale has all of its represented base changes open, because an étale morphism of
schemes is flat and locally of finite presentation, hence universally open. -/
@[sga "3 X 4.7" "more general"]
theorem presheafIsOpenMap_of_presheafEtale (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
  ⟨hf.rep, fun _ _ g fst snd sq ↦ by
    have : Etale ((BigFppfOver.toScheme B S hS).map snd) := hf.property g fst snd sq
    exact Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map snd)⟩

/-- **Stacks 03BX, clause (3).** A morphism of presheaves on the big fppf site of `S` each of
whose represented base changes is an étale morphism of schemes is open on the point sets of
Tag 03BU.

Clause (3) of Tag 03BX is the case of a representable source and an algebraic space as
target; neither hypothesis is used. -/
theorem isOpenMap_pointsMap_of_presheafEtale (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    @IsOpenMap _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) :=
  isOpenMap_pointsMap_of_presheafIsOpenMap B S hS f
    (presheafIsOpenMap_of_presheafEtale B S hS f hf)

/-- An étale morphism of presheaves which is surjective on points is a quotient map on
points: it is open and continuous, so the point topology of the target is the quotient
topology. -/
@[sga "1 IX 2.2" "special case"]
theorem isQuotientMap_pointsMap_of_presheafEtale (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hsurj : Function.Surjective (pointsMap B S hS F f)) :
    @Topology.IsQuotientMap _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) :=
  @IsOpenMap.isQuotientMap _ _ (pointsMap B S hS F f)
    (pointTopology B S hS F) (pointTopology B S hS G)
    (isOpenMap_pointsMap_of_presheafEtale B S hS f hf) (continuous_pointsMap B S hS f) hsurj

/-- The point topology of a presheaf which receives an étale morphism, surjective on points,
is the quotient topology of the point topology of the source. -/
theorem pointTopology_eq_coinduced_of_presheafEtale (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hsurj : Function.Surjective (pointsMap B S hS F f)) :
    pointTopology B S hS G =
      TopologicalSpace.coinduced (pointsMap B S hS F f) (pointTopology B S hS F) := by
  let _ : TopologicalSpace (points B S hS F) := pointTopology B S hS F
  let _ : TopologicalSpace (points B S hS G) := pointTopology B S hS G
  exact (isQuotientMap_pointsMap_of_presheafEtale B S hS f hf hsurj).eq_coinduced

end AlgebraicGeometry.Space

end
