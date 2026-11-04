module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Density of a representable base change on points

Let `q : h_U ⟶ F` be an étale representable morphism to a presheaf on the big fppf site of
`S` and let `f : h_V ⟶ F` be a morphism whose image on the point set of `F` is dense. If the
fibre product of `q` and `f` is represented by `W` with projections `i : W ⟶ U`, `g : W ⟶ V`,
then the image of `i` on the underlying topological space of `U` is dense.

This is the step by which a dense open subspace of an algebraic space produces a dense open
subscheme of a chart: the chart is étale, so it is open on points, and preimages of dense
sets along open maps are dense.

## Main results

* `AlgebraicGeometry.Space.denseRange_pointsMap_yonedaMap_of_isPullback`: density of the
  base change on the point sets.
* `AlgebraicGeometry.Space.denseRange_toScheme_map_of_isPullback`: density of the base change
  on the underlying topological space of the chart.

## Implementation notes

On point sets the image of the base change is the preimage along `q` of the image of `f`:
that is `AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback` taken at the whole
point set of `W`. Openness of `q` on points is clause (3) of Stacks 03BX,
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafEtale`, and needs nothing of `F`.

Passing from the point set of `h_U` to the underlying space of `U` is the homeomorphism
`AlgebraicGeometry.Space.schemePointsHomeomorph`, which is natural in `U` by
`AlgebraicGeometry.Space.pointsToScheme_pointsMap`; the image of a dense set under a
homeomorphism is dense.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W U V : BigFppfOver B S hS}

/-- **Density of a representable base change on point sets.** If the fibre product of an
étale morphism `q : h_U ⟶ F` with `f : h_V ⟶ F` is represented by `W`, and `f` has dense
image on the point set of `F`, then the first projection `i : W ⟶ U` has dense image on the
point set of `h_U`.

The image of `i` on points is the preimage along `q` of the image of `f`, and `q` is open on
points because it is étale. -/
theorem denseRange_pointsMap_yonedaMap_of_isPullback
    (i : W ⟶ U) (g : W ⟶ V) (q : yoneda.obj U ⟶ F) (f : yoneda.obj V ⟶ F)
    (hsq : IsPullback (yoneda.map i) (yoneda.map g) q f)
    (hq : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hdense : Dense (Set.range (pointsMap B S hS (yoneda.obj V) f))) :
    Dense (Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map i))) := by
  have h := preimage_image_pointsMap_of_isPullback B S hS hsq.flip Set.univ
  rw [Set.image_univ, Set.preimage_univ, Set.image_univ] at h
  rw [← h]
  exact hdense.preimage (isOpenMap_pointsMap_of_presheafEtale B S hS q hq)

/-- **Density of a representable base change on the underlying space of the chart.** In the
situation of `denseRange_pointsMap_yonedaMap_of_isPullback`, the first projection
`i : W ⟶ U` has dense image on the underlying topological space of `U`.

The point set of `h_U` is homeomorphic to that space, naturally in `U`. -/
theorem denseRange_toScheme_map_of_isPullback
    (i : W ⟶ U) (g : W ⟶ V) (q : yoneda.obj U ⟶ F) (f : yoneda.obj V ⟶ F)
    (hsq : IsPullback (yoneda.map i) (yoneda.map g) q f)
    (hq : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hdense : Dense (Set.range (pointsMap B S hS (yoneda.obj V) f))) :
    Dense (Set.range ((BigFppfOver.toScheme B S hS).map i)) := by
  set eU := schemePointsHomeomorph B S hS U with heU
  set eW := schemePointsHomeomorph B S hS W with heW
  have hnat (w : points B S hS (yoneda.obj W)) :
      eU (pointsMap B S hS (yoneda.obj W) (yoneda.map i) w) =
        (BigFppfOver.toScheme B S hS).map i (eW w) := by
    rw [heU, heW, schemePointsHomeomorph_apply, schemePointsHomeomorph_apply]
    exact pointsToScheme_pointsMap B S hS i w
  have himage : eU '' Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map i)) =
      Set.range ((BigFppfOver.toScheme B S hS).map i) := by
    ext y
    constructor
    · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨eW w, (hnat w).symm⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := eW.surjective z
      exact ⟨_, ⟨w, rfl⟩, hnat w⟩
  rw [← himage]
  exact eU.surjective.denseRange.dense_image eU.continuous
    (denseRange_pointsMap_yonedaMap_of_isPullback B S hS i g q f hsq hq hdense)

end AlgebraicGeometry.Space

end
