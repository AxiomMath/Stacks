module

public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension

/-!
# The dimension of the local ring of an algebraic space is invariant under isomorphism

An isomorphism of presheaves `f : F ⟶ G` on the big fppf site composes the étale scheme charts of
`F` above a point `x` into étale scheme charts of `G` above the image of `x`, selecting the same
scheme points, and its inverse does the converse. So the one-chart condition of Tag 0BAM, and
with it the dimension of the local ring at a point, is unchanged.

## Main results

* `AlgebraicGeometry.Space.hasChartLocalRingDimension_pointsMap_of_isIso`: the one-chart
  condition is unchanged by an isomorphism of presheaves.
* `AlgebraicGeometry.Space.localRingDimension_pointsMap_of_isIso` and
  `AlgebraicGeometry.Space.localRingDimension_pointsMap_iso_hom`: the dimension of the local
  ring is unchanged by an isomorphism of presheaves.

## References

* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale scheme chart of `F` above `x` composes with an isomorphism `f : F ⟶ G` to an
étale scheme chart of `G` above the image of `x`, selecting the same scheme point. -/
private theorem hasChartLocalRingDimension_pointsMap_of_isIso_aux
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [IsIso f] (x : points B S hS F) (d : ℕ∞)
    (h : HasChartLocalRingDimension B S hS x d) :
    HasChartLocalRingDimension B S hS (pointsMap B S hS F f x) d := by
  obtain ⟨U, a, u, ha, ⟨p, rfl, hp⟩, hdim⟩ := h
  refine ⟨U, a ≫ f, _, MorphismProperty.RespectsIso.postcomp _ f a ha, ⟨p, rfl, ?_⟩, hdim⟩
  rw [pointsMap_comp, Function.comp_apply, hp]

/-- An isomorphism of presheaves matches the étale scheme charts above a point with those
above its image, so the one-chart condition of Tag 0BAM is unchanged. -/
theorem hasChartLocalRingDimension_pointsMap_of_isIso
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [IsIso f] (x : points B S hS F)
    (d : ℕ∞) :
    HasChartLocalRingDimension B S hS (pointsMap B S hS F f x) d ↔
      HasChartLocalRingDimension B S hS x d := by
  refine ⟨fun h ↦ ?_, hasChartLocalRingDimension_pointsMap_of_isIso_aux B S hS f x d⟩
  have hx : pointsMap B S hS G (inv f) (pointsMap B S hS F f x) = x := by
    rw [← Function.comp_apply (f := pointsMap B S hS G (inv f)), ← pointsMap_comp,
      IsIso.hom_inv_id, pointsMap_id, id_eq]
  have hG := hasChartLocalRingDimension_pointsMap_of_isIso_aux B S hS (inv f)
    (pointsMap B S hS F f x) d h
  rwa [hx] at hG

/-- The dimension of the local ring at a point is unchanged by an isomorphism of presheaves:
the charts above a point and above its image are the same charts. -/
theorem localRingDimension_pointsMap_of_isIso {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [IsIso f] (x : points B S hS F) :
    localRingDimension B S hS (pointsMap B S hS F f x) = localRingDimension B S hS x := by
  have hset : {d : ℕ∞ | HasChartLocalRingDimension B S hS (pointsMap B S hS F f x) d} =
      {d : ℕ∞ | HasChartLocalRingDimension B S hS x d} :=
    Set.ext fun d ↦ hasChartLocalRingDimension_pointsMap_of_isIso B S hS f x d
  rw [localRingDimension, localRingDimension, hset]

/-- `AlgebraicGeometry.Space.localRingDimension_pointsMap_of_isIso` for an isomorphism of
presheaves on the big fppf site, which is the form an isomorphism of algebraic spaces takes. -/
theorem localRingDimension_pointsMap_iso_hom {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ≅ G) (x : points B S hS F) :
    localRingDimension B S hS (pointsMap B S hS F α.hom x) = localRingDimension B S hS x :=
  localRingDimension_pointsMap_of_isIso B S hS α.hom x

end Space

end AlgebraicGeometry

end
