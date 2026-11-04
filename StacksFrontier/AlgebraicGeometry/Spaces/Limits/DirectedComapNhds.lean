module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology

/-!
# Directedness of the stage neighbourhood filters of an inverse limit

Let `X = limit D` be the limit of a cofiltered inverse system `D` of sheaves on the big fppf
site of `S`, and let `x` be a point of `X`. The filters on `|X|` pulled back from the
neighbourhood filters at the images of `x` in the stages are downward directed.

## Main results

* `AlgebraicGeometry.Space.directedGE_comap_nhds_limitπ`: the pulled back neighbourhood filters
  at a point of the limit are downward directed.

## References

* [Stacks Project, Tag 086V](https://stacks.math.columbia.edu/tag/086V)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The neighbourhood filters at a point of the limit pulled back from the stages along the
limit projections are downward directed. -/
theorem directedGE_comap_nhds_limitπ (x : points B S hS (limit D)) :
    Directed (· ≥ ·) fun i : I ↦ Filter.comap (pointsMap B S hS (limit D) (limit.π D i))
      (nhds (pointsMap B S hS (limit D) (limit.π D i) x)) := by
  have key : ∀ {k i : I} (f : k ⟶ i),
      Filter.comap (pointsMap B S hS (limit D) (limit.π D k))
          (nhds (pointsMap B S hS (limit D) (limit.π D k) x)) ≤
        Filter.comap (pointsMap B S hS (limit D) (limit.π D i))
          (nhds (pointsMap B S hS (limit D) (limit.π D i) x)) := by
    intro k i f
    have hπ : pointsMap B S hS (limit D) (limit.π D i)
        = pointsMap B S hS (D.obj k) (D.map f) ∘
          pointsMap B S hS (limit D) (limit.π D k) := by
      rw [← limit.w D f, pointsMap_comp]
    rw [hπ]
    exact (Filter.comap_mono (Filter.map_le_iff_le_comap.1
      (continuous_pointsMap B S hS (D.map f)).continuousAt)).trans Filter.comap_comap.le
  exact fun i j ↦ ⟨IsCofiltered.min i j, key (IsCofiltered.minToLeft i j),
    key (IsCofiltered.minToRight i j)⟩

end AlgebraicGeometry.Space
