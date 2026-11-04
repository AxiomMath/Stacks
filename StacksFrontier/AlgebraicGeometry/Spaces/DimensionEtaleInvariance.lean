module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Étale invariance of the dimension of an algebraic space

An étale morphism of algebraic spaces changes neither the dimension at a point nor the
dimension of the local ring at a point, and a surjective étale morphism therefore preserves
the dimension of the whole space.

## Main results

* `AlgebraicGeometry.Space.dimensionAtPoint_eq_of_isEtale`: the dimension at a point agrees
  with the dimension at its image under an étale morphism.
* `AlgebraicGeometry.Space.localRingDimension_pointsMap_of_etale`: the same for the dimension
  of the local ring at a point.
* `AlgebraicGeometry.Space.dimension_eq_of_isEtale_of_isSurjective`: a surjective étale
  morphism of algebraic spaces preserves the dimension.

## Implementation notes

An étale scheme chart `a : yoneda.obj U ⟶ X` above a point `x` serves as a chart of `Y` above
the image of `x`, because étaleness of `f : X ⟶ Y` is exactly the statement that `a ≫ f` is
again an étale chart, and the two charts select the same scheme point of `U`. Both dimensions
are computed on that one chart, by the chart independence of Tag 04N5 and of Tag 0BAM
respectively, which gives the equalities without comparing charts of `X` with charts of `Y`.

The global statement follows from the pointwise one because the map on points of a surjective
morphism is surjective, so the two suprema over the point sets agree.

## References

* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0A4H.** An étale morphism of algebraic spaces preserves the dimension at a
point. -/
@[stacks 0A4H "dimension_at_point"]
theorem dimensionAtPoint_eq_of_isEtale (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsEtale B S hS f)
    (x : points B S hS X) :
    dimensionAtPoint B S hS X hX x =
      dimensionAtPoint B S hS Y hY (pointsMap B S hS X f x) := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  have hpf : pointsMap B S hS (yoneda.obj U) (a ≫ f) (p.class B S hS (yoneda.obj U)) =
      pointsMap B S hS X f x := by rw [pointsMap_comp_apply, hp]
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp,
    dimensionAtPoint_eq_of_etale_chart B S hS Y hY _ U (a ≫ f) (hf U a ha) p hpf]

/-- **Stacks 0A4H.** An étale morphism of algebraic spaces preserves the dimension of the
local ring at a point. -/
@[stacks 0A4H "dimension_local_ring"]
theorem localRingDimension_pointsMap_of_etale (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsEtale B S hS f)
    (x : points B S hS X) :
    localRingDimension B S hS (pointsMap B S hS X f x) = localRingDimension B S hS x := by
  obtain ⟨U, a, u, ha, ⟨p, rfl, hp⟩, hdim⟩ :=
    (localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hX x _).mp rfl
  refine (localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hY _ _).mpr
    ⟨U, a ≫ f, _, hf U a ha, ⟨p, rfl, ?_⟩, hdim⟩
  rw [pointsMap_comp_apply, hp]

/-- **Stacks 0A4H.** A surjective étale morphism of algebraic spaces preserves the
dimension. -/
@[stacks 0A4H "dimension_surjective"]
theorem dimension_eq_of_isEtale_of_isSurjective (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsEtale B S hS f)
    (hfs : IsSurjective B S hS f) :
    dimension B S hS X hX = dimension B S hS Y hY :=
  hfs.iSup_congr _ fun x ↦ (dimensionAtPoint_eq_of_isEtale B S hS hX hY f hf x).symm

end AlgebraicGeometry.Space

end
