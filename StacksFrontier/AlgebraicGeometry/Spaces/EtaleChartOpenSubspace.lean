module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange

/-!
# Pointed étale charts and open subspaces of the source

Restricting a morphism of presheaves on the big fppf site to an open subspace of its source
does not change which pointed étale charts it admits: a chart for the restriction is a chart
for the morphism itself, at the image of the point, with the same chart map.

This is the one fact behind every "property `P` at a point is unchanged by shrinking the
source to an open neighbourhood" statement, and it is stated here once, for the two
developments that need it — relative dimension at a point and flatness at a point.

## Main results

* `AlgebraicGeometry.Space.presheaf_etale_ι_of_isOpenSubspace`: the inclusion of an open
  subspace is étale as a morphism of presheaves on the site.
* `AlgebraicGeometry.Space.etaleChartAtPointOfOpenSubspace`: a pointed étale chart of the
  restriction to an open subspace is a pointed étale chart of the morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of an open subspace is étale as a morphism of presheaves on the site. -/
theorem presheaf_etale_ι_of_isOpenSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.ι :=
  presheaf_etale_of_isOpenImmersion B S hS hU.2

/-- A pointed étale chart of the restriction of a morphism to an open subspace of its source is
a pointed étale chart of the morphism itself, at the image of the point: the chart map is
unchanged and the chart of the source is composed with the inclusion. -/
noncomputable def etaleChartAtPointOfOpenSubspace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (f : X ⟶ Y) {x' : points B S hS U.toFunctor}
    (c : EtaleChartAtPoint B S hS (U.ι ≫ f) x') :
    EtaleChartAtPoint B S hS f (pointsMap B S hS U.toFunctor U.ι x') :=
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  { U := c.U
    V := c.V
    a := c.a ≫ U.ι
    b := c.b
    h := c.h
    a_etale := MorphismProperty.comp_mem _ c.a U.ι c.a_etale
      (presheaf_etale_ι_of_isOpenSubspace B S hS U hU)
    b_etale := c.b_etale
    comm := by simpa only [Category.assoc] using c.comm
    representative := c.representative
    point := c.point
    maps_to := by
      rw [pointsMap_comp]
      exact congrArg (pointsMap B S hS U.toFunctor U.ι) c.maps_to }

end AlgebraicGeometry.Space

end
