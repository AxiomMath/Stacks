module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods

/-!
# The Stein factorization is finite étale near a point

A geometric fibre of a morphism of algebraic spaces over a point at which the number of
geometric connected components is one is connected.

## Main results

* `connectedPullback_of_numberGeometricConnectedComponents_eq_one`: a geometric fibre over a point
  at which the number of geometric connected components is one is connected.

## References

* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- the default instance search for pullbacks of presheaves on the big fppf site times out
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ProperFlatSteinCore :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ProperFlatSteinCore
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A geometric fibre of `f` over a geometric point whose image carries the value `1` of the
number of geometric connected components is connected (and in particular nonempty). -/
theorem connectedPullback_of_numberGeometricConnectedComponents_eq_one
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (p : GeometricPoint B S hS G)
    (h : numberGeometricConnectedComponents B S hS f p.image = 1) :
    ConnectedPullback B S hS f (yonedaEquiv.symm p.val.value) := by
  rw [numberGeometricConnectedComponents_eq B S hS hF hG f p] at h
  set P := points B S hS (Limits.pullback f (yonedaEquiv.symm p.val.value))
  have hcard : Cardinal.mk (ConnectedComponents P) = 1 := Cardinal.toENat_eq_one.mp h
  have := Cardinal.le_one_iff_subsingleton.mp hcard.le
  obtain ⟨c⟩ := Cardinal.mk_ne_zero_iff.mp (hcard ▸ one_ne_zero)
  obtain ⟨x, -⟩ := ConnectedComponents.surjective_coe c
  refine { toPreconnectedSpace := ?_, toNonempty := ⟨x⟩ }
  rw [preconnectedSpace_iff_connectedComponent]
  exact fun _ ↦ Set.eq_univ_of_forall fun _ ↦
    ConnectedComponents.coe_eq_coe'.mp (Subsingleton.elim _ _)

end AlgebraicGeometry.Space.ProperFlatStein

end
