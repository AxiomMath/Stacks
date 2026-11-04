module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodFieldPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints

/-!
# Geometric points over the point of an elementary étale neighborhood

An elementary étale neighborhood `(U, u)` of a point `x` of an algebraic space `F` is in
particular an étale chart of `F`, and a geometric point `x̄` lying over `x` lifts to it along
the residue-field point of `u`. The lift makes `U` a small étale neighborhood of `x̄`.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.chart` is the étale chart underlying an
  elementary étale neighborhood.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.liftGeometricPoint` is the lift of a
  geometric point lying over the point of the space, and
  `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.smallEtaleNeighborhood` is the small
  étale neighborhood of that geometric point it produces.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.toSpace_liftGeometricPoint`: the lift
  composes with the structure morphism to the section defining the geometric point.

## Implementation notes

The lift exists because the residue-field point of `u` is a monomorphic representative of `x`
— this is exactly the condition an elementary étale neighborhood imposes beyond étaleness — so
any other representative of `x`, the geometric point in particular, factors through it uniquely
by Stacks 0H2X. Only algebraicity of `F` is used: decency enters nowhere, since the monomorphic
representative is supplied by the neighborhood rather than produced from the space.

The factorization is recorded through the field spectrum of the residue field of `u` and not
only through the chart; in this form it identifies the image of the geometric point in the chart
scheme with `u`.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace ElementaryEtaleNeighborhood

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  {x : points B S hS F} (U : ElementaryEtaleNeighborhood B S hS F hF x)

/-- The étale chart of `F` underlying an elementary étale neighborhood. -/
def chart : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk U.toSpace, presheaf_etale_of_isEtale B S hS U.etale_toSpace⟩

/-- The scheme of the chart of `U` is the scheme of `U`. -/
@[simp]
theorem chart_obj_left : U.chart.obj.left = U.scheme := rfl

/-- The structure morphism of the chart of `U` is the structure morphism of `U`. -/
@[simp]
theorem chart_obj_hom : U.chart.obj.hom = U.toSpace := rfl

/-- The canonical morphism from the residue-field point of the distinguished point. -/
abbrev fromResidueField :
    residueFieldObject B S hS U.scheme U.point U.residueField_contained ⟶ U.scheme :=
  residueFieldMap B S hS U.scheme U.point U.residueField_contained

/-- The morphism from the residue-field point of the distinguished point to `F` is a
monomorphism. -/
instance : Mono (yonedaEquiv.symm (neighborhoodFieldPoint B S hS F hF x U).value) := by
  rw [neighborhoodFieldPoint_morphism]; exact U.mono_residueField

variable (xbar : GeometricPoint B S hS F) (hxbar : xbar.LiesOver x)

/-- The factorization of a geometric point lying over `x` through the residue-field point of
the distinguished point of an elementary étale neighborhood of `x`. -/
def liftResidueField :
    xbar.val.siteObject B S hS F ⟶
      residueFieldObject B S hS U.scheme U.point U.residueField_contained :=
  (FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS F hF
    (neighborhoodFieldPoint B S hS F hF x U) xbar.val
    ((neighborhoodFieldPoint_class B S hS F hF x U).trans hxbar.symm)).choose

/-- Pulling back the residue-field point of `U` along `liftResidueField` gives the section
defining the geometric point `xbar`. -/
theorem map_liftResidueField :
    F.map (U.liftResidueField xbar hxbar).op
        (neighborhoodFieldPoint B S hS F hF x U).value =
      xbar.val.value := by
  unfold liftResidueField
  generalize_proofs h1 h2
  exact h2.choose_spec.1

/-- The lift of a geometric point lying over `x` to the chart scheme of an elementary étale
neighborhood of `x`. -/
def liftGeometricPoint : xbar.val.siteObject B S hS F ⟶ U.scheme :=
  U.liftResidueField xbar hxbar ≫ U.fromResidueField

/-- The lift of a geometric point is a lift: composing it with the structure morphism of the
neighborhood returns the section defining the geometric point. -/
theorem toSpace_liftGeometricPoint :
    U.toSpace.app (Opposite.op (xbar.val.siteObject B S hS F))
        (U.liftGeometricPoint xbar hxbar) =
      xbar.val.value := by
  calc U.toSpace.app (Opposite.op (xbar.val.siteObject B S hS F))
        (U.liftGeometricPoint xbar hxbar)
      = yonedaEquiv (yoneda.map (U.liftGeometricPoint xbar hxbar) ≫ U.toSpace) := by
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    _ = yonedaEquiv (yoneda.map (U.liftResidueField xbar hxbar) ≫
          yoneda.map U.fromResidueField ≫ U.toSpace) := by
        rw [liftGeometricPoint, yoneda.map_comp, Category.assoc]
    _ = F.map (U.liftResidueField xbar hxbar).op
          (neighborhoodFieldPoint B S hS F hF x U).value :=
        (yonedaEquiv_naturality _ _).symm
    _ = xbar.val.value := U.map_liftResidueField xbar hxbar

/-- An elementary étale neighborhood of `x` is a small étale neighborhood of every geometric
point lying over `x`, the chosen lift being the factorization through the residue-field point
of the distinguished point. -/
def smallEtaleNeighborhood : SmallEtaleNeighborhood xbar where
  chart := U.chart
  point := U.liftGeometricPoint xbar hxbar
  point_comp := U.toSpace_liftGeometricPoint xbar hxbar

/-- The chart of the small étale neighborhood of `xbar` is the chart of `U`. -/
@[simp]
theorem smallEtaleNeighborhood_chart :
    (U.smallEtaleNeighborhood xbar hxbar).chart = U.chart :=
  rfl

/-- The chosen lift of the small étale neighborhood of `xbar` is `liftGeometricPoint`. -/
@[simp]
theorem smallEtaleNeighborhood_point :
    (U.smallEtaleNeighborhood xbar hxbar).point = U.liftGeometricPoint xbar hxbar :=
  rfl

end ElementaryEtaleNeighborhood

end AlgebraicGeometry.Space

end
