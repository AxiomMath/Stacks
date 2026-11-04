module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFormalEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneSchematicLocus

/-!
# Formal objects of the stack of curves are effective

Stacks 0D58: every formal object of the stack `Curves` of families of curves over `Spec(ℤ)` is
effective.

`AlgebraicGeometry.curvesFormalObject_isEffective_of_schemeNeighbourhoods` is the source's
argument, with every level of the tower of the formal object a scheme by Stacks 0ADD in the form
`AlgebraicGeometry.Space.SchemeNeighbourhoodsInCodimensionOne`, and Stacks 0E7R for a tower of
schemes. Stacks 0ADD is proved
(`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one`), so
this file discharges that input.

## Main results

* `AlgebraicGeometry.Space.schemeNeighbourhoodsInCodimensionOne`: the statement of Stacks 0ADD,
  quantified over every big fppf site and every base scheme, holds.
* `AlgebraicGeometry.curvesFormalObject_isEffective`: every formal object of `Curves` is effective.

## References

* [Stacks Project, Tag 0D58](https://stacks.math.columbia.edu/tag/0D58)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
-/

@[expose] public section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The statement of Stacks 0ADD, quantified over every big fppf site and every base scheme,
holds: it is
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one`. -/
theorem Space.schemeNeighbourhoodsInCodimensionOne :
    Space.SchemeNeighbourhoodsInCodimensionOne.{u} :=
  fun B S hS _ _ hF hsep hN x hx =>
    Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one B S hS hF hsep hN x hx

/-- Every formal object of the stack `Curves` of families of curves over `Spec(ℤ)` is effective:
it comes, up to isomorphism of formal objects, from a family of curves over the spectrum of its
Noetherian complete local base. -/
@[stacks 0D58]
theorem curvesFormalObject_isEffective (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (ξ : Deformation.Artin.FormalObject B integerBase hZ (curvesProjectionOver B hZ)) :
    Deformation.Artin.FormalObject.IsEffective B integerBase hZ (curvesProjectionOver B hZ)
      (Functor.IsFiberedInGroupoids.of_comp_over (B.obj hZ) (curvesProjection B hZ)
        (curvesProjectionOver B hZ) (by rfl) (curvesProjection_isFiberedInGroupoids B hZ)) ξ :=
  curvesFormalObject_isEffective_of_schemeNeighbourhoods Space.schemeNeighbourhoodsInCodimensionOne
    B hZ ξ

end AlgebraicGeometry

end
