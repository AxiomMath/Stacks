module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ConstancyOfStackDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness

/-!
# The dimension formula is not a hypothesis of the irreducible-chart constancy

`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionAtPoint_of_irreducible_chart` derives the
constancy of `x ↦ dim_x(𝒳)` of Stacks 0AFN from a smooth surjective *irreducible* scheme chart,
carrying two hypotheses: the dimension formula of Stacks 0DRJ along the chart, with its relative
dimension produced as a natural number, and the local constancy of that relative dimension,
which is Stacks 0DRQ (2) for a stack target.

The first of the two is not a hypothesis at all. Stacks 0DRJ is available in exactly the shape
the constancy consumes, as
`AlgebraicGeometry.Stack.exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`: the relative
dimension of a 1-morphism locally of finite type from an algebraic space is a natural number,
and at that value the formula `dim_x(𝒳) = dim_t(T) - d` holds. This file discharges it, leaving
Stacks 0DRQ (2) as the only non-geometric hypothesis of the irreducible-chart constancy.

## Main results

* `AlgebraicGeometry.Stack.isConstant_dimensionAtPoint_of_irreducible_chart`: the constancy of
  the dimension at a point along an irreducible smooth surjective scheme chart, with the
  dimension formula of Stacks 0DRJ discharged.

## Implementation notes

No `@[stacks 0DRX]` attribute is attached. This is the irreducible-chart statement, which the
docstring of `dimensionAtPoint_eq_dimensionAtPoint_of_irreducible_chart` already records as
*not* Stacks 0DRX: an irreducible chart makes vacuous the comparison of the irreducible
components of the chart that is the content of the source's proof. The remaining hypothesis
`h0DRQ` is the local constancy of the relative dimension of the chart, so the statement would
also be a conditional registration.

The hypothesis `hdim` of the unrestricted `AlgebraicGeometry.Stack.isConstant_dimensionAtPoint`
— the local constancy of `u ↦ dim_u(U)` on the whole chart — is not discharged the same way: the
source proves it from Stacks 0DRT at the irreducible components of the chart. Here it is the
irreducibility of the chart that supplies it, through Stacks 0DRT directly.

## References

* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DRT](https://stacks.math.columbia.edu/tag/0DRT)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- The dimension of Stacks 0AFN of a Jacobson, pseudo-catenary, locally Noetherian algebraic
stack `𝒳` with `|𝒳|` irreducible is the same at every point, given a smooth surjective chart by
an *irreducible* scheme `U` of the site which is catenary of finite dimension and along which
the relative dimension is locally constant.

This is `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionAtPoint_of_irreducible_chart` with
its hypothesis `h0DRJ` discharged by
`AlgebraicGeometry.Stack.exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`, which is the
dimension formula of Stacks 0DRJ together with the finiteness of the relative dimension it
subtracts. The surviving hypothesis `h0DRQ` is Stacks 0DRQ (2) for a stack target. -/
theorem isConstant_dimensionAtPoint_of_irreducible_chart
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒳.val))
    (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
    (hsurj : ∀ x : points B S hS 𝒳.val.val 𝒳.val.property,
      ∃ q : Space.points B S hS (yoneda.obj U),
        pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
          (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj U) q) = x)
    (hUirreducible : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUcatenary : IrreducibleClosedsCodim.IsCatenarySpace
      ((BigFppfOver.toScheme B S hS).obj U))
    (d : ℕ)
    (hUdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) = d)
    (h0DRQ : IsLocallyConstant
      (relativeDimensionAt.{u, w} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) 𝒳 a ha)) :
    ∀ x y : points B S hS 𝒳.val.val 𝒳.val.property,
      dimensionAtPoint B S hS 𝒳 h𝒳 x = dimensionAtPoint B S hS 𝒳 h𝒳 y :=
  dimensionAtPoint_eq_dimensionAtPoint_of_irreducible_chart.{u, w} B S hS 𝒳 h𝒳 h𝒳Jacobson
    h𝒳Catenary h𝒳Irreducible U a hasm ha hsurj hUirreducible hUcatenary d hUdim
    (fun q => exists_dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _
      (isAlgebraicSpace_yoneda B S hS U) a hasm ha q rfl)
    h0DRQ

end AlgebraicGeometry.Stack

end
