module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SmoothDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint

/-!
# The dimension formula for a smooth morphism of algebraic spaces, in relative dimension

For a smooth morphism `f : U ⟶ X` of locally Noetherian algebraic spaces over `S` and a point
`u ∈ |U|` above `x ∈ |X|`, Stacks 0DRI reads the dimension formula `dim_u(U) = dim_x(X) +
dim_u(U_x)` with `dim_u(U_x)` the relative dimension of Stacks 0DRG, that is, the dimension of
the fibre `U ×_X Spec k` of the induced 1-morphism of algebraic stacks over a field-valued point
representing `x`.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_add_relativeDimensionAt_of_isSmooth` is
  **Stacks 0DRI**.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_algebraicSpaceStackMap_of_isSmooth`: the
  1-morphism of algebraic stacks induced by a smooth morphism of algebraic spaces is locally of
  finite type, which is what makes the relative dimension of Stacks 0DRG defined on it.

## Implementation notes

The source's proof is the remark that the relative dimension of Stacks 0DRG agrees for a
morphism of algebraic spaces with the relative dimension at a point of Stacks 04NM, and that
the formula in the latter is Stacks 0AFI. Both are available:
`AlgebraicGeometry.Stack.relativeDimensionAt_eq_iff_hasRelativeDimensionAt` is the agreement and
`AlgebraicGeometry.Space.exists_hasRelativeDimensionAt_and_dimensionAtPoint_eq_add_of_isSmooth`
is the formula together with the finiteness of the value it is stated at, the relative dimension
of Stacks 04NM being a predicate carrying its value as an index rather than a function.

Local finite type of the induced 1-morphism is a consequence of smoothness rather than a
hypothesis, by Stacks 06MH and the smooth-diagram criterion of
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_algebraicSpaceStackMap_iff`, so it is supplied in
the statement instead of being assumed.

The universe `u` is that of the base scheme and of its relative big fppf site, while `w` is the
descent universe at which algebraicity of the stack of `X` is tested; the two are independent.

## References

* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 06MH](https://stacks.math.columbia.edu/tag/06MH)
* [Stacks Project, Tag 0AFI](https://stacks.math.columbia.edu/tag/0AFI)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRI](https://stacks.math.columbia.edu/tag/0DRI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism of algebraic stacks induced by a smooth morphism of algebraic spaces over
`S` is locally of finite type.** A smooth morphism of algebraic spaces is locally of finite type
by Stacks 06MH, and the two local finite types correspond by
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_algebraicSpaceStackMap_iff`. -/
theorem isLocallyOfFiniteType_algebraicSpaceStackMap_of_isSmooth
    {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    (g : U ⟶ X) (hg : Space.IsSmooth B S hS g) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hU hX g) :=
  (isLocallyOfFiniteType_algebraicSpaceStackMap_iff.{u, w} B S hS hU hX g).mpr
    (Space.isLocallyOfFiniteType_of_isSmooth B S hS hg)

/-- **Stacks 0DRI.** Let `g : U ⟶ X` be a smooth morphism of locally Noetherian algebraic spaces
over `S` and let `u ∈ |U|` have image `x ∈ |X|`. Then `dim_u(U) = dim_x(X) + dim_u(U_x)`, where
`dim_u(U_x)` is the relative dimension of Stacks 0DRG of the induced 1-morphism of algebraic
stacks at `u`. -/
@[stacks 0DRI]
theorem dimensionAtPoint_eq_add_relativeDimensionAt_of_isSmooth
    {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    (hNU : Space.HasEtaleLocalProperty B S hS U
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNX : Space.HasEtaleLocalProperty B S hS X
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (g : U ⟶ X) (hg : Space.IsSmooth B S hS g) (u : Space.points B S hS U) :
    Space.dimensionAtPoint B S hS U hU u =
      Space.dimensionAtPoint B S hS X hX (Space.pointsMap B S hS U g u) +
        relativeDimensionAt.{u, w} B S hS U hU (algebraicSpaceStack.{u, w} B S hS X hX)
          (algebraicSpaceStackMap.{u, w} B S hS hU hX g)
          (isLocallyOfFiniteType_algebraicSpaceStackMap_of_isSmooth.{u, w} B S hS hU hX g hg)
          u := by
  obtain ⟨d, hd, hdim⟩ :=
    Space.exists_hasRelativeDimensionAt_and_dimensionAtPoint_eq_add_of_isSmooth B S hS hU hX
      hNU hNX g hg u
  rw [hdim, (relativeDimensionAt_eq_iff_hasRelativeDimensionAt.{u, w} B S hS hU hX g
    (isLocallyOfFiniteType_algebraicSpaceStackMap_of_isSmooth.{u, w} B S hS hU hX g hg)
    u d).mpr hd]

end AlgebraicGeometry.Stack

end
