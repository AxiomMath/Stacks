module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness

/-!
# The dimension formula of Stacks 0DRJ at a smooth chart by an algebraic space

**Stacks 0DRJ** computes the dimension of Stacks 0AFN of a locally Noetherian algebraic stack
`𝒳` at a point `x` from any smooth 1-morphism `U ⟶ 𝒳` from an algebraic space and any point
`u ∈ |U|` above `x`: `dim_x(𝒳) = dim_u(U) - dim_u(U_x)`, the relative dimension being that of
Stacks 0DRG. This file states it with smoothness as the only hypothesis on the chart.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_relativeDimensionAt_of_isSmooth` is
  **Stacks 0DRJ**.

## Implementation notes

The relative dimension of Stacks 0DRG, `AlgebraicGeometry.Stack.relativeDimensionAt`, is defined
for a 1-morphism locally of finite type. A smooth 1-morphism is one, by **Stacks 06MH** and
Stacks 06FM (`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth`), so the
relative dimension in the statement is taken at that proof rather than at a hypothesis.

Its value lies in `WithBot ℕ∞`, and the source's subtraction presupposes that it is a natural
number; it is one, by `AlgebraicGeometry.Stack.exists_relativeDimensionAt_eq_natCast`. The
statement subtracts that natural number, read off the value as `ENat.toNat (r.unbotD 0)`, from
the dimension of the algebraic space with `AlgebraicGeometry.Stack.dimensionSubNat`; the reading
is lossless because the value is a natural number, which is why no existential is needed. The
equation itself is `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`
(Stacks 0AFM read at the given chart).

## References

* [Stacks Project, Tag 06MH](https://stacks.math.columbia.edu/tag/06MH)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DRJ.** Let `𝒳` be a locally Noetherian algebraic stack over `S`, let
`f : T ⟶ 𝒳` be a smooth 1-morphism from an algebraic space, and let `t ∈ |T|` lie above
`x ∈ |𝒳|`. Then

`dim_x(𝒳) = dim_t(T) - dim_t(T_x)`,

the left-hand side being the dimension of Stacks 0AFN and `dim_t(T_x)` the relative dimension of
Stacks 0DRG of `f` at `t`.

The relative dimension is taken at the local finite type of `f` that smoothness gives
(Stacks 06MH, `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth`). It is
a natural number (`AlgebraicGeometry.Stack.exists_relativeDimensionAt_eq_natCast`), and it enters
the subtraction as that natural number, `ENat.toNat (r.unbotD 0)`. -/
@[stacks 0DRJ "dimension via a smooth algebraic space, from smoothness alone"]
theorem dimensionAtPoint_eq_dimensionSubNat_relativeDimensionAt_of_isSmooth
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (t : Space.points B S hS T)
    (ht : pointsMap B S hS (fibredCategory B S hS T).val
      (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
      (stackPointOfSpacePoint B S hS T t) = x) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x =
      dimensionSubNat (Space.dimensionAtPoint B S hS T hT t)
        (ENat.toNat ((relativeDimensionAt.{u, w} B S hS T hT 𝒳 f
          (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hsm) t).unbotD 0)) := by
  have hf := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS f hsm
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS T hT 𝒳 f hf t
  have hdn : ENat.toNat ((relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t).unbotD 0) = d := by
    rw [hd]
    rfl
  rw [hdn]
  exact dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 x hT f hsm hf t ht d
    hd

end AlgebraicGeometry.Stack

end
