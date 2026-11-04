module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.DimensionFunctionBase

/-!
# The setup for cycles on algebraic spaces

Chow homology of algebraic spaces is developed over a fixed base: a quasi-separated, locally
Noetherian, universally catenary algebraic space carrying a dimension function `δ`. An
algebraic space over that base is *good* when its structure morphism is quasi-separated and
locally of finite type, and a good space inherits from `δ` the integer-valued function whose
value at `x` is `δ` at the image of `x` plus the transcendence degree of `x` over its image.

## Main definitions

* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.IsGood`: **Stacks 0EDT**, the
  good-space condition on an algebraic space over the fixed base.

## Main results

The induced function and its pointwise formula are those of Stacks 0EDN,
`AlgebraicGeometry.Space.inducedDimensionValue` and
`AlgebraicGeometry.Space.inducedDimensionValue_eq`; this module records that they realize the
corresponding clause of Stacks 0EDT.

## Implementation notes

The good-space condition is an abbreviation and the structure morphism to the base is kept
explicit, so a consumer can use its algebraic-space, quasi-separatedness and
locally-of-finite-type components, and the morphism itself, without conversion lemmas.

Nothing else needs to be re-proved for the present setup. The construction of Tag 0EDN allows an
arbitrary base function and an arbitrary morphism, so it applies to the dimension function and
the structure morphism of this situation without a specialization. Its finite-degree branch
gives exactly the stated sum, and local finiteness of the structure morphism — part of
goodness — makes that branch apply at every point, by
`AlgebraicGeometry.Space.exists_finite_transcendenceDegreeAt`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0EDT.** An algebraic space over the fixed base is *good* when its structure
morphism is quasi-separated and locally of finite type. -/
@[stacks 0EDT "good_space"]
abbrev BaseSpaceDimensionSituation.IsGood (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (f : X ⟶ D.space) : Prop :=
  IsAlgebraicSpace D.site D.base D.base_mem X ∧
    IsQuasiSeparated D.site D.base D.base_mem f ∧
    IsLocallyOfFiniteType D.site D.base D.base_mem f

end AlgebraicGeometry.Space

add_to_stacks 0EDT "induced_delta" AlgebraicGeometry.Space.inducedDimensionValue
add_to_stacks 0EDT "induced_delta" AlgebraicGeometry.Space.inducedDimensionValue_eq

end
