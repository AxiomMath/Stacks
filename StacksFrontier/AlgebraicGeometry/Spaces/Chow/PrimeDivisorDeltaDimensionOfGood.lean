module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionFunction

/-!
# Stacks 0EPZ, part (1), at the hypotheses of the source

In Situation 0EDT let `X/B` be good and let `X` be integral with `dim_δ(X) = n`.  For an
integral closed subspace `Z ⊆ X`, being a prime divisor of `X`, having codimension one in `|X|`
and having `dim_δ(Z) = n - 1` are equivalent.

## Main results

* `AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace'`: **Stacks 0EPZ, part (1)**,
  at the hypotheses of the source.

## Implementation notes

`AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace'` is an alias of
`AlgebraicGeometry.Space.isPrimeDivisor_tfae` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimension`, where the equivalence is
proved at the hypotheses of the source.  The engine there,
`AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace`, takes in addition a bundled
`TopologicalSpace.DimensionFunction` on `|X|` whose underlying function is `δ_{X/B}`.  That
bundle is not an input of Stacks 0EPZ: for a good `X/B` it is produced by Stacks 0EDN,
`AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue`, whose hypotheses are
exactly the standing data of Situation 0EDT together with goodness of `X/B` — decency of `X` is
`AlgebraicGeometry.Space.isDecentSpace_of_isGood` and decency of the base follows from its
quasi-separatedness.

## References

* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- In Situation 0EDT let `X/B` be good and assume `X` integral with
`dim_δ(X) = n`. For an integral closed subspace `Z ⊆ X` the following are equivalent: `Z` is a
prime divisor of `X`; the set of points of `Z` has codimension one in `|X|`; and
`dim_δ(Z) = n - 1`.

This is an alias of `AlgebraicGeometry.Space.isPrimeDivisor_tfae`, which is proved at these
hypotheses in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimension`. The
bundled dimension function on `|X|` with underlying function `δ_{X/B}` that the engine
`AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace` takes is produced from goodness
of `X/B` by Stacks 0EDN,
`AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue`: the base of
Situation 0EDT is a quasi-separated, locally Noetherian, universally catenary algebraic space
with a dimension function, a good `X/B` is decent and locally of finite type over it, and a
quasi-separated algebraic space is decent. -/
@[stacks 0EPZ "part (1)"]
alias isPrimeDivisor_tfae_of_isIntegralSpace' := isPrimeDivisor_tfae

end AlgebraicGeometry.Space

end
