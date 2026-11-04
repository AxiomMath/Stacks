module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MaximalDeltaDimension

/-!
# Cycles on an irreducible good algebraic space

In Situation 0EDT let `X/B` be good and suppose that the space of points `|X|` is irreducible,
with generic point `ξ`, and write `n = δ(ξ)` for the value of the dimension function `δ_{X/B}`
there. Every integral closed subspace `Z` of `X` has its generic point in the closure of `ξ`, and
`δ_{X/B}` strictly decreases along nontrivial specializations (Stacks 02I3 for the induced
dimension function), so `dim_δ(Z) ≤ n`, with equality only when the generic point of `Z` is
`ξ`. Consequently

* `Z_k(X) = 0` for `k > n`, and
* a cycle of δ-dimension `n` is a multiple of the single integral closed subspace whose generic
  point is `ξ` (Stacks 0EDV), that is of `[X]_n` when `X` is integral.

These are the two dimension counts in the proof of Stacks 0ERU: a pushforward to an integral
space of δ-dimension `k` vanishes in dimensions above `k` and is a multiple of `[X]` in
dimension `k`.

## Main results

* `AlgebraicGeometry.Space.deltaDimension_le_of_isGenericPoint`: `dim_δ(Z) ≤ δ(ξ)`.
* `AlgebraicGeometry.Space.eq_of_deltaDimension_eq_of_isGenericPoint`: equality only at the
  generic point.
* `AlgebraicGeometry.Space.cyclesOfDimension_eq_bot_of_lt`: **`Z_k(X) = 0` for `k > δ(ξ)`.**
* `AlgebraicGeometry.Space.eq_of_mem_cyclesOfDimension`: **a cycle of δ-dimension
  `δ(ξ)` is a multiple of the integral closed subspace with generic point `ξ`.**

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
  {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
  (sX : X ⟶ D.space) (hX : D.IsGood sX) {ξ : points D.site D.base D.base_mem X}
  (hξ : IsGenericPoint ξ (Set.univ : Set (points D.site D.base D.base_mem X)))

include hX hξ

/-- On a good algebraic space whose space of points has generic point `ξ`, the induced dimension
function is strictly smaller than its value at `ξ` at every other point. -/
theorem deltaValue_lt_of_isGenericPoint (x : points D.site D.base D.base_mem X) (hx : x ≠ ξ) :
    D.deltaValue sX x < D.deltaValue sX ξ :=
  lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2
    (hξ.specializes (Set.mem_univ x)) (Ne.symm hx)

/-- **The δ-dimension of an integral closed subspace is at most the value of the dimension
function at the generic point of `|X|`.** -/
theorem deltaDimension_le_of_isGenericPoint
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimension D sX Z ≤ D.deltaValue sX ξ := by
  by_cases h : pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem) = ξ
  · exact (congrArg (D.deltaValue sX) h).le
  · exact (deltaValue_lt_of_isGenericPoint D sX hX hξ _ h).le

/-- **An integral closed subspace of maximal δ-dimension has generic point `ξ`.** -/
theorem eq_of_deltaDimension_eq_of_isGenericPoint
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (h : deltaDimension D sX Z = D.deltaValue sX ξ) :
    pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem) = ξ := by
  by_contra hne
  exact (deltaValue_lt_of_isGenericPoint D sX hX hξ _ hne).ne h

/-- **`Z_k(X) = 0` for `k` above the value of the dimension function at the generic point of
`|X|`.** -/
theorem cyclesOfDimension_eq_bot_of_lt {k : ℤ} (hk : D.deltaValue sX ξ < k) :
    cyclesOfDimension D sX k = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun α hα => funext fun Z => ?_
  by_contra hZ
  have hdim := hα.2 Z hZ
  have hle := deltaDimension_le_of_isGenericPoint D sX hX hξ Z
  omega

/-- **A cycle of δ-dimension `δ(ξ)` is a multiple of the integral closed subspace `Z₀` whose
generic point is `ξ`**: its coefficient vanishes at every other integral closed subspace. -/
theorem eq_of_mem_cyclesOfDimension
    (Z₀ : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ₀ : IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem X Z₀.subspace))
    {α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ}
    (hα : α ∈ cyclesOfDimension D sX (D.deltaValue sX ξ))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hαZ : α Z ≠ 0) : Z = Z₀ := by
  have hgen := eq_of_deltaDimension_eq_of_isGenericPoint D sX hX hξ Z (hα.2 Z hαZ)
  have hξZ : IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem X Z.subspace) :=
    hgen ▸ isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 Z
  exact (existsUnique_integralClosedSubspace_isGenericPoint_of_isGood D sX hX ξ).unique hξZ hZ₀

end AlgebraicGeometry.Space

end
