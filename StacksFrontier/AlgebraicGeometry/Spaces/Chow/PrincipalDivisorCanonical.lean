module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrincipalWeilDivisorOfUnit

/-!
# The principal divisor of a rational function as a cycle, with every ingredient constructed

In Situation 0EDT let `X/B` be good, assume `X` integral with `dim_δ(X) = n`, and let
`f ∈ R(X)^*`. This file defines the principal divisor

`div(f) = div_X(f) = ∑_Z ord_Z(f) [Z]`

as an `(n - 1)`-cycle on `X`, where `ord_Z(f)` is the order of vanishing along the prime divisor
`Z` of the image of `f` under the canonical embedding `R(X) → Q(𝒪^h_{X,ξ})`.

## Main definitions

* `AlgebraicGeometry.Space.canonicalGenericFractionEmbedding`: the canonical embeddings
  `R(X) → Q(𝒪^h_{X,ξ})` at the prime divisors of `X`.
* `AlgebraicGeometry.Space.rationalFunctionPrincipalDivisorCycle`: the principal divisor
  `div(f) ∈ Z_{n-1}(X)` of `f ∈ R(X)^*`.

## Main results

* `AlgebraicGeometry.Space.rationalFunctionPrincipalDivisorCycle_coe`: the coefficient family of
  `div(f)` is `Z ↦ ord_Z(f)` on prime divisors and zero elsewhere.
* `AlgebraicGeometry.Space.rationalFunctionPrincipalDivisorCycle_toIntegralClosedSubspace`: the
  coefficient of `div(f)` at a prime divisor `Z` is `ord_Z(f)`.

## References

* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
variable (sX : X ⟶ D.space) (hX : D.IsGood sX)
variable (hint : IsIntegralSpace D.site D.base D.base_mem X)

/-- The canonical embeddings `R(X) → Q(𝒪^h_{X,ξ})` at the prime divisors of a good integral
algebraic space `X/B`, together with the nontriviality, Noetherianity and dimension bound of the
henselian local rings `𝒪^h_{X,ξ}`. -/
abbrev canonicalGenericFractionEmbedding :
    GenericFractionEmbedding D.site D.base D.base_mem hX.1 hint.isDecentSpace :=
  genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)

/-- The *principal divisor associated to `f ∈ R(X)^*`*, `div(f) = div_X(f) = ∑_Z ord_Z(f) [Z]`, as
an element of `Z_{n-1}(X)`, for `X/B` good and integral with `dim_δ(X) = n`. -/
@[stacks 0EQ1 "div(f) = ∑ ord_Z(f) [Z] in Z_{n-1}(X) for X/B good and integral with \
dim_δ(X) = n and f ∈ R(X)^*; ord_Z(f) is read through the canonical embedding of Stacks 0ENK, \
local finiteness is Stacks 0ENN proved, the δ-dimension n - 1 of a prime divisor is Stacks 0EPZ \
with the dimension function of Stacks 0EDN proved; nothing carried"]
def rationalFunctionPrincipalDivisorCycle {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) :
    CycleGroup D sX (n - 1) :=
  letI := (canonicalGenericFractionEmbedding D sX hX hint).nontrivial
  letI := (canonicalGenericFractionEmbedding D sX hX hint).isNoetherianRing
  letI := (canonicalGenericFractionEmbedding D sX hX hint).krullDimLE
  principalDivisorCycle D sX hX hint.isDecentSpace
    (canonicalGenericFractionEmbedding D sX hX hint).emb
    (f : rationalFunctions D.site D.base D.base_mem hX.1)
    (fun W => f.isUnit.map ((canonicalGenericFractionEmbedding D sX hX hint).emb W))
    (genericFractionEmbedding_ord_mem_weilDivisor D.site D.base D.base_mem hX.1 hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) f)
    hint (exists_dimensionFunction_deltaValue_of_isGood D sX hX).choose
    (exists_dimensionFunction_deltaValue_of_isGood D sX hX).choose_spec hn

/-- The coefficient family of `div(f)`: the order of vanishing `ord_Z(f)` at an integral closed
subspace which is a prime divisor, read through the canonical embedding `R(X) → Q(𝒪^h_{X,ξ})`, and
zero at any other integral closed subspace. -/
theorem rationalFunctionPrincipalDivisorCycle_coe {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) :
    letI := (canonicalGenericFractionEmbedding D sX hX hint).nontrivial
    letI := (canonicalGenericFractionEmbedding D sX hX hint).isNoetherianRing
    letI := (canonicalGenericFractionEmbedding D sX hX hint).krullDimLE
    (rationalFunctionPrincipalDivisorCycle D sX hX hint hn f).1 =
      principalDivisorCycleCoefficients D sX hX hint.isDecentSpace
        (canonicalGenericFractionEmbedding D sX hX hint).emb
        (f : rationalFunctions D.site D.base D.base_mem hX.1)
        (fun W => f.isUnit.map ((canonicalGenericFractionEmbedding D sX hX hint).emb W)) :=
  rfl

/-- The coefficient of `div(f)` at the integral closed subspace underlying a prime divisor `Z` is
`ord_Z(f)`, the order of vanishing along `Z` of the image of `f` under the canonical embedding
`R(X) → Q(𝒪^h_{X,ξ})`. -/
theorem rationalFunctionPrincipalDivisorCycle_toIntegralClosedSubspace {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ)
    (Z : PrimeDivisor D.site D.base D.base_mem X) :
    (rationalFunctionPrincipalDivisorCycle D sX hX hint hn f).1
        (Z.toIntegralClosedSubspace D.site D.base D.base_mem) =
      (canonicalGenericFractionEmbedding D sX hX hint).ord f Z :=
  let := (canonicalGenericFractionEmbedding D sX hX hint).nontrivial
  let := (canonicalGenericFractionEmbedding D sX hX hint).isNoetherianRing
  let := (canonicalGenericFractionEmbedding D sX hX hint).krullDimLE
  principalDivisorCycleCoefficients_toIntegralClosedSubspace D sX hX hint.isDecentSpace
    (canonicalGenericFractionEmbedding D sX hX hint).emb
    (f : rationalFunctions D.site D.base D.base_mem hX.1)
    (fun W => f.isUnit.map ((canonicalGenericFractionEmbedding D sX hX hint).emb W)) Z

end AlgebraicGeometry.Space

end
