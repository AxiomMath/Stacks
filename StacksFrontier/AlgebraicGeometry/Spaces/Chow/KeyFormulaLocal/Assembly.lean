module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCodimensionZeroHypotheses

/-!
# The local chart of the third step of the key formula

In Situation 0EDT let `X/B` be good, `X` integral with `dim_δ(X) = n`, let `ℒ` and `𝒩` be
invertible `𝒪_X`-modules with regular meromorphic sections `s` and `t`, and let `Y ⊂ X` be an
integral closed subspace with `dim_δ(Y) = n - 2` and generic point `ζ`. The third step of the
proof of Stacks 0EQV chooses an étale neighbourhood `(U, u) → (X, ζ)` over which `ℒ` and `𝒩` are
trivial, writes `s = f · e_ℒ` and `t = g · e_𝒩` with `f, g` units of the total ring of fractions
of `Γ(U, 𝒪_U)`, and applies the reciprocity law of Stacks 0EAW to the reduced Noetherian local
ring `A = 𝒪_{U, u}` of dimension two. This file assembles that chart.

## Main results

* `AlgebraicGeometry.Space.exists_keyFormulaLocalChart`: the chart, with all the properties
  listed above.

The height-one primes of `A` and the prime divisors of `X` through `ζ` are related in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.HeightOnePoints`, and the local ring
of
the base change of the chart to a prime divisor through `ζ` is described in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChartStalk`.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)

include hint in
/-- **The local chart of the third step of Stacks 0EQV.** In Situation 0EDT let `X/B` be good,
`X` integral with `dim_δ(X) = n`, `ℒ`, `𝒩` invertible with regular meromorphic sections `s`, `t`,
and `Y ⊂ X` an integral closed subspace with `dim_δ(Y) = n - 2`. There is an étale chart `W` of
`X` with affine scheme and a point `w` of it over the generic point of `Y`, compatible families
`e_ℒ`, `e_𝒩` of free generators of `ℒ` and `𝒩` over the charts over `W`, such that

* the ratios `s / e_ℒ` and `t / e_𝒩` (`AlgebraicGeometry.Space.chartRatio`) are units of the
  total ring of fractions `𝒦_X(W) = Q(𝒪_X(W))` (Stacks 0EN6(2)), and
* the local ring `𝒪_{W, w}` is a reduced Noetherian local ring of Krull dimension two. -/
theorem exists_keyFormulaLocalChart {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hY : deltaDimension D sX Y = n - 2) :
    ∃ (W : SmallEtale D.site D.base D.base_mem X) (_ : IsAffine (chartScheme W))
      (w : chartScheme W)
      (eL : (W' : SmallEtale D.site D.base D.base_mem X) → (W' ⟶ W) → L.val.obj (op W'))
      (hcL : ∀ (W₁ W₂ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (L.val.map g.op).hom (eL W₁ k) = eL W₂ (g ≫ k))
      (hfL : ∀ (W₁ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ W),
        Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 W₁ ↦ r • eL W₁ k)
      (eN : (W' : SmallEtale D.site D.base D.base_mem X) → (W' ⟶ W) → N.val.obj (op W'))
      (hcN : ∀ (W₁ W₂ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (N.val.map g.op).hom (eN W₁ k) = eN W₂ (g ≫ k))
      (hfN : ∀ (W₁ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ W),
        Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 W₁ ↦ r • eN W₁ k),
      chartSchemeToPoints D.site D.base D.base_mem X W w =
          pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
            (Y.genericPoint D.site D.base D.base_mem) ∧
        IsUnit (chartRatio D.site D.base D.base_mem X hX.1 L W eL hcL hfL s) ∧
        IsUnit (chartRatio D.site D.base D.base_mem X hX.1 N W eN hcN hfN t) ∧
        ringKrullDim ((chartScheme W).presheaf.stalk w) = 2 ∧
        _root_.IsReduced ((chartScheme W).presheaf.stalk w) ∧
        IsNoetherianRing ((chartScheme W).presheaf.stalk w) := by
  obtain ⟨W, hW, w, eL, hcL, hfL, eN, hcN, hfN, hw, hsu, htu⟩ :=
    exists_affine_chart_isUnit_chartRatio D.site D.base D.base_mem ⟨X, hX.1⟩
      (forall_localRingDimension_eq_zero_of_isIntegralSpace D.site D.base D.base_mem
        ⟨X, hX.1⟩ hint)
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
        (hF := hX.1) (hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX))
      L N hL hN s hs t ht
      (pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem))
  exact ⟨W, hW, w, eL, hcL, hfL, eN, hcN, hfN, hw, hsu, htu,
    ringKrullDim_stalk_chartScheme_eq_two D sX hX hint hn Y hY W w hw,
    isReduced_stalk_chartScheme_of_isIntegralSpace hX.1 hint W w,
    isNoetherianRing_stalk_chartScheme_of_isGood D sX hX W w⟩

end AlgebraicGeometry.Space

end
