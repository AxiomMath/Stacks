module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IteratedFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaTameCarrier

/-!
# The canonical principal divisor as a homomorphism on units

In Situation 0EDT let `Y/B` be good and integral with `dim_δ(Y) = k + 1`. The principal divisor
`div(f) ∈ Z_k(Y)` of an invertible rational function `f ∈ R(Y)^*`, taken at the canonical
embeddings `R(Y) → Q(𝒪^h_{Y, ξ})` of Stacks 0ENK, is additive: `div(fg) = div(f) + div(g)`
(Stacks 0ENQ), and `div(1) = 0`. Together with Stacks 0EPT — two regular meromorphic sections of
an invertible module differ by an invertible rational function — this writes every integer
multiple of the difference of their Weil divisors as one canonical principal divisor.

## Main results

* `AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt_mul`: `div(fg) = div(f) + div(g)`.
* `AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt_inv`: `div(f⁻¹) = -div(f)`.
* `AlgebraicGeometry.Space.exists_zsmul_sub_canonicalDivisorCycleAt_eq`:
  `a · (div_ℳ(τ) - div_ℳ(τ')) = div(g)` for an invertible rational function `g`.

## References

* [Stacks Project, Tag 0ENQ](https://stacks.math.columbia.edu/tag/0ENQ)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- **Stacks 0ENQ at the canonical choices.** `div(fg) = div(f) + div(g)` for the canonical
principal divisors of invertible rational functions on a good integral algebraic space. -/
theorem canonicalPrincipalDivisorCycleAt_mul
    (f g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalPrincipalDivisorCycleAt D sY hY hintY (f * g) hk =
      canonicalPrincipalDivisorCycleAt D sY hY hintY f hk +
        canonicalPrincipalDivisorCycleAt D sY hY hintY g hk := by
  refine Subtype.ext (funext fun P => ?_)
  show _ = (canonicalPrincipalDivisorCycleAt D sY hY hintY f hk).1 P +
    (canonicalPrincipalDivisorCycleAt D sY hY hintY g hk).1 P
  by_cases hP : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 P) = 1
  · simp only [canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one D sY hY hintY _ hk P hP,
      ordRationalFunction, GenericFractionEmbedding.ord_mul_apply]
  · simp only [canonicalPrincipalDivisorCycleAt, principalDivisorCycleCoefficients, dif_neg hP,
      add_zero]

/-- `div(f⁻¹) = -div(f)` for the canonical principal divisor. -/
theorem canonicalPrincipalDivisorCycleAt_inv
    (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalPrincipalDivisorCycleAt D sY hY hintY f⁻¹ hk =
      -canonicalPrincipalDivisorCycleAt D sY hY hintY f hk := by
  have h := canonicalPrincipalDivisorCycleAt_mul D sY hY hintY f⁻¹ f hk
  rw [inv_mul_cancel, canonicalPrincipalDivisorCycleAt_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **Stacks 0EPT at the canonical choices, as one principal divisor.** On a good integral
algebraic space of δ-dimension `k + 1`, for regular meromorphic sections `τ`, `τ'` of an
invertible module `ℳ` and an integer `a`, there is an invertible rational function `g` with

`a · (div_ℳ(τ) - div_ℳ(τ')) = div(g)`,

the principal divisor being taken at the canonical embeddings of Stacks 0ENK. -/
theorem exists_zsmul_sub_canonicalDivisorCycleAt_eq
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (τ τ' : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ)
    (hτ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ') {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) (a : ℤ) :
    ∃ g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ,
      a • (canonicalDivisorCycleAt D sY hY hintY M hM τ hτ hk -
          canonicalDivisorCycleAt D sY hY hintY M hM τ' hτ' hk) =
        canonicalPrincipalDivisorCycleAt D sY hY hintY g hk := by
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1
    (isDecentSpace_of_isGood D sY hY) hintY hNY
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨g, hg⟩ := exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord
    D.site D.base D.base_mem hY.1 (isDecentSpace_of_isGood D sY hY) hintY hNY M hM τ τ' hτ hτ'
  refine ⟨g ^ a, Subtype.ext (funext fun W => ?_)⟩
  show a • ((canonicalDivisorCycle D sY hY hintY M hM τ hτ hk).1 W -
      (canonicalDivisorCycle D sY hY hintY M hM τ' hτ' hk).1 W) = _
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 W) = 1
  · rw [show (canonicalDivisorCycle D sY hY hintY M hM τ hτ hk).1 W = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ M τ _ hcod,
      show (canonicalDivisorCycle D sY hY hintY M hM τ' hτ' hk).1 W = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ M τ' _ hcod,
      canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one D sY hY hintY _ hk W hcod]
    unfold divisorCoefficients
    rw [hg, add_sub_cancel_left]
    exact (congrFun (E.ord_zpow g a) (W.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)).symm
  · rw [show (canonicalDivisorCycle D sY hY hintY M hM τ hτ hk).1 W = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ M τ _ hcod,
      show (canonicalDivisorCycle D sY hY hintY M hM τ' hτ' hk).1 W = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ M τ' _ hcod]
    unfold canonicalPrincipalDivisorCycleAt
    simp only [principalDivisorCycleCoefficients, dif_neg hcod, sub_self, smul_zero]

end AlgebraicGeometry.Space

end
