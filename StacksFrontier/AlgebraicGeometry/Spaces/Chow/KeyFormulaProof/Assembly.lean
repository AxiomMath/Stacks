module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Coefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Member

/-!
# The coefficient of the key formula at the image of a prime divisor of a member

In the situation of Stacks 0EQV, let `Y'` be a prime divisor of the member `Z_i` of the family
with image `Y` in `X`. On an affine étale chart `(V, w)` of `X` at the generic point of `Y`, on
which `ℒ` and `𝒩` are free, and for a point `y` of `V ×_X Z_i` over `w` and over the generic point
of `Y'`, the difference of the coefficients at `Y` of the `i`-th terms of the two sides of the key
formula is `-∑_{𝔮} ord_{A/𝔮}(∂_{A_𝔮}(a, b))`, the sum running over the height-one primes of
`A = 𝒪_{V, w}` over the generic point of `Z_i`
(`AlgebraicGeometry.Space.keyFormulaCoeffDiff_pushforward_eq_neg_finsum`).

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology chartMeromorphicFunctionAlgebra

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ N)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 N t)
    {k : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    {I : Type*} (Zf : I → PrimeDivisor D.site D.base D.base_mem X)
    (v w : ∀ i, (↥((Zf i).genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)))ˣ)
    (V : SmallEtale D.site D.base D.base_mem X) (hV : IsAffine (chartScheme V))
    (eL : (W' : SmallEtale D.site D.base D.base_mem X) → (W' ⟶ V) → L.val.obj (op W'))
    (hcL : ∀ (W₁ W₂ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (eL W₁ k) = eL W₂ (g ≫ k))
    (hfL : ∀ (W₁ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V),
      Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 W₁ ↦ r • eL W₁ k)
    (eN : (W' : SmallEtale D.site D.base D.base_mem X) → (W' ⟶ V) → N.val.obj (op W'))
    (hcN : ∀ (W₁ W₂ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
      (N.val.map g.op).hom (eN W₁ k) = eN W₂ (g ≫ k))
    (hfN : ∀ (W₁ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V),
      Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 W₁ ↦ r • eN W₁ k)

/-- **The `i`-th coefficient difference at the image of a prime divisor `Y'` of `Z_i`, computed on
a chart.** -/
theorem keyFormulaCoeffDiff_pushforward_eq_neg_finsum (i : I)
    (Y' : IntegralClosedSubspace D.site D.base D.base_mem
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor)
    (hP : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
        D.base_mem)).1 Y') = 1)
    (y : chartScheme ((Zf i).baseChangeChart D.site D.base D.base_mem hX.1 V))
    [IsNoetherianRing ((chartScheme V).presheaf.stalk
      ((Zf i).baseChangeChartProj D.site D.base D.base_mem hX.1 V y))]
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk
      ((Zf i).baseChangeChartProj D.site D.base D.base_mem hX.1 V y)) = 2)
    (hy : chartSchemeToPoints D.site D.base D.base_mem (Zf i).subspace.toFunctor
        ((Zf i).baseChangeChart D.site D.base D.base_mem hX.1 V) y =
      (Y'.toPrimeDivisor D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX _).1 hP).genericPoint D.site D.base D.base_mem _)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk
      ((Zf i).baseChangeChartProj D.site D.base D.base_mem hX.1 V y)))ˣ)
    (ha : (a : FractionRing ((chartScheme V).presheaf.stalk
        ((Zf i).baseChangeChartProj D.site D.base D.base_mem hX.1 V y))) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) _
        (chartRatio D.site D.base D.base_mem X hX.1 L V eL hcL hfL s))
    (hb : (b : FractionRing ((chartScheme V).presheaf.stalk
        ((Zf i).baseChangeChartProj D.site D.base D.base_mem hX.1 V y))) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) _
        (chartRatio D.site D.base D.base_mem X hX.1 N V eN hcN hfN t))
    (hG2L : (Zf i).UnitRestrictionReading D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V hV L hL eL hcL hfL
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
          D.base_mem)))
      ((Zf i).isAffine_chartScheme_baseChangeChart D.site D.base D.base_mem hX.1 V hV) (v i))
    (hG2N : (Zf i).UnitRestrictionReading D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V hV N hN eN hcN hfN
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
          D.base_mem)))
      ((Zf i).isAffine_chartScheme_baseChangeChart D.site D.base D.base_mem hX.1 V hV) (w i)) :
    keyFormulaCoeffDiff D sX hX hint L hL s hs N hN t ht hn Zf v w
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX)
          ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2 Y') i =
      -∑ᶠ 𝔮 : (Zf i).HeightOnePrimeOver D.site D.base D.base_mem V
          ((Zf i).baseChangeChartProj D.site D.base D.base_mem hX.1 V y),
        heightOneOrd hdim (heightOnePrimeOfIdeal D.site D.base D.base_mem V _ 𝔮.1)
          (tameSymbolOfKrullDimOne
            (ringKrullDim_localization_heightOnePrime
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V _ 𝔮.1))
            (FractionRing (Localization.AtPrime
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V _ 𝔮.1).1.asIdeal))
            (Units.map (heightOneFractionMap
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V _ 𝔮.1)).toMonoidHom a)
            (Units.map (heightOneFractionMap
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V _ 𝔮.1)).toMonoidHom b)) := by
  refine (keyFormulaCoeffDiff_pushforward D sX hX hint L hL s hs N hN t ht hn Zf v w i Y').trans ?_
  have e1 := (Zf i).restrictedGeneratorDivisor_apply D sX hX hint N hN hn Y' hP (w i)
  have e2 := (Zf i).restrictedGeneratorDivisor_apply D sX hX hint L hL hn Y' hP (v i)
  have e3 := (Zf i).keyFormulaTameCycle_apply D sX hX hint L hL s hs N hN t ht hn Y' hP (v i) (w i)
  have key := (Zf i).keyFormula_member_eq_neg_finsum_of_unitRestrictionReading D.site D.base
    D.base_mem hX.1 V (isDecentSpace_of_isGood D sX hX) hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)))
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
      (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
        D.base_mem))) hV L hL eL hcL hfL N hN eN hcN hfN _ y hdim hy s t a b ha hb
    ((Zf i).sectionRatio D sX hX hint L hL s hs (v i))
    ((Zf i).sectionRatio D sX hX hint N hN t ht (w i)) (v i) (w i)
    ((Zf i).sectionRatio_mul D sX hX hint L hL s hs (v i))
    ((Zf i).sectionRatio_mul D sX hX hint N hN t ht (w i)) hG2L hG2N
  exact (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg (_ * ·) e1) (congrArg (_ * ·) e2))
    e3).trans key

end AlgebraicGeometry.Space

end
