module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.ReciprocityTotalFraction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Assembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.HeightOnePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Assembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Hub
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength

/-!
# The key formula, Stacks 0EQV, from the reading of the restricted generators

We assemble the proof of the key formula for algebraic spaces. Fix an integral closed subspace
`Y` of δ-dimension `k` with generic point `ζ`, and an affine étale chart `(V, u)` of `X` at `ζ` on
which `ℒ` and `𝒩` are free, with chart ratios `a = s / e_ℒ`, `b = t / e_𝒩` units of `Q(A)`,
`A = 𝒪_{V, u}` two-dimensional (`AlgebraicGeometry.Space.exists_keyFormulaLocalChart`). For each
member `Z_i` of the family, the difference of the coefficients at `Y` of the `i`-th terms of the
two sides is `-∑_{𝔮} ord_{A/𝔮}(∂_{A_𝔮}(a, b))`, the sum over the height-one primes `𝔮` of `A`
over the generic point of `Z_i`
(`AlgebraicGeometry.Space.keyFormulaCoeffDiff_eq_neg_finsum_of_chart`): this is
`AlgebraicGeometry.Space.keyFormulaCoeffDiff_pushforward_eq_neg_finsum` when `Y` is the image of a
prime divisor of `Z_i`, and both sides vanish otherwise. A height-one prime lies over the generic
point of at most one `Z_i` (the family is injective and a prime divisor is determined by its
generic point), the summand vanishes at a height-one prime over the generic point of a prime
divisor outside the family (there `s` and `t` generate), and the sum over all height-one primes is
zero by the Key Lemma, Stacks 0EAX. Regrouping gives the vanishing of the sum of the coefficient
differences, hence the key formula
(`AlgebraicGeometry.Space.keyFormulaDivisorSum_eq_keyFormulaTameSum_of_unitRestrictionReading`).

The reading of the restricted generators (G2,
`AlgebraicGeometry.Space.PrimeDivisor.UnitRestrictionReading`) is kept as a hypothesis, for `ℒ`
and for `𝒩`, at every member and every affine chart with a free generator.

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

section Chart

variable (V : SmallEtale D.site D.base D.base_mem X) (hV : IsAffine (chartScheme V))
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
    (u : chartScheme V) [IsNoetherianRing ((chartScheme V).presheaf.stalk u)]
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)

/-- The image in `|X|` of the generic point of the image of a prime divisor `Y'` of `Z_i` is the
image of the generic point of `Y'`, as a prime divisor of `Z_i`. -/
theorem PrimeDivisor.pointsMap_genericPoint_toPrimeDivisor_eq (Z : PrimeDivisor D.site D.base
      D.base_mem X)
    (Y' : IntegralClosedSubspace D.site D.base D.base_mem
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor)
    (hP : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX (Z.toIntegralClosedSubspace D.site D.base
        D.base_mem)).1 Y') = 1) :
    pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
        ((Y'.toPrimeDivisor D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX _).1 hP).genericPoint D.site D.base D.base_mem _) =
      pointsMap D.site D.base D.base_mem
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX)
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2
          Y').subspace.toFunctor
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX)
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2 Y').subspace.ι
        ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX)
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2
          Y').genericPoint D.site D.base D.base_mem) :=
  IntegralClosedSubspace.pointsMap_eq_genericPoint_pushforward D.site D.base D.base_mem hX.1 _ _ _
    Y' _ ((Y'.toPrimeDivisor D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX _).1 hP).isGenericPoint_genericPoint D.site D.base
      D.base_mem _)

/-- **The `i`-th coefficient difference at `Y`, computed on a chart at the generic point of `Y`
through `Z_i`**: when the point `u` of the chart over the generic point of `Y` lies over `Z_i`,
`Y` is the image of a prime divisor `Y'` of `Z_i`, and the difference is
`-∑_{𝔮} ord_{A/𝔮}(∂_{A_𝔮}(a, b))` over the height-one primes `𝔮` of `A = 𝒪_{V, u}` over the
generic point of `Z_i`. -/
theorem keyFormulaCoeffDiff_eq_neg_finsum_of_mem (i : I)
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X) (hYk : deltaDimension D sX Y = k)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X V u =
      pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem))
    (hmem : chartSchemeToPoints D.site D.base D.base_mem X V u ∈
      (Zf i).support D.site D.base D.base_mem X)
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk u) = 2)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk u))ˣ)
    (ha : (a : FractionRing ((chartScheme V).presheaf.stalk u)) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) u
        (chartRatio D.site D.base D.base_mem X hX.1 L V eL hcL hfL s))
    (hb : (b : FractionRing ((chartScheme V).presheaf.stalk u)) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) u
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
    keyFormulaCoeffDiff D sX hX hint L hL s hs N hN t ht hn Zf v w Y i =
      -∑ᶠ 𝔮 : (Zf i).HeightOnePrimeOver D.site D.base D.base_mem V u,
        heightOneOrd hdim (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1)
          (tameSymbolOfKrullDimOne
            (ringKrullDim_localization_heightOnePrime
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1))
            (FractionRing (Localization.AtPrime
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1).1.asIdeal))
            (Units.map (heightOneFractionMap
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1)).toMonoidHom a)
            (Units.map (heightOneFractionMap
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1)).toMonoidHom b)) := by
  obtain ⟨y, hyu⟩ := (Zf i).exists_baseChangeChartProj_eq D.site D.base D.base_mem hX.1 V u hmem
  have hsub : subspacePointSet D.site D.base D.base_mem X Y.subspace ⊆
      Set.range (pointsMap D.site D.base D.base_mem
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace.ι) :=
    IntegralClosedSubspace.subspacePointSet_subset_of_genericPoint_mem D.site D.base D.base_mem
      hX.1 Y (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)) (hu ▸ hmem)
  obtain ⟨Y', rfl⟩ := IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1
    ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX)
    (isDecentSpace_of_isGood D _ (isGood_integralClosedSubspace D sX hX
      ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem)))
    ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2 Y hsub
  subst hyu
  have hZk : deltaDimension D sX ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) =
      k + 1 :=
    (deltaDimension_toIntegralClosedSubspace D sX hX hint (deltaDimensionFunction D sX hX)
      (deltaDimensionFunction_apply D sX hX) hn (Zf i)).trans (by ring)
  have hP := codimension_eq_one_of_deltaDimension_pushforward D sX hX
    ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem) hZk Y' hYk
  have hy : chartSchemeToPoints D.site D.base D.base_mem (Zf i).subspace.toFunctor
        ((Zf i).baseChangeChart D.site D.base D.base_mem hX.1 V) y =
      (Y'.toPrimeDivisor D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX _).1 hP).genericPoint D.site D.base D.base_mem
          _ := by
    refine (((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).isClosedEmbedding_pointsMap
      D.site D.base D.base_mem hX.1).injective ?_
    refine ((Zf i).chartSchemeToPoints_baseChangeChartProj D.site D.base D.base_mem hX.1 V
      y).symm.trans (hu.trans ?_)
    exact ((Zf i).pointsMap_genericPoint_toPrimeDivisor_eq D sX hX Y' hP).symm
  exact keyFormulaCoeffDiff_pushforward_eq_neg_finsum D sX hX hint L hL s hs N hN t ht hn Zf v w
    V hV eL hcL hfL eN hcN hfN i Y' hP y hdim hy a b ha hb hG2L hG2N

omit [IsNoetherianRing ((chartScheme V).presheaf.stalk u)] in
/-- If the point `u` of the chart does not lie over `Z_i`, no height-one prime of `𝒪_{V, u}` lies
over the generic point of `Z_i`: such a prime cuts out a generization of `u`. -/
theorem PrimeDivisor.isEmpty_heightOnePrimeOver_of_not_mem
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (hmem : chartSchemeToPoints D.site D.base D.base_mem X V u ∉
      Z.support D.site D.base D.base_mem X) :
    IsEmpty (Z.HeightOnePrimeOver D.site D.base D.base_mem V u) := by
  refine ⟨fun 𝔮 => hmem ?_⟩
  have hsp := (specializes_intermediatePointOfHeightOnePrime u 𝔮.1).map
    (continuous_chartSchemeToPoints D.site D.base D.base_mem V)
  rw [𝔮.2] at hsp
  rw [← (Z.isGenericPoint_genericPoint D.site D.base D.base_mem X).def]
  exact specializes_iff_mem_closure.mp hsp

omit [IsNoetherianRing ((chartScheme V).presheaf.stalk u)] in
/-- If the point `u` of the chart over the generic point of `Y` does not lie over `Z_i`, then `Y`
is not the image of an integral closed subspace of `Z_i`. -/
theorem PrimeDivisor.pushforward_ne_of_not_mem (Z : PrimeDivisor D.site D.base D.base_mem X)
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X V u =
      pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem))
    (hmem : chartSchemeToPoints D.site D.base D.base_mem X V u ∉
      Z.support D.site D.base D.base_mem X)
    (Y' : IntegralClosedSubspace D.site D.base D.base_mem
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem).subspace.toFunctor) :
    IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX)
      (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2 Y' ≠ Y := by
  rintro rfl
  refine hmem ?_
  have h1 : chartSchemeToPoints D.site D.base D.base_mem X V u ∈
      subspacePointSet D.site D.base D.base_mem X
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX)
          (Z.toIntegralClosedSubspace D.site D.base D.base_mem).isClosedSubspace.2 Y').subspace :=
    hu ▸ ⟨_, rfl⟩
  rw [IntegralClosedSubspace.subspacePointSet_pushforward] at h1
  obtain ⟨z, -, hz⟩ := h1
  exact ⟨z, hz⟩

/-- **The `i`-th coefficient difference at `Y`, computed on a chart at the generic point of
`Y`**: `-∑_{𝔮} ord_{A/𝔮}(∂_{A_𝔮}(a, b))` over the height-one primes `𝔮` of `A = 𝒪_{V, u}` over
the generic point of `Z_i`. -/
theorem keyFormulaCoeffDiff_eq_neg_finsum_of_chart (i : I)
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X) (hYk : deltaDimension D sX Y = k)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X V u =
      pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem))
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk u) = 2)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk u))ˣ)
    (ha : (a : FractionRing ((chartScheme V).presheaf.stalk u)) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) u
        (chartRatio D.site D.base D.base_mem X hX.1 L V eL hcL hfL s))
    (hb : (b : FractionRing ((chartScheme V).presheaf.stalk u)) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) u
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
    keyFormulaCoeffDiff D sX hX hint L hL s hs N hN t ht hn Zf v w Y i =
      -∑ᶠ 𝔮 : (Zf i).HeightOnePrimeOver D.site D.base D.base_mem V u,
        heightOneOrd hdim (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1)
          (tameSymbolOfKrullDimOne
            (ringKrullDim_localization_heightOnePrime
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1))
            (FractionRing (Localization.AtPrime
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1).1.asIdeal))
            (Units.map (heightOneFractionMap
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1)).toMonoidHom a)
            (Units.map (heightOneFractionMap
              (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮.1)).toMonoidHom b)) := by
  by_cases hmem : chartSchemeToPoints D.site D.base D.base_mem X V u ∈
      (Zf i).support D.site D.base D.base_mem X
  · exact keyFormulaCoeffDiff_eq_neg_finsum_of_mem D sX hX hint L hL s hs N hN t ht hn Zf v w V hV
      eL hcL hfL eN hcN hfN u i Y hYk hu hmem hdim a b ha hb hG2L hG2N
  · have := (Zf i).isEmpty_heightOnePrimeOver_of_not_mem D V u hmem
    rw [keyFormulaCoeffDiff_of_forall_ne D sX hX hint L hL s hs N hN t ht hn Zf v w Y i
      fun Y' => (Zf i).pushforward_ne_of_not_mem D sX hX V u Y hu hmem Y', finsum_of_isEmpty,
      neg_zero]

include hinj hcov in
/-- **The coefficient differences at `Y` sum to zero**, given a chart at the generic point of `Y`
and the reading (G2) of the restricted generators on it for every member. -/
theorem finsum_keyFormulaCoeffDiff_eq_zero_of_chart
    (Y : IntegralClosedSubspace D.site D.base D.base_mem X) (hYk : deltaDimension D sX Y = k)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X V u =
      pointsMap D.site D.base D.base_mem Y.subspace.toFunctor Y.subspace.ι
        (Y.genericPoint D.site D.base D.base_mem))
    (hdim : ringKrullDim ((chartScheme V).presheaf.stalk u) = 2)
    (a b : (FractionRing ((chartScheme V).presheaf.stalk u))ˣ)
    (ha : (a : FractionRing ((chartScheme V).presheaf.stalk u)) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) u
        (chartRatio D.site D.base D.base_mem X hX.1 L V eL hcL hfL s))
    (hb : (b : FractionRing ((chartScheme V).presheaf.stalk u)) =
      chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
            D.site D.base D.base_mem hX.1 hint)
          (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
            (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) u
        (chartRatio D.site D.base D.base_mem X hX.1 N V eN hcN hfN t))
    (hG2L : ∀ i, (Zf i).UnitRestrictionReading D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V hV L hL eL hcL hfL
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
          D.base_mem)))
      ((Zf i).isAffine_chartScheme_baseChangeChart D.site D.base D.base_mem hX.1 V hV) (v i))
    (hG2N : ∀ i, (Zf i).UnitRestrictionReading D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V hV N hN eN hcN hfN
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
        (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
          D.base_mem)))
      ((Zf i).isAffine_chartScheme_baseChangeChart D.site D.base D.base_mem hX.1 V hV) (w i)) :
    ∑ᶠ i, keyFormulaCoeffDiff D sX hX hint L hL s hs N hN t ht hn Zf v w Y i = 0 := by
  refine finsum_neg_finsum_subtype_eq_zero
    (fun i (𝔮 : {𝔮 : Ideal ((chartScheme V).presheaf.stalk u) // 𝔮.IsPrime ∧ 𝔮.height = 1}) =>
      chartSchemeToPoints D.site D.base D.base_mem X V (intermediatePointOfHeightOnePrime u 𝔮) =
        (Zf i).genericPoint D.site D.base D.base_mem X)
    (fun i j _ hi hj => hinj (PrimeDivisor.eq_of_genericPoint_eq D.site D.base D.base_mem hX.1
      (hi.symm.trans hj)))
    (fun 𝔮 => heightOneOrd hdim (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮)
      (tameSymbolOfKrullDimOne
        (ringKrullDim_localization_heightOnePrime
          (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮))
        (FractionRing (Localization.AtPrime
          (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮).1.asIdeal))
        (Units.map (heightOneFractionMap
          (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮)).toMonoidHom a)
        (Units.map (heightOneFractionMap
          (heightOnePrimeOfIdeal D.site D.base D.base_mem V u 𝔮)).toMonoidHom b)))
    ((finite_heightOneOrd_tameSymbol_totalFraction_support hdim a b).preimage
      (heightOnePrimeEquivIdeal.symm.injective.injOn))
    ((finsum_comp_equiv heightOnePrimeEquivIdeal.symm).trans
      (finsum_heightOneOrd_tameSymbol_totalFraction_eq_zero hdim a b)) ?_ _
    (fun i => keyFormulaCoeffDiff_eq_neg_finsum_of_chart D sX hX hint L hL s hs N hN t ht hn Zf v w
      V hV eL hcL hfL eN hcN hfN u i Y hYk hu hdim a b ha hb (hG2L i) (hG2N i))
  intro 𝔮 hno
  obtain ⟨Z, hZ, -⟩ := exists_primeDivisor_of_heightOnePrime D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) V u 𝔮
  have hgen := hcov Z fun i hi => hno i (hZ.symm.trans (congrArg
    (fun W : PrimeDivisor D.site D.base D.base_mem X => W.genericPoint D.site D.base D.base_mem X)
    hi.symm))
  exact heightOnePrime_tameSymbolOrd_eq_zero_of_generates D.site D.base D.base_mem hX.1
    (isDecentSpace_of_isGood D sX hX) hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) Z V hV u 𝔮 hZ.symm L hL eL hcL
    hfL hdim N hN eN hcN hfN s t a b ha hb hgen.1 hgen.2

end Chart

/-- **Stacks 0EQV, the key formula, from the reading of the restricted generators (G2).** In the
situation of Stacks 0EQU, for an injective locally finite family of prime divisors `Z_i` outside
of which `s` and `t` generate `ℒ` and `𝒩`, and units `v_i`, `w_i` of `𝒪^h_{X, ξ_i}`,

`∑ (Z_i → X)_*(ord_{B_i}(f_i) div(t_i|_{Z_i}) - ord_{B_i}(g_i) div(s_i|_{Z_i})) =
  ∑ (Z_i → X)_* div(∂_{B_i}(f_i, g_i))`

in `Z_k(X)`, granted the reading (G2,
`AlgebraicGeometry.Space.PrimeDivisor.UnitRestrictionReading`) of `(v_i s_{ξ_i})|_{Z_i}` and
`(w_i t_{ξ_i})|_{Z_i}` on every affine étale chart of `X` with free generators of `ℒ` and `𝒩`. -/
theorem keyFormulaDivisorSum_eq_keyFormulaTameSum_of_unitRestrictionReading
    (hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem X
        ((Zf i).toIntegralClosedSubspace D.site D.base D.base_mem).subspace)
    (hinj : Function.Injective Zf)
    (hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X, (∀ i, Zf i ≠ W) →
      W.SectionGenerates D sX hX hint L hL s ∧ W.SectionGenerates D sX hX hint N hN t)
    (hG2L : ∀ (i : I) (V : SmallEtale D.site D.base D.base_mem X) (hV : IsAffine (chartScheme V))
      (eL : (W' : SmallEtale D.site D.base D.base_mem X) → (W' ⟶ V) → L.val.obj (op W'))
      (hcL : ∀ (W₁ W₂ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
        (L.val.map g.op).hom (eL W₁ k) = eL W₂ (g ≫ k))
      (hfL : ∀ (W₁ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V),
        Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 W₁ ↦ r • eL W₁ k),
      (Zf i).UnitRestrictionReading D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V hV L hL eL hcL hfL
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
          (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
            D.base_mem)))
        ((Zf i).isAffine_chartScheme_baseChangeChart D.site D.base D.base_mem hX.1 V hV) (v i))
    (hG2N : ∀ (i : I) (V : SmallEtale D.site D.base D.base_mem X) (hV : IsAffine (chartScheme V))
      (eN : (W' : SmallEtale D.site D.base D.base_mem X) → (W' ⟶ V) → N.val.obj (op W'))
      (hcN : ∀ (W₁ W₂ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
        (N.val.map g.op).hom (eN W₁ k) = eN W₂ (g ≫ k))
      (hfN : ∀ (W₁ : SmallEtale D.site D.base D.base_mem X) (k : W₁ ⟶ V),
        Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 W₁ ↦ r • eN W₁ k),
      (Zf i).UnitRestrictionReading D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) V hV N hN eN hcN hfN
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D _
          (isGood_integralClosedSubspace D sX hX ((Zf i).toIntegralClosedSubspace D.site D.base
            D.base_mem)))
        ((Zf i).isAffine_chartScheme_baseChangeChart D.site D.base D.base_mem hX.1 V hV) (w i)) :
    keyFormulaDivisorSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w =
      keyFormulaTameSum D sX hX hint L hL s hs N hN t ht hn Zf hfin v w := by
  refine keyFormulaDivisorSum_eq_keyFormulaTameSum_of_finsum_sub_eq_zero D sX hX hint L hL s hs N
    hN t ht hn Zf hfin v w fun Y hYk => ?_
  have hY2 : deltaDimension D sX Y = k + 1 + 1 - 2 := hYk.trans (by ring)
  obtain ⟨V, hV, u, eL, hcL, hfL, eN, hcN, hfN, hu, hsu, htu, hdim, -, hnoeth⟩ :=
    exists_keyFormulaLocalChart D sX hX hint hn L N hL hN s hs t ht Y hY2
  let φ := chartPointMeromorphicMap D.site D.base D.base_mem ⟨X, hX.1⟩ V hV
    (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨X, hX.1⟩
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
        D.site D.base D.base_mem hX.1 hint)
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian D.site D.base D.base_mem
        (F := X) hX.1 (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)) V hV) u
  exact finsum_keyFormulaCoeffDiff_eq_zero_of_chart D sX hX hint L hL s hs N hN t ht hn Zf v w V
    hV eL hcL hfL eN hcN hfN u hinj hcov Y hYk hu hdim (hsu.map φ).unit (htu.map φ).unit
    (IsUnit.unit_spec _) (IsUnit.unit_spec _) (fun i => hG2L i V hV eL hcL hfL)
    (fun i => hG2N i V hV eN hcN hfN)

end AlgebraicGeometry.Space

end
