module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGood

/-!
# Differences of Weil divisors are principal divisors at the canonical embeddings

In the situation of Stacks 0EDT let `W/B` be good and integral.  Stacks 0EPT says that two
regular meromorphic sections of one invertible `𝒪_W`-module have Weil divisors differing by the
principal divisor of an invertible rational function; the repository states that in the form
`AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub`, whose
conclusion is `AlgebraicGeometry.Space.IsPrincipalDivisorCycle` — the predicate in which the
embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK are quantified existentially with no
compatibility condition.

That conclusion is too coarse for the vanishing statements the factoring tags need.
`AlgebraicGeometry.Space.canonicalFirstChernCap_eq_zero_of_isPrincipalDivisorCycle` asks for
`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`, with the embeddings pinned to the
canonical ones of `AlgebraicGeometry.Space.genericFractionEmbedding`, and there is no bridge from
the existentially quantified predicate to that one: the rescaling
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_emb_mul` that
the reduction would need has a hypothesis — that the embedding is the evaluation of a global
meromorphic function at the generic point of every prime divisor — which is discharged only at
the canonical embedding.

The lemmas of this file are therefore the statements above with the conclusion at the canonical
embeddings.  Each is exactly the corresponding existentially quantified lemma with the witness
`AlgebraicGeometry.Space.genericFractionEmbedding` — which is the witness its proof already
supplies — kept rather than forgotten, so nothing new is assumed and the implication
`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood.isPrincipalDivisorCycle` recovers the
coarse forms.

## Main results

* `isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt`: the principal divisor of
  Stacks 0EQ1 at the canonical choices satisfies the canonical reading of part (1) of Stacks 0EQ6.
* `isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub`: **Stacks 0EPT**, with the
  conclusion at the canonical embeddings.
* `isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_picardTensorModule_sub`:
  **Stacks 0EPV**, with the conclusion at the canonical embeddings.
* `isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_picardTensorModule_sub` and
  `isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_of_iso`: the same two statements
  for the component rule of Stacks 0EQJ on an integral closed subspace.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Principal divisors and differences of Weil divisors on a good integral space -/

section Divisor

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)

/-- **The principal divisor of Stacks 0EQ1 at the canonical choices is a principal divisor in
the canonical reading of part (1) of Stacks 0EQ6.**  The cycle
`AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt` of an invertible rational function
`f ∈ R(Y)^*` is by construction the coefficient family of `div(f)` read at the canonical
embeddings `R(Y) → Q(𝒪^h_{Y,ξ})` of Stacks 0ENK, which is what
`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood` asks for; so `f` itself is the witness.

This is the canonical counterpart of
`AlgebraicGeometry.Space.isPrincipalDivisorCycle_canonicalPrincipalDivisorCycleAt`, which
forgets the embedding. -/
theorem isPrincipalDivisorCycleOfGood_canonicalPrincipalDivisorCycleAt
    (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k
      (canonicalPrincipalDivisorCycleAt D sY hY hint f hk) :=
  ⟨(f : rationalFunctions D.site D.base D.base_mem hY.1), f.isUnit, rfl⟩

/-- **Stacks 0EPT at the canonical embeddings of Stacks 0ENK.**  Two regular meromorphic
sections of an invertible module on a good integral algebraic space have Weil divisors differing
by a principal divisor, and so does any integer multiple of the difference:
`a · (div_ℳ(τ) - div_ℳ(τ')) = div(g^a)` for the rational function `g = τ / τ'`, the principal
divisor being read at the canonical embeddings.

This is `AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub` with
the embedding kept: the witness that proof supplies for the existential is already the canonical
family `AlgebraicGeometry.Space.genericFractionEmbedding`, so the conclusion at the finer
predicate costs nothing. -/
theorem isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub
    (M : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (τ τ' : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ)
    (hτ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M τ') {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k
      (a • (canonicalDivisorCycleAt D sY hY hint M hM τ hτ hk -
        canonicalDivisorCycleAt D sY hY hint M hM τ' hτ' hk)) := by
  have hNY := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1
    (isDecentSpace_of_isGood D sY hY) hint hNY
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨g, hg⟩ := exists_units_orderOfVanishingSection_canonicalLocalRatio_eq_add_ord
    D.site D.base D.base_mem hY.1 (isDecentSpace_of_isGood D sY hY) hint hNY M hM τ τ' hτ hτ'
  refine ⟨((g ^ a : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) :
    rationalFunctions D.site D.base D.base_mem hY.1), (g ^ a).isUnit, ?_⟩
  funext W
  show a • ((canonicalDivisorCycle D sY hY hint M hM τ hτ hk).1 W -
      (canonicalDivisorCycle D sY hY hint M hM τ' hτ' hk).1 W) = _
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 W) = 1
  · rw [show (canonicalDivisorCycle D sY hY hint M hM τ hτ hk).1 W = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ M τ _ hcod,
      show (canonicalDivisorCycle D sY hY hint M hM τ' hτ' hk).1 W = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ M τ' _ hcod]
    unfold divisorCoefficients
    rw [hg, add_sub_cancel_left]
    simp only [principalDivisorCycleCoefficients, dif_pos hcod]
    have hz := congrFun (E.ord_zpow g a) (W.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)
    exact hz.symm
  · rw [show (canonicalDivisorCycle D sY hY hint M hM τ hτ hk).1 W = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ M τ _ hcod,
      show (canonicalDivisorCycle D sY hY hint M hM τ' hτ' hk).1 W = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ M τ' _ hcod]
    simp only [principalDivisorCycleCoefficients, dif_neg hcod, sub_self, smul_zero]

/-- **Stacks 0EPV at the canonical embeddings of Stacks 0ENK.**  For invertible `ℒ`, `𝒩` with
regular meromorphic sections `s`, `t` and any regular meromorphic section `u` of `ℒ ⊗ 𝒩`, every
integer multiple of

  `div_{ℒ⊗𝒩}(u) - (div_ℒ(s) + div_𝒩(t))`

is the principal divisor of an invertible rational function, read at the canonical embeddings.

This is `isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_picardTensorModule_sub` with the
embedding kept.  The product section `st` of Stacks 0EPV has `div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)`
on the nose, and `u` and `st` are two regular meromorphic sections of one invertible module, so the
previous lemma applies. -/
theorem isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_picardTensorModule_sub
    (L N : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ L)
    (hN : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ N)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L s)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 N t)
    (w : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1
      (picardTensorModule D.site D.base D.base_mem hY.1 L N))
    (hw : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1
      (picardTensorModule D.site D.base D.base_mem hY.1 L N) w)
    {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k
      (a • (canonicalDivisorCycleAt D sY hY hint
            (picardTensorModule D.site D.base D.base_mem hY.1 L N)
            (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hY.1 L N hL hN)
            w hw hk -
          (canonicalDivisorCycleAt D sY hY hint L hL s hs hk +
            canonicalDivisorCycleAt D sY hY hint N hN t ht hk))) := by
  have : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY)) := fun W =>
    W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  have : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY)) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  have : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY)) := fun W =>
    W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  obtain ⟨st, hstreg, -, hfinst, hfins, hfint, hdiv⟩ :=
    exists_divisorOfSection_canonicalLocalRatioFamily_picardTensorModule_eq_add
      D.site D.base D.base_mem hY.1 (isDecentSpace_of_isGood D sY hY) L N hL hN hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) s t hs ht
  have hcoeff : ∀ Z : PrimeDivisor D.site D.base D.base_mem Y,
      divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isGood D sY hY)
          (picardTensorModule D.site D.base D.base_mem hY.1 L N) st
          (canonicalLocalRatioFamily D.site D.base D.base_mem hY.1
            (isDecentSpace_of_isGood D sY hY)
            (picardTensorModule D.site D.base D.base_mem hY.1 L N)
            (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hY.1 L N hL hN)
            hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)) Z =
        divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1
            (isDecentSpace_of_isGood D sY hY) L s
            (canonicalLocalRatioFamily D.site D.base D.base_mem hY.1
              (isDecentSpace_of_isGood D sY hY) L hL hint
              (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)) Z +
          divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1
            (isDecentSpace_of_isGood D sY hY) N t
            (canonicalLocalRatioFamily D.site D.base D.base_mem hY.1
              (isDecentSpace_of_isGood D sY hY) N hN hint
              (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)) Z :=
    fun Z => congrFun (congrArg Subtype.val hdiv) Z
  have hsum : canonicalDivisorCycleAt D sY hY hint
        (picardTensorModule D.site D.base D.base_mem hY.1 L N)
        (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hY.1 L N hL hN)
        st hstreg hk =
      canonicalDivisorCycleAt D sY hY hint L hL s hs hk +
        canonicalDivisorCycleAt D sY hY hint N hN t ht hk := by
    refine Subtype.ext (funext fun Z => ?_)
    have hadd : (canonicalDivisorCycleAt D sY hY hint L hL s hs hk +
        canonicalDivisorCycleAt D sY hY hint N hN t ht hk).1 Z =
        (canonicalDivisorCycleAt D sY hY hint L hL s hs hk).1 Z +
          (canonicalDivisorCycleAt D sY hY hint N hN t ht hk).1 Z := rfl
    rw [hadd]
    by_cases hcod : codimension
        (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z) = 1
    · rw [show (canonicalDivisorCycleAt D sY hY hint _ _ st hstreg hk).1 Z = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ _ st _ hcod,
        show (canonicalDivisorCycleAt D sY hY hint L hL s hs hk).1 Z = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ L s _ hcod,
        show (canonicalDivisorCycleAt D sY hY hint N hN t ht hk).1 Z = _ from
        divisorCycleCoefficients_of_codimension_eq_one D sY hY _ N t _ hcod]
      exact hcoeff _
    · rw [show (canonicalDivisorCycleAt D sY hY hint _ _ st hstreg hk).1 Z = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ _ st _ hcod,
        show (canonicalDivisorCycleAt D sY hY hint L hL s hs hk).1 Z = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ L s _ hcod,
        show (canonicalDivisorCycleAt D sY hY hint N hN t ht hk).1 Z = 0 from
        divisorCycleCoefficients_of_codimension_ne_one D sY hY _ N t _ hcod,
        add_zero]
  rw [← hsum]
  exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D sY hY hint _ _ w st hw
    hstreg hk a

end Divisor

/-! ### The component rule of Stacks 0EQJ on an integral closed subspace -/

section Rule

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    (hX : D.IsGood sX)

attribute [local instance] modulesMonoidalCategory

/-- The component rule of Stacks 0EQJ for `ℳ` is the canonical divisor cycle of some regular
meromorphic section of any invertible module on `W` isomorphic to `ℳ|_W`. -/
private theorem exists_canonicalFirstChernRule_eq_canonicalDivisorCycleAt
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (M : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (M' : Modules.{u, u} D.site D.base D.base_mem _ (isGood_integralClosedSubspace D sX hX W).1)
    (hM' : IsInvertibleModule (B := D.site)
      ⟨W.subspace.toFunctor, (isGood_integralClosedSubspace D sX hX W).1⟩ M')
    (e : integralClosedSubspaceRestrict D sX hX M W ≅ M') (k : ℤ)
    (hW : deltaDimension D sX W = k + 1) :
    ∃ (σ' : MeromorphicSection.{u, u} D.site D.base D.base_mem _
        (isGood_integralClosedSubspace D sX hX W).1 M')
      (hσ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _
        (isGood_integralClosedSubspace D sX hX W).1 M' σ'),
      canonicalFirstChernRule D sX hX M hM k W hW =
        canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
          W.isIntegralSpace M' hM' σ' hσ'
          (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW]) := by
  have hσ := isRegularMeromorphicSection_componentMeromorphicSection sX hX
    (subspaceDivisorSetupOfIsGood D sX hX) M hM W
  have hσ' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem
    W.subspace.toFunctor (isGood_integralClosedSubspace D sX hX W).1 e _ hσ
  exact ⟨_, hσ', (canonicalDivisorCycleAt_sectionsMap_iso D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace _ _ _ _ e _ hσ hσ' _).symm⟩

/-- **The component rule of Stacks 0EQJ is additive up to a principal divisor at the canonical
embeddings.**  On an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` every integer
multiple of

  `c₁((ℒ⊗𝒩)|_W) ∩ [W] - (c₁(ℒ|_W) ∩ [W] + c₁(𝒩|_W) ∩ [W])`

is a principal divisor on `W` in the canonical reading of part (1) of Stacks 0EQ6.

This is `isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_picardTensorModule_sub` with the
embedding kept: the chosen section of `(ℒ⊗𝒩)|_W` is carried along `(ℒ⊗𝒩)|_W ≅ ℒ|_W ⊗ 𝒩|_W` to a
regular meromorphic section of the latter with the same Weil divisor, and there
Stacks 0EPV at the canonical embeddings applies. -/
theorem isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_picardTensorModule_sub
    (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1) (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace k
      (a • (canonicalFirstChernRule D sX hX
              (picardTensorModule D.site D.base D.base_mem hX.1 L N)
              (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN)
              k W hW -
            (canonicalFirstChernRule D sX hX L hL k W hW +
              canonicalFirstChernRule D sX hX N hN k W hW))) := by
  obtain ⟨σ', hσ', h⟩ := exists_canonicalFirstChernRule_eq_canonicalDivisorCycleAt hX W
    (picardTensorModule D.site D.base D.base_mem hX.1 L N)
    (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN) _
    (isInvertibleModule_picardTensorModule D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1 _ _
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL W)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W))
    (integralClosedSubspaceRestrictPicardTensorIso hX L N W) k hW
  rw [h]
  exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_picardTensorModule_sub D
    (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace _ _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
    _ (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) L hL W)
    _ (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
    σ' hσ' _ a

/-- **The component rule of Stacks 0EQJ depends on the module only up to isomorphism, up to a
principal divisor at the canonical embeddings.**  For `e : ℳ ≅ ℳ'` and an integral closed
subspace `W ⊆ X` of δ-dimension `k + 1`, every integer multiple of
`c₁(ℳ'|_W) ∩ [W] - c₁(ℳ|_W) ∩ [W]` is a principal divisor on `W` in the canonical reading of
part (1) of Stacks 0EQ6.

This is `AlgebraicGeometry.Space.isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_sub_of_iso`
with the embedding kept. -/
theorem isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_of_iso
    (M M' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (hM' : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M')
    (e : M ≅ M') (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1) (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D (W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace k
      (a • (canonicalFirstChernRule D sX hX M' hM' k W hW -
        canonicalFirstChernRule D sX hX M hM k W hW)) := by
  obtain ⟨σ', hσ', h⟩ := exists_canonicalFirstChernRule_eq_canonicalDivisorCycleAt hX W M hM _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M' hM' W)
    ((modulePullback D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)).mapIso e)
    k hW
  rw [h]
  exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M' hM' W) _ _
    (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) M' hM' W) hσ' _ a

end Rule

end AlgebraicGeometry.Space

end
