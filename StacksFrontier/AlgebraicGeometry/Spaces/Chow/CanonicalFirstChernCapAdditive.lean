module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorMeromorphicSectionIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor

/-!
# Additivity of the first Chern class cap product at the canonical choices

In the situation of Stacks 0EDT let `X/B` be good and let `ℒ` and `𝒩` be invertible
`𝒪_X`-modules.  Stacks 0EQK is the pair of assertions

  `c₁(ℒ) ∩ α + c₁(𝒩) ∩ α = c₁(ℒ ⊗_{𝒪_X} 𝒩) ∩ α`   and   `c₁(𝒪_X) ∩ α = 0`

in `CH_k(X)`.  Both are proved here for the cap product of Stacks 0EQJ at the canonical choices,
`AlgebraicGeometry.Space.canonicalFirstChernCap`, whose component cycle is the Weil divisor of
Stacks 0EQE at the canonical ratios and whose target is the Chow group `CH_k(X)` of Stacks 0EQ6.
The tensor product is `AlgebraicGeometry.Space.picardTensorModule` and the structure sheaf is the
tensor unit `𝟙_ (AlgebraicGeometry.Space.Modules …)`, which is `𝒪_X` viewed as a module over
itself on the nose (`AlgebraicGeometry.Space.modulesTensorUnit_eq`).

The source writes `α ∈ Z_{k-1}(X)`, which is a slip: the operation of Stacks 0EQJ is
`c₁(ℒ) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)`, so only `α ∈ Z_{k+1}(X)` gives an identity in `CH_k(X)`,
and the identical lemma on the scheme side (Stacks 02SP) states `Z_{k+1}(X)`.  The statements
below use `Z_{k+1}(X)`.

## Main results

* `AlgebraicGeometry.Space.canonicalFirstChernCap_picardTensorModule`: the first assertion of
  Stacks 0EQK.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_tensorUnit_eq_zero`: the second assertion of
  Stacks 0EQK.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_congr_iso`: the cap product of Stacks 0EQJ at
  the canonical choices depends on the invertible module only through its isomorphism class.

## References

* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The Weil divisor of Stacks 0EQE and the module it is taken on -/

section Divisor
variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)

/-- The instances on the generic henselian local rings of the prime divisors of a good integral
space which the Weil divisors of Stacks 0EQE need. -/
private theorem genericHenselianLocalRing_instances
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) :
    (∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY))) ∧
    (∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY))) ∧
    (∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY))) :=
  ⟨fun W => W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY),
    fun W => W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY),
    fun W => W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)⟩

/-- **Two Weil divisors of Stacks 0EQE agree when their coefficients do.**  Two cycles
`div_ℳ(σ)` and `div_ℳ'(σ')` of Stacks 0EQE, part (1), at the canonical ratios on the same space,
possibly for different invertible modules and sections, are equal as soon as the orders of
vanishing of `σ` and `σ'` agree along every prime divisor. -/
theorem canonicalDivisorCycleAt_congr
    (M M' : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (hM' : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M')
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (σ' : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M')
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M σ)
    (hσ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M' σ')
    {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    haveI : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
        Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isGood D sY hY)) := fun W =>
      W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
    haveI : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
        IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isGood D sY hY)) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
    haveI : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
          (isDecentSpace_of_isGood D sY hY)) := fun W =>
      W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1
        (isDecentSpace_of_isGood D sY hY) hint
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
    (∀ Z : PrimeDivisor D.site D.base D.base_mem Y,
        divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1
            (isDecentSpace_of_isGood D sY hY) M σ
            (canonicalLocalRatioFamily D.site D.base D.base_mem hY.1
              (isDecentSpace_of_isGood D sY hY) M hM hint
              (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)) Z =
          divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1
            (isDecentSpace_of_isGood D sY hY) M' σ'
            (canonicalLocalRatioFamily D.site D.base D.base_mem hY.1
              (isDecentSpace_of_isGood D sY hY) M' hM' hint
              (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)) Z) →
      canonicalDivisorCycleAt D sY hY hint M hM σ hσ hk =
        canonicalDivisorCycleAt D sY hY hint M' hM' σ' hσ' hk := by
  intro hord
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances D sY hY hint
  refine Subtype.ext (funext fun Z => ?_)
  change divisorCycleCoefficients D sY hY _ M σ _ Z = divisorCycleCoefficients D sY hY _ M' σ' _ Z
  unfold divisorCycleCoefficients
  split_ifs
  · exact hord _
  · rfl

/-- **The Weil divisor of Stacks 0EQE is carried along an isomorphism of modules.**  For
`e : ℳ ≅ ℳ'` and a regular meromorphic section `σ` of `ℳ`, the Weil divisor of the image of `σ`
under the induced isomorphism `𝒦_Y(ℳ) ≅ 𝒦_Y(ℳ')` is the Weil divisor of `σ`. -/
theorem canonicalDivisorCycleAt_sectionsMap_iso
    (M M' : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (hM' : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M')
    (e : M ≅ M')
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M σ)
    (hσ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M'
      (SheafOfModules.sectionsMap
        (meromorphicSectionSheafMap D.site D.base D.base_mem Y hY.1 e.hom) σ))
    {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalDivisorCycleAt D sY hY hint M' hM'
          (SheafOfModules.sectionsMap
            (meromorphicSectionSheafMap D.site D.base D.base_mem Y hY.1 e.hom) σ) hσ' hk =
      canonicalDivisorCycleAt D sY hY hint M hM σ hσ hk :=
  canonicalDivisorCycleAt_congr D sY hY hint M' M hM' hM _ σ hσ' hσ hk fun Z =>
    Z.orderOfVanishingSection_canonicalLocalRatio_sectionsMap D.site D.base D.base_mem hY.1
      (isDecentSpace_of_isGood D sY hY) M' M hM' hM hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) e.symm σ hσ

/-- **Stacks 0EPV at the canonical choices, as a rational equivalence of Weil divisors.**  Let
`Y/B` be good and integral, let `ℒ` and `𝒩` be invertible `𝒪_Y`-modules with regular meromorphic
sections `s` and `t`, and let `u` be *any* regular meromorphic section of `ℒ ⊗ 𝒩`.  Then every
integer multiple of

  `div_{ℒ⊗𝒩}(u) - (div_ℒ(s) + div_𝒩(t))`

is the principal divisor of an invertible rational function on `Y`. -/
theorem isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_picardTensorModule_sub
    (L N : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ L)
    (hN : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ N)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L s)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 N)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 N t)
    (u : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1
      (picardTensorModule D.site D.base D.base_mem hY.1 L N))
    (hu : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1
      (picardTensorModule D.site D.base D.base_mem hY.1 L N) u)
    {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (a : ℤ) :
    IsPrincipalDivisorCycle D sY k
      (a • (canonicalDivisorCycleAt D sY hY hint
            (picardTensorModule D.site D.base D.base_mem hY.1 L N)
            (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hY.1 L N hL hN)
            u hu hk -
          (canonicalDivisorCycleAt D sY hY hint L hL s hs hk +
            canonicalDivisorCycleAt D sY hY hint N hN t ht hk))) := by
  obtain ⟨_, _, _⟩ := genericHenselianLocalRing_instances D sY hY hint
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
    change divisorCycleCoefficients D sY hY _ _ st _ Z =
      divisorCycleCoefficients D sY hY _ L s _ Z + divisorCycleCoefficients D sY hY _ N t _ Z
    unfold divisorCycleCoefficients
    split_ifs
    · exact hcoeff _
    · rfl
  rw [← hsum]
  exact isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub D sY hY hint _ _ u st hu
    hstreg hk a


end Divisor

/-! ### Stacks 0EQK -/

section Cap

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    (hX : D.IsGood sX)

attribute [local instance] modulesMonoidalCategory

/-- **Stacks 03EL on an algebraic space, at a closed immersion.**  The restriction of a tensor
product of `𝒪_X`-modules to an integral closed subspace `W ⊆ X` is the tensor product of the
restrictions, `(ℒ ⊗ 𝒩)|_W ≅ ℒ|_W ⊗ 𝒩|_W`. -/
def integralClosedSubspaceRestrictPicardTensorIso
    (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    integralClosedSubspaceRestrict D sX hX
          (picardTensorModule D.site D.base D.base_mem hX.1 L N) W ≅
      picardTensorModule D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX W).1
        (integralClosedSubspaceRestrict D sX hX L W)
        (integralClosedSubspaceRestrict D sX hX N W) :=
  (modulePullback D.site D.base D.base_mem
        (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)).mapIso
      (modulesTensorObjIso D.site D.base D.base_mem X hX.1 L N).symm ≪≫
    modulePullbackTensorIso D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) L N ≪≫
    modulesTensorObjIso D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 _ _

/-- **The component rule of Stacks 0EQJ is additive up to rational equivalence on each integral
closed subspace.**  On an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` every integer
multiple of

  `c₁((ℒ⊗𝒩)|_W) ∩ [W] - (c₁(ℒ|_W) ∩ [W] + c₁(𝒩|_W) ∩ [W])`

is a principal divisor on `W`, the three component cycles being those of
`AlgebraicGeometry.Space.canonicalFirstChernRule`. -/
theorem isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_picardTensorModule_sub
    (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1) (a : ℤ) :
    IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k
      (a • (canonicalFirstChernRule D sX hX
              (picardTensorModule D.site D.base D.base_mem hX.1 L N)
              (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN)
              k W hW -
            (canonicalFirstChernRule D sX hX L hL k W hW +
              canonicalFirstChernRule D sX hX N hN k W hW))) := by
  set hYgood := isGood_integralClosedSubspace D sX hX W with hYgooddef
  set e := integralClosedSubspaceRestrictPicardTensorIso hX L N W with hedef
  have hσ := isRegularMeromorphicSection_componentMeromorphicSection sX hX
    (subspaceDivisorSetupOfIsGood D sX hX)
    (picardTensorModule D.site D.base D.base_mem hX.1 L N)
    (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN) W
  have hσ' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem
    W.subspace.toFunctor hYgood.1 e _ hσ
  rw [show canonicalFirstChernRule D sX hX
          (picardTensorModule D.site D.base D.base_mem hX.1 L N)
          (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN)
          k W hW =
        canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hYgood W.isIntegralSpace
          (picardTensorModule D.site D.base D.base_mem hYgood.1
            (integralClosedSubspaceRestrict D sX hX L W)
            (integralClosedSubspaceRestrict D sX hX N W))
          (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hYgood.1 _ _
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL W)
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W))
          (SheafOfModules.sectionsMap
            (meromorphicSectionSheafMap D.site D.base D.base_mem W.subspace.toFunctor hYgood.1
              e.hom)
            (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX)
              (picardTensorModule D.site D.base D.base_mem hX.1 L N)
              (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN) W))
          hσ' _ from
      (canonicalDivisorCycleAt_sectionsMap_iso D (W.subspace.ι ≫ sX) hYgood W.isIntegralSpace
        _ _ _ _ e _ hσ hσ' _).symm]
  exact isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_picardTensorModule_sub D
    (W.subspace.ι ≫ sX) hYgood W.isIntegralSpace _ _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
    _ (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) L hL W)
    _ (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) N hN W)
    _ hσ' _ a


/-- **The component rule of Stacks 0EQJ depends on the module only up to isomorphism, up to
rational equivalence on each integral closed subspace.**  For `e : ℳ ≅ ℳ'` and an integral
closed subspace `W ⊆ X` of δ-dimension `k + 1`, every integer multiple of
`c₁(ℳ'|_W) ∩ [W] - c₁(ℳ|_W) ∩ [W]` is a principal divisor on `W`. -/
theorem isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_sub_of_iso
    (M M' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (hM' : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M')
    (e : M ≅ M') (k : ℤ) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1) (a : ℤ) :
    IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k
      (a • (canonicalFirstChernRule D sX hX M' hM' k W hW -
        canonicalFirstChernRule D sX hX M hM k W hW)) := by
  set hYgood := isGood_integralClosedSubspace D sX hX W with hYgooddef
  set eW := (modulePullback D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)).mapIso e
    with heWdef
  have hσ := isRegularMeromorphicSection_componentMeromorphicSection sX hX
    (subspaceDivisorSetupOfIsGood D sX hX) M hM W
  have hσ' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem
    W.subspace.toFunctor hYgood.1 eW _ hσ
  rw [show canonicalFirstChernRule D sX hX M hM k W hW =
        canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hYgood W.isIntegralSpace
          (integralClosedSubspaceRestrict D sX hX M' W)
          (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M' hM' W)
          (SheafOfModules.sectionsMap
            (meromorphicSectionSheafMap D.site D.base D.base_mem W.subspace.toFunctor hYgood.1
              eW.hom)
            (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) M hM W))
          hσ' _ from
      (canonicalDivisorCycleAt_sectionsMap_iso D (W.subspace.ι ≫ sX) hYgood W.isIntegralSpace
        _ _ _ _ eW _ hσ hσ' _).symm]
  exact isPrincipalDivisorCycle_zsmul_canonicalDivisorCycleAt_sub D (W.subspace.ι ≫ sX) hYgood
    W.isIntegralSpace _
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M' hM' W) _ _
    (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) M' hM' W) hσ' _ a

/-- The integral closed subspaces at which a `k`-cycle has a nonzero coefficient form a locally
finite family. -/
theorem locallyFinite_cycleSupport {k : ℤ} (α : CycleGroup D sX k) :
    LocallyFinite fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X //
        α.1 W ≠ 0} =>
      subspacePointSet D.site D.base D.base_mem X
        (i : IntegralClosedSubspace D.site D.base D.base_mem X).subspace :=
  (α.2.1.comp_injective Subtype.val_injective).subset fun i => le_of_eq (ite_eq_right i.2).symm

/-- **The cap product of Stacks 0EQJ as a sum of Stacks 0EQ6 part (1).**  The cap product at the
canonical choices, evaluated on a `(k+1)`-cycle `α`, is the class of the locally finite sum
`∑_W α(W) · (W → X)_*(c₁(ℒ|_W) ∩ [W])` over the integral closed subspaces at which `α` has a
nonzero coefficient. -/
theorem canonicalFirstChernCap_eq_chowClass_cycleFamilySum
    (M : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCap.{u, u + 1} D sX hX M hM k α =
      chowClass.{u + 1} D sX hX k (cycleFamilySum D sX hX Subtype.val
        (locallyFinite_cycleSupport α) k
        fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
          α.1 i.1 • canonicalFirstChernRule D sX hX M hM k i.1 (α.2.2 i.1 i.2)) := by
  rw [canonicalFirstChernCap, AddMonoidHom.comp_apply,
    firstChernCapCycleMap_eq_cycleFamilySum D sX hX k (canonicalFirstChernRule D sX hX M hM k)
      α Subtype.val Subtype.val_injective (locallyFinite_cycleSupport α)
      (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
        α.2.2 i.1 i.2) fun W hW => ⟨⟨W, hW⟩, rfl⟩]

/-- *Additivity of the first Chern class cap product.* For
invertible `𝒪_X`-modules `ℒ` and `𝒩` on a good algebraic space `X/B` and every `α ∈ Z_{k+1}(X)`,

  `c₁(ℒ) ∩ α + c₁(𝒩) ∩ α = c₁(ℒ ⊗_{𝒪_X} 𝒩) ∩ α`   in   `CH_k(X)`.

The cap product is the one of Stacks 0EQJ at the canonical choices,
`AlgebraicGeometry.Space.canonicalFirstChernCap`, the tensor product is
`AlgebraicGeometry.Space.picardTensorModule`, and `CH_k(X)` is the Chow group of Stacks 0EQ6. -/
@[stacks 0EQK "first assertion: c_1(L) ∩ α + c_1(N) ∩ α = c_1(L ⊗ N) ∩ α in CH_k(X), for the \
cap product of Stacks 0EQJ at the canonical choices (canonicalFirstChernCap), the tensor \
product picardTensorModule and the Chow group of Stacks 0EQ6. DISCHARGED: the component cycle \
c_1(L|_W) ∩ [W] is the constructed canonicalFirstChernRule, not a parameter, and the tensor \
product and the product of meromorphic sections are constructed too, so nothing is carried. \
Proved from Stacks 0EPV at the canonical choices, Stacks 03EL for the restriction of a tensor \
product to W, Stacks 0EPT, and Stacks 0EQ6 parts (1), (2) and (4). CORRECTED: the source writes \
α ∈ Z_{k-1}(X), which cannot give an identity in CH_k(X) for the operation Z_{k+1}(X) → \
CH_k(X) of Stacks 0EQJ; stated here for α ∈ Z_{k+1}(X), as the identical scheme-side lemma \
Stacks 02SP does"]
theorem canonicalFirstChernCap_picardTensorModule
    (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCap.{u, u + 1} D sX hX L hL k α +
        canonicalFirstChernCap.{u, u + 1} D sX hX N hN k α =
      canonicalFirstChernCap.{u, u + 1} D sX hX
        (picardTensorModule D.site D.base D.base_mem hX.1 L N)
        (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN) k α := by
  rw [canonicalFirstChernCap_eq_chowClass_cycleFamilySum hX L hL k α,
    canonicalFirstChernCap_eq_chowClass_cycleFamilySum hX N hN k α,
    canonicalFirstChernCap_eq_chowClass_cycleFamilySum hX _ _ k α, eq_comm, ← sub_eq_zero,
    sub_add_eq_sub_sub, ← map_sub, ← map_sub, ← cycleFamilySum_sub, ← cycleFamilySum_sub]
  refine chowClass_cycleFamilySum_eq_zero.{u + 1} D sX hX k Subtype.val
    (locallyFinite_cycleSupport α) _
    (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
      α.2.2 i.1 i.2) fun i => ?_
  have h := isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_picardTensorModule_sub hX L N hL
    hN k i.1 (α.2.2 i.1 i.2) (α.1 i.1)
  rwa [smul_sub, smul_add, ← sub_sub] at h

/-- **The cap product of Stacks 0EQJ depends on the invertible module only through its
isomorphism class.**  For `e : ℳ ≅ ℳ'` the two cap products agree on every `α ∈ Z_{k+1}(X)`. -/
theorem canonicalFirstChernCap_congr_iso
    (M M' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (hM' : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M')
    (e : M ≅ M') (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCap.{u, u + 1} D sX hX M hM k α =
      canonicalFirstChernCap.{u, u + 1} D sX hX M' hM' k α := by
  rw [canonicalFirstChernCap_eq_chowClass_cycleFamilySum hX M hM k α,
    canonicalFirstChernCap_eq_chowClass_cycleFamilySum hX M' hM' k α, ← sub_eq_zero, ← map_sub,
    ← cycleFamilySum_sub]
  refine chowClass_cycleFamilySum_eq_zero.{u + 1} D sX hX k Subtype.val
    (locallyFinite_cycleSupport α) _
    (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
      α.2.2 i.1 i.2) fun i => ?_
  have h := isPrincipalDivisorCycle_zsmul_canonicalFirstChernRule_sub_of_iso hX M' M hM' hM
    e.symm k i.1 (α.2.2 i.1 i.2) (α.1 i.1)
  rwa [smul_sub] at h

/-- **The structure sheaf is an invertible `𝒪_X`-module.**  The tensor unit of
`AlgebraicGeometry.Space.Modules`, which is `𝒪_X` viewed as a module over itself
(`AlgebraicGeometry.Space.modulesTensorUnit_eq`), is invertible. -/
theorem isInvertibleModule_tensorUnit :
    IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- `ℳ ⊗_{𝒪_X} 𝒪_X ≅ ℳ`, the right unitor of the tensor product of `𝒪_X`-modules read in the
spelling `AlgebraicGeometry.Space.picardTensorModule`. -/
def picardTensorModuleUnitIso (M : Modules.{u, u} D.site D.base D.base_mem X hX.1) :
    picardTensorModule D.site D.base D.base_mem hX.1 M
        (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) ≅ M :=
  (modulesTensorObjIso D.site D.base D.base_mem X hX.1 M
    (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))).symm ≪≫ ρ_ M

/-- `c₁(𝒪_X) ∩ α = 0` in `CH_k(X)` for every `α ∈ Z_{k+1}(X)`, the structure sheaf being the
tensor unit of `AlgebraicGeometry.Space.Modules`, which is `𝒪_X` as a module over itself. -/
@[stacks 0EQK "second assertion: c_1(O_X) ∩ α = 0 in CH_k(X), for the cap product of Stacks \
0EQJ at the canonical choices (canonicalFirstChernCap) and the Chow group of Stacks 0EQ6; O_X \
is the tensor unit of the modules on the small étale site, which is the structure sheaf viewed \
as a module over itself on the nose (modulesTensorUnit_eq). DISCHARGED: the component cycle is \
the constructed canonicalFirstChernRule, not a parameter, and no section of O_X|_W is chosen; \
proved from the first assertion at L = N = O_X, the invertibility of the tensor unit, the right \
unitor O_X ⊗ O_X ≅ O_X and the isomorphism invariance canonicalFirstChernCap_congr_iso. \
CORRECTED: stated for α ∈ Z_{k+1}(X), the source's Z_{k-1}(X) being a slip"]
theorem canonicalFirstChernCap_tensorUnit_eq_zero (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCap.{u, u + 1} D sX hX
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (isInvertibleModule_tensorUnit hX) k α = 0 := by
  have h := canonicalFirstChernCap_picardTensorModule hX _ _ (isInvertibleModule_tensorUnit hX)
    (isInvertibleModule_tensorUnit hX) k α
  rw [canonicalFirstChernCap_congr_iso hX _ _
    (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 _ _
      (isInvertibleModule_tensorUnit hX) (isInvertibleModule_tensorUnit hX))
    (isInvertibleModule_tensorUnit hX) (picardTensorModuleUnitIso hX _) k α] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

end Cap

end AlgebraicGeometry.Space

end
