module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorTransport

/-!
# Commutativity of the iterated cap products with first Chern classes

In Situation 0EDT let `X/B` be good and let `ℒ`, `𝒩` be invertible `𝒪_X`-modules. Stacks 0EQZ
asserts that for `α ∈ CH_{k+2}(X)`

`c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α` in `CH_k(X)`.

## Main results

* `exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq`: the Weil divisor of a section
  on `V ⊆ Y` for a closed subspace `Y ⊆ X`, pushed to `X`, is that of a section on the image of
  `V`.
* `isRationallyEquivalentToZeroWithin_firstChernCapCycleMap_pushforward_sub`:
  `c₁(𝒩) ∩ i_*β ∼_rat i_*(c₁(𝒩|_W) ∩ β)` within `|W|`, for a closed immersion `i : W → X` of an
  integral closed subspace.
* `isRationallyEquivalentToZeroWithin_pushforward_firstChernCapCycleMap_divisor_sub`: the key
  formula on `W`, pushed forward to `X`.
* `chowClassCanonical_firstChernCapCycleMap_firstChernCapCycleMap_comm`: Stacks 0EQZ, in the Chow
  group of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK.
* `canonicalFirstChernCap_firstChernCapCycleMap_comm`: its image in the coarser quotient
  `chowGroup`.

## Implementation notes

The statement of Stacks 0EQZ is given on representatives. A class of `CH_{k+2}(X)` is the class
of a cycle `α`. The inner cap product is the cycle-level operation of Stacks 0EQJ, and the outer
one is `AlgebraicGeometry.Space.canonicalFirstChernCap`, the class in `CH_k(X)` of the
cycle-level operation. This form does not use that `c₁(ℒ) ∩ -` descends to `CH_{k+1}(X)`
(Stacks 0EQY). With that descent it is the source's statement on classes.

Every rational equivalence constructed here is a sum of principal divisors `div(f)` taken with
the canonical embeddings `R(V) → Q(𝒪^h_{V, ξ})` of Stacks 0ENK
(`AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt`), as in Stacks 0EQ6.

## References

* [Stacks Project, Tag 0EQZ](https://stacks.math.columbia.edu/tag/0EQZ)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-! ### Along the inclusion of a closed subspace -/

/-- The δ-dimension of an integral closed subspace of `Y`, read on itself, is that of its image
in `X`. -/
theorem deltaDimensionClosed_univ_closedSubspace_component
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    deltaDimensionClosed D (V.subspace.ι ≫ Y.ι ≫ sX)
        (isGood_integralClosedSubspace D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) V)
        Set.univ isClosed_univ =
      deltaDimensionClosed D ((closedSubspaceComponentImage D sX hX Y hY V).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y hY V))
        Set.univ isClosed_univ := by
  rw [deltaDimensionClosed_univ_integralClosedSubspace D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) V,
    deltaDimensionClosed_univ_integralClosedSubspace D sX hX,
    deltaDimension_closedSubspaceComponentImage]

/-- **Weil divisors of sections along the inclusion of a closed subspace.** Let `Y ⊆ X` be a
closed subspace, `V ⊆ Y` an integral closed subspace of δ-dimension `k + 1` with image `V' ⊆ X`,
and `τ` a regular meromorphic section of `(𝒩|_Y)|_V`. Then there is a regular meromorphic section
`σ` of `𝒩|_{V'}` with

`(Y → X)_*(V → Y)_* div(τ) = (V' → X)_* div(σ)`.

The restriction `𝒩|_Y` is any module `NY` on `Y` equal to it. -/
theorem exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (NY : Modules.{u, u} D.site D.base D.base_mem Y.toFunctor hY.1)
    (hNY : NY = (modulePullback D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem hX.1 Y hY)).obj N)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) {k : ℤ}
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      (isGood_integralClosedSubspace D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) V).1
      (integralClosedSubspaceRestrict D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY)
        NY V))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      (isGood_integralClosedSubspace D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY)
        V).1 _ τ)
    (hk : deltaDimensionClosed D (V.subspace.ι ≫ Y.ι ≫ sX)
      (isGood_integralClosedSubspace D (Y.ι ≫ sX) (isGood_ι_of_isClosedSubspace D sX hX Y hY) V)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hk' : deltaDimensionClosed D ((closedSubspaceComponentImage D sX hX Y hY V).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y hY V))
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    ∃ (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem
        (closedSubspaceComponentImage D sX hX Y hY V).subspace.toFunctor
        (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y hY V)).1
        (integralClosedSubspaceRestrict D sX hX N (closedSubspaceComponentImage D sX hX Y hY V)))
      (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _
        (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y hY V)).1
        _ σ),
      cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
          (Y.ι ≫ sX) rfl k
          (integralClosedSubspacePushforward D (Y.ι ≫ sX)
            (isGood_ι_of_isClosedSubspace D sX hX Y hY) V k
            (canonicalDivisorCycleAt D (V.subspace.ι ≫ Y.ι ≫ sX)
              (isGood_integralClosedSubspace D (Y.ι ≫ sX)
                (isGood_ι_of_isClosedSubspace D sX hX Y hY) V)
              V.isIntegralSpace _
              (isInvertibleModule_integralClosedSubspaceRestrict D (Y.ι ≫ sX)
                (isGood_ι_of_isClosedSubspace D sX hX Y hY) _
                (hNY ▸ modulePullbackInvertible
                  (closedSubspaceHom D.site D.base D.base_mem hX.1 Y hY) N hN) V)
              τ hτ hk)) =
        integralClosedSubspacePushforward D sX hX (closedSubspaceComponentImage D sX hX Y hY V) k
          (canonicalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX
              (closedSubspaceComponentImage D sX hX Y hY V))
            (closedSubspaceComponentImage D sX hX Y hY V).isIntegralSpace
            _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN _) σ hσ hk') := by
  subst hNY
  have hdec := isDecentSpace_of_isGood D sX hX
  have hYg := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hgV := isGood_integralClosedSubspace D (Y.ι ≫ sX) hYg V
  have hgV' := isGood_integralClosedSubspace D sX hX
    (closedSubspaceComponentImage D sX hX Y hY V)
  let φ := IntegralClosedSubspace.isoPushforward hX.1 hY.1 hdec hY.2 V
  have hφ : φ.hom ≫ (closedSubspaceComponentImage D sX hX Y hY V).subspace.ι =
      V.subspace.ι ≫ Y.ι :=
    IntegralClosedSubspace.isoPushforward_hom_comp_ι hX.1 hY.1 hdec hY.2 V
  let VA : AlgebraicSpaces D.site D.base D.base_mem := ⟨V.subspace.toFunctor, hgV.1⟩
  let VA' : AlgebraicSpaces D.site D.base D.base_mem :=
    ⟨(closedSubspaceComponentImage D sX hX Y hY V).subspace.toFunctor, hgV'.1⟩
  let ψ : VA' ≅ VA := ObjectProperty.isoMk _ φ.symm
  let NW := (modulePullback D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 Y hY)).obj N
  have hNW := modulePullbackInvertible (closedSubspaceHom D.site D.base D.base_mem hX.1 Y hY)
    N hN
  let NV := integralClosedSubspaceRestrict D (Y.ι ≫ sX) hYg NW V
  have hNV := isInvertibleModule_integralClosedSubspaceRestrict D (Y.ι ≫ sX) hYg NW hNW V
  let NV' := integralClosedSubspaceRestrict D sX hX N
    (closedSubspaceComponentImage D sX hX Y hY V)
  have hNV' := isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN
    (closedSubspaceComponentImage D sX hX Y hY V)
  have hf := pullbacksMeromorphicSections_of_iso D.site D.base D.base_mem ψ
  let σ₀ := pullbackMeromorphicSection D.site D.base D.base_mem ψ.hom NV hf τ
  have hσ₀ := isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
    ψ.hom hf NV (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hNV) τ hτ
  let iW := closedSubspaceHom D.site D.base D.base_mem hX.1 Y hY
  let iV := closedSubspaceHom D.site D.base D.base_mem hYg.1 V.subspace V.isClosedSubspace
  let iV' := closedSubspaceHom D.site D.base D.base_mem hX.1
    (closedSubspaceComponentImage D sX hX Y hY V).subspace
    (closedSubspaceComponentImage D sX hX Y hY V).isClosedSubspace
  have hcomp : ψ.hom ≫ iV ≫ iW = iV' := by
    ext1
    change φ.inv ≫ V.subspace.ι ≫ Y.ι = (closedSubspaceComponentImage D sX hX Y hY V).subspace.ι
    rw [← hφ]
    exact Iso.inv_hom_id_assoc φ _
  obtain ⟨β⟩ : Nonempty ((modulePullback D.site D.base D.base_mem ψ.hom).obj NV ≅ NV') :=
    ⟨(modulePullback D.site D.base D.base_mem ψ.hom).mapIso
        ((modulePullbackCompIso D.site D.base D.base_mem iV iW).app N) ≪≫
      (modulePullbackCompIso D.site D.base D.base_mem ψ.hom (iV ≫ iW)).app N ≪≫
      eqToIso (by rw [hcomp])⟩
  let σ := SheafOfModules.sectionsMap
    (meromorphicSectionSheafMap D.site D.base D.base_mem _ _ β.hom) σ₀
  have hσ := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem _ _ β σ₀ hσ₀
  refine ⟨σ, hσ, ?_⟩
  have hdecV' := isDecentSpace_of_isGood D _ hgV'
  have hB₁ := congrArg Subtype.val (canonicalDivisorCycle_sectionsMap_of_iso D _ hgV'
    (closedSubspaceComponentImage D sX hX Y hY V).isIntegralSpace _ NV'
    (modulePullbackInvertible ψ.hom NV hNV) hNV' β σ₀ hσ₀ hk')
  have hB₂ := cycleClosedPushforward_canonicalDivisorCycle_pullbackMeromorphicSection_of_iso D
    ((closedSubspaceComponentImage D sX hX Y hY V).subspace.ι ≫ sX) hgV'
    (V.subspace.ι ≫ Y.ι ≫ sX) hgV (closedSubspaceComponentImage D sX hX Y hY V).isIntegralSpace
    V.isIntegralSpace ψ NV hNV τ hτ hk' hk
  have hψφ : ψ.hom.hom ≫ φ.hom = 𝟙 _ := φ.inv_hom_id
  have hB₃ : (canonicalDivisorCycle D _ hgV'
        (closedSubspaceComponentImage D sX hX Y hY V).isIntegralSpace
        ((modulePullback D.site D.base D.base_mem ψ.hom).obj NV)
        (modulePullbackInvertible ψ.hom NV hNV) σ₀ hσ₀ hk').1 =
      cycleClosedPushforward D hgV'.1 hgV.1 hdecV'
        (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom)
        (canonicalDivisorCycle D _ hgV V.isIntegralSpace NV hNV τ hτ hk).1 := by
    have hfun := cycleClosedPushforward_cycleClosedPushforward D hgV'.1 hgV.1 hgV'.1 hdecV'
      (isDecentSpace_of_isGood D _ hgV) hψφ
      (isClosedImmersion_of_isIso D.site D.base D.base_mem ψ.hom.hom)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 _))
      (canonicalDivisorCycle D _ hgV' (closedSubspaceComponentImage D sX hX Y hY V).isIntegralSpace
        ((modulePullback D.site D.base D.base_mem ψ.hom).obj NV)
        (modulePullbackInvertible ψ.hom NV hNV) σ₀ hσ₀ hk').1
    rw [cycleClosedPushforward_id_eq_self] at hfun
    rw [← hB₂]
    exact hfun.symm
  have hl : IsClosedImmersion D.site D.base D.base_mem (V.subspace.ι ≫ Y.ι) :=
    isClosedImmersion_comp D.site D.base D.base_mem _ _ V.isClosedSubspace.2 hY.2
  refine Subtype.ext ?_
  have h₁ := cycleClosedPushforward_cycleClosedPushforward D hX.1 hY.1
    V.isClosedSubspace.1 hdec (isDecentSpace_of_isGood D _ hYg) rfl V.isClosedSubspace.2
    hY.2 hl (canonicalDivisorCycle D _ hgV V.isIntegralSpace NV hNV τ hτ hk).1
  have h₂ := cycleClosedPushforward_cycleClosedPushforward D hX.1
    (closedSubspaceComponentImage D sX hX Y hY V).isClosedSubspace.1
    V.isClosedSubspace.1 hdec hdecV' hφ
    (isClosedImmersion_of_isIso D.site D.base D.base_mem φ.hom)
    (closedSubspaceComponentImage D sX hX Y hY V).isClosedSubspace.2 hl
    (canonicalDivisorCycle D _ hgV V.isIntegralSpace NV hNV τ hτ hk).1
  refine h₁.trans (h₂.symm.trans (congrArg _ ?_))
  exact ((canonicalDivisorCycleAt_coe D _ hgV'
    (closedSubspaceComponentImage D sX hX Y hY V).isIntegralSpace NV' hNV' σ hσ hk').trans
    (hB₁.trans hB₃)).symm


section Transport

variable (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)

/-- The δ-dimension of the image in `X` of an integral closed subspace of `W`, from the
δ-dimension of the subspace read on itself. -/
theorem deltaDimension_closedSubspaceComponentImage_of_deltaDimensionClosed
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) {n : ℤ}
    (hk : deltaDimensionClosed D (V.subspace.ι ≫ W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V) Set.univ isClosed_univ = (n : EInt)) :
    deltaDimension D sX (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace V) =
      n := by
  have h := (deltaDimensionClosed_univ_closedSubspace_component D sX hX
    W.subspace W.isClosedSubspace V).symm.trans hk
  rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX] at h
  exact WithBotTop.coe_injective h

/-- An integer multiple of the difference of the Weil divisors of two regular meromorphic sections
of `𝒩|_W`, pushed forward to `X`, is canonically rationally equivalent to zero within `|W|`. -/
private theorem isCanonicallyRationallyEquivalentToZeroWithin_pushforward_zsmul_sub
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N) {k : ℤ}
    (σ σ' : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 (integralClosedSubspaceRestrict D sX hX N W))
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 _ σ)
    (hσ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 _ σ')
    (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) (a : ℤ) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (integralClosedSubspacePushforward D sX hX W k
        (a • (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace _
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) σ hσ hk -
          canonicalDivisorCycleAt D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace _
            (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) σ' hσ' hk)))
      (subspacePointSet D.site D.base D.base_mem X W.subspace) :=
  isCycleFamilySumWithin_integralClosedSubspacePushforward D sX hX k _
    ((exists_zsmul_sub_canonicalDivisorCycleAt_eq D _ (isGood_integralClosedSubspace D sX hX _)
      W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN _) σ σ'
      hσ hσ' hk a).elim fun g hg => ⟨hk, g, hg⟩)

/-- An integer multiple of the difference of the Weil divisors of two regular meromorphic
sections of `(𝒩|_W)|_V`, for an integral closed subspace `V ⊆ W` of δ-dimension `k + 1`, pushed
forward along `V → W → X`, is rationally equivalent to zero within the image `|V| ⊆ |X|`. -/
theorem isRationallyEquivalentToZeroWithin_pushforward_pushforward_zsmul_sub
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) {k : ℤ}
    (τ τ' : MeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V).1
      (integralClosedSubspaceRestrict D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) (integralClosedSubspaceRestrict D sX hX N W) V))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V).1 _ τ)
    (hτ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V).1 _ τ')
    (hk : deltaDimensionClosed D (V.subspace.ι ≫ W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V) Set.univ isClosed_univ =
        ((k + 1 : ℤ) : EInt)) (a : ℤ) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (integralClosedSubspacePushforward D sX hX W k
        (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) V k
          (a • (canonicalDivisorCycleAt D (V.subspace.ι ≫ W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) V) V.isIntegralSpace _
              (isInvertibleModule_integralClosedSubspaceRestrict D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) _
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) V)
              τ hτ hk -
            canonicalDivisorCycleAt D (V.subspace.ι ≫ W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) V) V.isIntegralSpace _
              (isInvertibleModule_integralClosedSubspaceRestrict D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) _
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) V)
              τ' hτ' hk))))
      (subspacePointSet D.site D.base D.base_mem X
        (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace V).subspace) := by
  have hk' := (deltaDimensionClosed_univ_closedSubspace_component D sX hX
    W.subspace W.isClosedSubspace V).symm.trans hk
  obtain ⟨σ, hσ, h⟩ := exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq D sX hX
    W.subspace W.isClosedSubspace N hN (integralClosedSubspaceRestrict D sX hX N W) rfl
    V τ hτ hk hk'
  replace h : integralClosedSubspacePushforward D sX hX W k _ = _ := h
  obtain ⟨σ', hσ', h'⟩ := exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq D sX hX
    W.subspace W.isClosedSubspace N hN (integralClosedSubspaceRestrict D sX hX N W) rfl
    V τ' hτ' hk hk'
  replace h' : integralClosedSubspacePushforward D sX hX W k _ = _ := h'
  rw [map_zsmul, map_sub, map_zsmul, map_sub, h, h', ← map_sub, ← map_zsmul]
  exact isCanonicallyRationallyEquivalentToZeroWithin_pushforward_zsmul_sub D sX hX _ N hN σ σ'
    hσ hσ' hk' a

/-- **The component cycle at the image of a subspace of `W`.** For an integral closed subspace
`V ⊆ W` of δ-dimension `k + 1` with image `V' ⊆ X`, and any regular meromorphic section `τ` of
`(𝒩|_W)|_V`, the component cycle `c₁(𝒩|_{V'}) ∩ [V']` of Stacks 0EQJ at the canonical choices
and the pushforward of `div(τ)` along `V → W → X` are rationally equivalent within `|V'|`. -/
theorem isRationallyEquivalentToZeroWithin_firstChernComponentCycle_sub_pushforward_pushforward
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor) {k : ℤ}
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V).1
      (integralClosedSubspaceRestrict D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) (integralClosedSubspaceRestrict D sX hX N W) V))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem V.subspace.toFunctor
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V).1 _ τ)
    (hk : deltaDimensionClosed D (V.subspace.ι ≫ W.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) V) Set.univ isClosed_univ =
        ((k + 1 : ℤ) : EInt)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (firstChernComponentCycle D sX hX k (canonicalFirstChernRule D sX hX N hN k)
          (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace V) -
        integralClosedSubspacePushforward D sX hX W k
          (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W) V k
            (canonicalDivisorCycleAt D (V.subspace.ι ≫ W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) V) V.isIntegralSpace _
              (isInvertibleModule_integralClosedSubspaceRestrict D (W.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX W) _
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) V)
              τ hτ hk)))
      (subspacePointSet D.site D.base D.base_mem X
        (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace V).subspace) := by
  have hk' := (deltaDimensionClosed_univ_closedSubspace_component D sX hX
    W.subspace W.isClosedSubspace V).symm.trans hk
  have hdim := deltaDimension_closedSubspaceComponentImage_of_deltaDimensionClosed D sX hX W V hk
  obtain ⟨σ, hσ, h⟩ := exists_closedSubspaceCyclePushforward_canonicalDivisorCycleAt_eq D sX hX
    W.subspace W.isClosedSubspace N hN (integralClosedSubspaceRestrict D sX hX N W) rfl
    V τ hτ hk hk'
  replace h : integralClosedSubspacePushforward D sX hX W k _ = _ := h
  rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k _ hdim, h, ← map_sub,
    ← one_smul ℤ (_ - _)]
  exact isCanonicallyRationallyEquivalentToZeroWithin_pushforward_zsmul_sub D sX hX _ N hN _ σ
    (isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) N hN _) hσ hk' 1

end Transport

/-- A sum over `β` of a function supported in the range of an injective map `e : α → β` is the
sum over `α` of its composite with `e`. -/
theorem finsum_eq_finsum_comp_of_support_subset_range {α β M : Type*} [AddCommMonoid M]
    {e : α → β} (he : Function.Injective e) {g : β → M}
    (hg : Function.support g ⊆ Set.range e) :
    ∑ᶠ y, g y = ∑ᶠ x, g (e x) := by
  rw [← finsum_mem_range he, ← finsum_mem_univ g]
  exact (finsum_mem_inter_support_eq g _ _ (by rw [Set.univ_inter, Set.inter_eq_right.2 hg])).symm

section ClosedImmersionCap

variable (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **The cap product with `c₁(𝒩)` along the inclusion of an integral closed subspace.** For an
integral closed subspace `i : W → X` and a `(k+1)`-cycle `β` on `W`, the cycle
`c₁(𝒩) ∩ i_*β - i_*(c₁(𝒩|_W) ∩ β)` is rationally equivalent to zero within `|W|`, the cap
products being those of Stacks 0EQJ at the canonical choices on `X` and on `W`. -/
theorem isRationallyEquivalentToZeroWithin_firstChernCapCycleMap_pushforward_sub {k : ℤ}
    (β : CycleGroup D (W.subspace.ι ≫ sX) (k + 1)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
          (integralClosedSubspacePushforward D sX hX W (k + 1) β) -
        integralClosedSubspacePushforward D sX hX W k
          (firstChernCapCycleMap D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
            k (canonicalFirstChernRule D (W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D sX hX W)
              (integralClosedSubspaceRestrict D sX hX N W)
              (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) k) β))
      (subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hdec := isDecentSpace_of_isGood D sX hX
  have hY := isGood_integralClosedSubspace D sX hX W
  let img := closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
  have himg : Function.Injective img := IntegralClosedSubspace.injective_pushforward D.site
    D.base D.base_mem hX.1 W.isClosedSubspace.1 hdec W.isClosedSubspace.2
  let push := fun j : ℤ => integralClosedSubspacePushforward D sX hX W j
  have hpush : ∀ (j : ℤ) (γ : CycleGroup D (W.subspace.ι ≫ sX) j) V,
      (push j γ).1 (img V) = γ.1 V := fun j γ V =>
    integralClosedSubspacePushforward_apply_pushforward D sX hX W γ V
  have hpush0 : ∀ (j : ℤ) (γ : CycleGroup D (W.subspace.ι ≫ sX) j) Z,
      (∀ V, img V ≠ Z) → (push j γ).1 Z = 0 := fun j γ Z hZ =>
    integralClosedSubspacePushforward_apply_of_forall_ne D sX hX W γ Z hZ
  let chern := canonicalFirstChernRule D sX hX N hN k
  let chernW := canonicalFirstChernRule D (W.subspace.ι ≫ sX) hY
    (integralClosedSubspaceRestrict D sX hX N W)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) k
  have hT : LocallyFinite fun V : IntegralClosedSubspace D.site D.base D.base_mem
      W.subspace.toFunctor =>
      if β.1 V = 0 then (∅ : Set (points D.site D.base D.base_mem X))
      else subspacePointSet D.site D.base D.base_mem X (img V).subspace := by
    refine ((push (k + 1) β).2.1.comp_injective himg).subset fun V => ?_
    simp only [Function.comp_apply, hpush]
    exact subset_rfl
  have hδ : ∀ V, IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (firstChernComponentCycle D sX hX k chern (img V) -
        push k (firstChernComponentCycle D (W.subspace.ι ≫ sX) hY k chernW V))
      (subspacePointSet D.site D.base D.base_mem X (img V).subspace) := by
    intro V
    by_cases hV : deltaDimension D (W.subspace.ι ≫ sX) V = k + 1
    · rw [firstChernComponentCycle_of_deltaDimension_eq D (W.subspace.ι ≫ sX) hY k chernW hV]
      exact isRationallyEquivalentToZeroWithin_firstChernComponentCycle_sub_pushforward_pushforward
        D sX hX W N hN V _ _
        (by rw [deltaDimensionClosed_univ_integralClosedSubspace D (W.subspace.ι ≫ sX) hY V, hV])
    · rw [firstChernComponentCycle_of_deltaDimension_ne D (W.subspace.ι ≫ sX) hY k chernW hV,
        firstChernComponentCycle_of_deltaDimension_ne D sX hX k chern
          (by rwa [deltaDimension_closedSubspaceComponentImage]), map_zero, sub_zero]
      exact isCycleFamilySumWithin_zero D sX hX k _
  have h := isCycleFamilySumWithin_finsum.{u, v, u + 1} D sX hX k _ hT
    (P := canonicalPrincipalDivisors D sX hX k)
    (fun V => β.1 V • (firstChernComponentCycle D sX hX k chern (img V) -
      push k (firstChernComponentCycle D (W.subspace.ι ≫ sX) hY k chernW V)))
    (fun V => by
      by_cases hV : β.1 V = 0
      · simp only [hV, ite_true, zero_smul]
        exact isCycleFamilySumWithin_zero D sX hX k _
      · simp only [hV, ite_false]
        exact (hδ V).zsmul neg_mem_canonicalPrincipalDivisors _)
    (α := firstChernCapCycleMap D sX hX k chern (push (k + 1) β) -
      push k (firstChernCapCycleMap D (W.subspace.ι ≫ sX) hY k chernW β))
    (fun Z => ?_)
  · refine h.mono (Set.iUnion_subset fun V => ?_)
    split_ifs
    · exact Set.empty_subset _
    · rw [IntegralClosedSubspace.subspacePointSet_pushforward]
      exact Set.image_subset_range _ _
  have hreindex : ∑ᶠ Z' : IntegralClosedSubspace D.site D.base D.base_mem X,
      (push (k + 1) β).1 Z' * (firstChernComponentCycle D sX hX k chern Z').1 Z =
      ∑ᶠ V, β.1 V * (firstChernComponentCycle D sX hX k chern (img V)).1 Z := by
    rw [finsum_eq_finsum_comp_of_support_subset_range himg]
    · simp only [hpush]
    · intro Z' hZ'
      by_contra hne
      refine hZ' ?_
      change (push (k + 1) β).1 Z' * _ = 0
      rw [hpush0 _ _ Z' fun V hV => hne ⟨V, hV⟩, zero_mul]
  have hfinX : Function.HasFiniteSupport fun V =>
      β.1 V * (firstChernComponentCycle D sX hX k chern (img V)).1 Z := by
    refine ((hasFiniteSupport_firstChernCapCoeff D sX hX k chern (push (k + 1) β) Z).preimage
      himg.injOn).subset fun V hV => ?_
    simpa only [Function.mem_support, Set.mem_preimage, hpush] using hV
  change (firstChernCapCycleMap D sX hX k chern (push (k + 1) β)).1 Z -
      (push k (firstChernCapCycleMap D (W.subspace.ι ≫ sX) hY k chernW β)).1 Z = _
  rw [firstChernCapCycleMap_apply, hreindex]
  by_cases hZ : ∃ V₀, img V₀ = Z
  · obtain ⟨V₀, rfl⟩ := hZ
    rw [hpush, firstChernCapCycleMap_apply,
      ← finsum_sub_distrib hfinX
        (hasFiniteSupport_firstChernCapCoeff D (W.subspace.ι ≫ sX) hY k chernW β V₀)]
    refine finsum_congr fun V => ?_
    change _ = β.1 V * ((firstChernComponentCycle D sX hX k chern (img V)).1 (img V₀) -
      (push k (firstChernComponentCycle D (W.subspace.ι ≫ sX) hY k chernW V)).1 (img V₀))
    rw [hpush, mul_sub]
  · rw [hpush0 _ _ Z fun V hV => hZ ⟨V, hV⟩, sub_zero]
    refine finsum_congr fun V => ?_
    change _ = β.1 V * ((firstChernComponentCycle D sX hX k chern (img V)).1 Z -
      (push k (firstChernComponentCycle D (W.subspace.ι ≫ sX) hY k chernW V)).1 Z)
    rw [hpush0 _ _ Z fun V hV => hZ ⟨V, hV⟩, sub_zero]

/-- **A locally finite sum on `W`, pushed forward to `X`.** Let `{V_i}` be a locally finite family
of integral closed subspaces of an integral closed subspace `W ⊆ X` and `c_i` cycles on them. If
each `(V_i → W → X)_* c_i` is rationally equivalent to zero within the image of `V_i` in `X`, then
the pushforward to `X` of `∑_i (V_i → W)_* c_i` is rationally equivalent to zero within
`|W|`. -/
theorem isRationallyEquivalentToZeroWithin_pushforward_cycleFamilySum {I : Type w} {k : ℤ}
    (V : I → IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (hV : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem W.subspace.toFunctor
      (V i).subspace)
    (c : ∀ i, CycleGroup D ((V i).subspace.ι ≫ W.subspace.ι ≫ sX) k)
    (hc : ∀ i, IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D sX hX k
      (integralClosedSubspacePushforward D sX hX W k
        (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) (V i) k (c i)))
      (subspacePointSet D.site D.base D.base_mem X
        (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace (V i)).subspace)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max w v} D sX hX k
      (integralClosedSubspacePushforward D sX hX W k
        (cycleFamilySum D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) V hV k c))
      (subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hdec := isDecentSpace_of_isGood D sX hX
  have hY := isGood_integralClosedSubspace D sX hX W
  let img := closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace
  let push := fun j : ℤ => integralClosedSubspacePushforward D sX hX W j
  have hpush : ∀ (j : ℤ) (γ : CycleGroup D (W.subspace.ι ≫ sX) j) V,
      (push j γ).1 (img V) = γ.1 V := fun j γ V =>
    integralClosedSubspacePushforward_apply_pushforward D sX hX W γ V
  have hpush0 : ∀ (j : ℤ) (γ : CycleGroup D (W.subspace.ι ≫ sX) j) Z,
      (∀ V, img V ≠ Z) → (push j γ).1 Z = 0 := fun j γ Z hZ =>
    integralClosedSubspacePushforward_apply_of_forall_ne D sX hX W γ Z hZ
  have hT : LocallyFinite fun i => subspacePointSet D.site D.base D.base_mem X
      (img (V i)).subspace :=
    locallyFinite_of_isClosedEmbedding_extend
      (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
        W.isClosedSubspace.2) (e := id) (fun i hi => absurd rfl (hi i))
      (fun i => (IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem
        hX.1 W.isClosedSubspace.1 hdec W.isClosedSubspace.2 (V i)).le) hV
  refine (isCycleFamilySumWithin_finsum.{u, v, w} D sX hX k _ hT _ hc
    fun Z => ?_).mono (Set.iUnion_subset fun i => ?_)
  · by_cases hZ : ∃ V₀, img V₀ = Z
    · obtain ⟨V₀, rfl⟩ := hZ
      change (push k _).1 (img V₀) = _
      rw [hpush, cycleFamilySum_apply]
      refine finsum_congr fun i => ?_
      change _ = (push k _).1 (img V₀)
      rw [hpush]
    · rw [hpush0 _ _ Z fun V hV => hZ ⟨V, hV⟩]
      exact (finsum_eq_zero_of_forall_eq_zero fun i => hpush0 _ _ Z
        fun V hV => hZ ⟨V, hV⟩).symm
  · rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.image_subset_range _ _

end ClosedImmersionCap

section KeyFormula

variable (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **The key formula on an integral closed subspace, pushed forward.** Let `W ⊆ X` be an
integral closed subspace with `dim_δ(W) = k + 2` and `s`, `t` regular meromorphic sections of
`ℒ|_W`, `𝒩|_W`. Then the pushforward to `X` of

`c₁(𝒩|_W) ∩ div_{ℒ|_W}(s) - c₁(ℒ|_W) ∩ div_{𝒩|_W}(t)`

is rationally equivalent to zero within `|W|`. This is the key formula of Section 0EQU on `W`
(Stacks 0EQV), at the level of cycles. -/
theorem isRationallyEquivalentToZeroWithin_pushforward_firstChernCapCycleMap_divisor_sub
    {k : ℤ}
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 (integralClosedSubspaceRestrict D sX hX L W))
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 _ s)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 (integralClosedSubspaceRestrict D sX hX N W))
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (isGood_integralClosedSubspace D sX hX W).1 _ t)
    (hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D sX hX k
      (integralClosedSubspacePushforward D sX hX W k
        (firstChernCapCycleMap D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) k
            (canonicalFirstChernRule D (W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D sX hX W)
              (integralClosedSubspaceRestrict D sX hX N W)
              (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W) k)
            (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
              W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL W)
              s hs hn) -
          firstChernCapCycleMap D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) k
            (canonicalFirstChernRule D (W.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D sX hX W)
              (integralClosedSubspaceRestrict D sX hX L W)
              (isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL W) k)
            (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
              W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W)
              t ht hn)))
      (subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hY := isGood_integralClosedSubspace D sX hX W
  have hint := W.isIntegralSpace
  let LW := integralClosedSubspaceRestrict D sX hX L W
  have hLW := isInvertibleModule_integralClosedSubspaceRestrict D sX hX L hL W
  let NW := integralClosedSubspaceRestrict D sX hX N W
  have hNW := isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN W
  let I := {P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor //
    ¬ (P.SectionGenerates D (W.subspace.ι ≫ sX) hY hint LW hLW s ∧
      P.SectionGenerates D (W.subspace.ι ≫ sX) hY hint NW hNW t)}
  let Zf : I → PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor := Subtype.val
  let Zf' := fun i : I => (Zf i).toIntegralClosedSubspace D.site D.base D.base_mem
  have hfin : LocallyFinite fun i : I =>
      subspacePointSet D.site D.base D.base_mem W.subspace.toFunctor (Zf' i).subspace :=
    locallyFinite_primeDivisor_not_sectionGenerates D (W.subspace.ι ≫ sX) hY hint LW hLW s hs
      NW hNW t ht
  have hinj : Function.Injective Zf := Subtype.val_injective
  have hcov : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      (∀ i, Zf i ≠ P) → P.SectionGenerates D (W.subspace.ι ≫ sX) hY hint LW hLW s ∧
        P.SectionGenerates D (W.subspace.ι ≫ sX) hY hint NW hNW t := fun P hP =>
    Classical.byContradiction fun h => hP ⟨P, h⟩ rfl
  have hdim : ∀ i, deltaDimension D (W.subspace.ι ≫ sX) (Zf' i) = k + 1 := fun i =>
    (deltaDimension_toIntegralClosedSubspace D (W.subspace.ι ≫ sX) hY hint
      (deltaDimensionFunction D (W.subspace.ι ≫ sX) hY)
      (deltaDimensionFunction_apply D (W.subspace.ι ≫ sX) hY) hn (Zf i)).trans
      (add_sub_cancel_right _ _)
  have hinj' : Function.Injective Zf' :=
    (PrimeDivisor.injective_toIntegralClosedSubspace D.site D.base D.base_mem).comp hinj
  have hcoverS : ∀ V, (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hY hint LW hLW s hs hn).1 V
      ≠ 0 → ∃ i, Zf' i = V := by
    intro V hV
    by_contra h
    push Not at h
    exact hV (canonicalDivisorCycle_apply_eq_zero_of_notMem D (W.subspace.ι ≫ sX) hY hint LW hLW
      s hs hn Zf (fun P hP => (hcov P hP).1) V h)
  have hcoverT : ∀ V, (canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) hY hint NW hNW t ht hn).1 V
      ≠ 0 → ∃ i, Zf' i = V := by
    intro V hV
    by_contra h
    push Not at h
    exact hV (canonicalDivisorCycle_apply_eq_zero_of_notMem D (W.subspace.ι ≫ sX) hY hint NW hNW
      t ht hn Zf (fun P hP => (hcov P hP).2) V h)
  rw [firstChernCapCycleMap_eq_cycleFamilySum D (W.subspace.ι ≫ sX) hY k _ _ Zf' hinj' hfin hdim
      hcoverS,
    firstChernCapCycleMap_eq_cycleFamilySum D (W.subspace.ι ≫ sX) hY k _ _ Zf' hinj' hfin hdim
      hcoverT]
  have hkey : cycleFamilySum D (W.subspace.ι ≫ sX) hY Zf' hfin k (fun i =>
        (Zf i).keyFormulaDivisorCycle D (W.subspace.ι ≫ sX) hY hint LW hLW s hs NW hNW t ht hn
          1 1) =
      keyFormulaTameSum D (W.subspace.ι ≫ sX) hY hint LW hLW s hs NW hNW t ht hn Zf hfin
        (fun _ => 1) (fun _ => 1) :=
    keyFormulaDivisorSum_eq_keyFormulaTameSum D (W.subspace.ι ≫ sX) hY hint LW hLW s hs NW hNW
      t ht hn Zf (fun _ => 1) (fun _ => 1) hfin hinj hcov
  have hsplit : ∀ a b : ∀ i, CycleGroup D ((Zf' i).subspace.ι ≫ W.subspace.ι ≫ sX) k,
      cycleFamilySum D (W.subspace.ι ≫ sX) hY Zf' hfin k a -
          cycleFamilySum D (W.subspace.ι ≫ sX) hY Zf' hfin k b =
        cycleFamilySum D (W.subspace.ι ≫ sX) hY Zf' hfin k (fun i => a i - b i -
          (Zf i).keyFormulaDivisorCycle D (W.subspace.ι ≫ sX) hY hint LW hLW s hs NW hNW t ht hn
            1 1) +
        keyFormulaTameSum D (W.subspace.ι ≫ sX) hY hint LW hLW s hs NW hNW t ht hn Zf hfin
          (fun _ => 1) (fun _ => 1) := by
    intro a b
    rw [cycleFamilySum_sub, cycleFamilySum_sub, ← hkey]
    abel
  rw [hsplit, map_add]
  refine (isRationallyEquivalentToZeroWithin_pushforward_cycleFamilySum.{v, u, u + 1} D sX hX W
    Zf' hfin _ fun i => ?_).add
    (isRationallyEquivalentToZeroWithin_pushforward_cycleFamilySum.{v, u, u + 1} D sX hX W
      Zf' hfin _ fun i => ?_)
  · obtain ⟨hfs, hαs⟩ := orderOfVanishingSection_canonical_eq_ord D (W.subspace.ι ≫ sX) hY hint LW
      hLW s hs (Zf i) _ (1 : _ˣ).isUnit _
      ((Zf i).sectionRatio_mul D (W.subspace.ι ≫ sX) hY hint LW hLW s hs 1)
    obtain ⟨hft, hαt⟩ := orderOfVanishingSection_canonical_eq_ord D (W.subspace.ι ≫ sX) hY hint NW
      hNW t ht (Zf i) _ (1 : _ˣ).isUnit _
      ((Zf i).sectionRatio_mul D (W.subspace.ι ≫ sX) hY hint NW hNW t ht 1)
    rw [canonicalDivisorCycleAt_coe, canonicalDivisorCycle_apply_primeDivisor,
      canonicalDivisorCycleAt_coe, canonicalDivisorCycle_apply_primeDivisor, hαs, hαt]
    unfold PrimeDivisor.keyFormulaDivisorCycle
    rw [show ∀ (x y z w : CycleGroup D ((Zf' i).subspace.ι ≫ W.subspace.ι ≫ sX) k) (m n : ℤ),
        m • x - n • y - (m • z - n • w) = m • (x - z) - n • (y - w) from
      fun x y z w m n => by rw [smul_sub, smul_sub]; abel, map_sub, map_sub]
    exact (isRationallyEquivalentToZeroWithin_pushforward_pushforward_zsmul_sub D sX hX W N hN
      (Zf' i) _ _ _ _ _ _).sub
      (isRationallyEquivalentToZeroWithin_pushforward_pushforward_zsmul_sub D sX hX W L hL
        (Zf' i) _ _ _ _ _ _) neg_mem_canonicalPrincipalDivisors
  · refine (IsCanonicallyRationallyEquivalentToZeroWithin.closedPushforward (hX := hX) _
      (isGood_integralClosedSubspace D sX hX W) W.isClosedSubspace.2 rfl
      (isCycleFamilySumWithin_integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) k (Zf' i)
        (P := canonicalPrincipalDivisors D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) k)
        ⟨_, _, rfl⟩)).mono ?_
    rw [IntegralClosedSubspace.subspacePointSet_pushforward]

end KeyFormula

section Commutativity

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **The two iterated cap products on one integral closed subspace.** For an integral closed
subspace `W ⊆ X` of δ-dimension `k + 2`, the cycle

`c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]) - c₁(𝒩) ∩ (c₁(ℒ) ∩ [W])`

is rationally equivalent to zero within `|W|`, the cap products being those of Stacks 0EQJ at
the canonical choices. -/
theorem isRationallyEquivalentToZeroWithin_firstChernCapCycleMap_firstChernComponentCycle_comm
    {k : ℤ} (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1 + 1) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX L hL k)
          (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            W) -
        firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
          (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX L hL (k + 1))
            W))
      (subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  have hn : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW]
  have hreg := fun (M : Modules.{u, u} D.site D.base D.base_mem X hX.1) hM =>
    isRegularMeromorphicSection_componentMeromorphicSection sX hX
      (subspaceDivisorSetupOfIsGood D sX hX) M hM W
  let div := fun (M : Modules.{u, u} D.site D.base D.base_mem X hX.1) hM =>
    canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      W.isIntegralSpace _ (isInvertibleModule_integralClosedSubspaceRestrict D sX hX M hM W)
      (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) M hM W)
      (hreg M hM) hn
  have hrule : ∀ (M : Modules.{u, u} D.site D.base D.base_mem X hX.1) hM,
      canonicalFirstChernRule D sX hX M hM (k + 1) W hW = div M hM := fun _ _ => rfl
  rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX (k + 1) _ hW,
    firstChernComponentCycle_of_deltaDimension_eq D sX hX (k + 1) _ hW, hrule N hN, hrule L hL]
  have h := ((isRationallyEquivalentToZeroWithin_firstChernCapCycleMap_pushforward_sub D sX hX W
      L hL (div N hN)).sub
    (isRationallyEquivalentToZeroWithin_firstChernCapCycleMap_pushforward_sub D sX hX W
      N hN (div L hL)) neg_mem_canonicalPrincipalDivisors).sub
    (isRationallyEquivalentToZeroWithin_pushforward_firstChernCapCycleMap_divisor_sub D sX hX W L
      hL N hN _ (hreg L hL) _ (hreg N hN) hn) neg_mem_canonicalPrincipalDivisors
  rw [map_sub] at h
  convert h using 1
  abel

/-- **Stacks 0EQZ: the two iterated cap products with first Chern classes commute.** In
Situation 0EDT let `X/B` be good and let `ℒ`, `𝒩` be invertible `𝒪_X`-modules. For every
`(k + 2)`-cycle `α` on `X`,

`c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α` in `CH_k(X)`.

The cap products are those of Stacks 0EQJ at the canonical choices
(`AlgebraicGeometry.Space.canonicalFirstChernRule`): the inner one is the cycle-level operation
`Z_{k+2}(X) → Z_{k+1}(X)` defining `c₁(-) ∩ -` on representatives, and so is the outer one
`Z_{k+1}(X) → Z_k(X)`, the class being taken afterwards in the Chow group `CH_k(X)` of
Stacks 0EQ6, `AlgebraicGeometry.Space.chowGroupCanonical`, whose rational equivalences are sums of
principal divisors at the canonical embeddings of Stacks 0ENK. As every class of `CH_{k+2}(X)` is
the class of a cycle, this is the identity of the source on representatives. -/
@[stacks 0EQZ "c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α in CH_k(X), for every (k+2)-cycle α on X \
representing a class of CH_{k+2}(X); both cap products are the cycle-level operations of Stacks \
0EQJ at the canonical choices, the classes taken in the Chow group of Stacks 0EQ6 at the canonical \
embeddings of Stacks 0ENK (chowGroupCanonical); nothing carried"]
theorem chowClassCanonical_firstChernCapCycleMap_firstChernCapCycleMap_comm (k : ℤ)
    (α : CycleGroup D sX (k + 1 + 1)) :
    chowClassCanonical.{max (u + 1) v} D sX hX k
        (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX L hL k)
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            α)) =
      chowClassCanonical.{max (u + 1) v} D sX hX k
        (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX L hL (k + 1))
            α)) := by
  classical
  have h := isRationallyEquivalentToZeroCanonical_finsum_of_canonicallyWithin.{u, max (u + 1) v,
      u + 1} D sX hX k
    (fun W => if α.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem X))
      else subspacePointSet D.site D.base D.base_mem X W.subspace) α.2.1
    (fun W => α.1 W •
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX L hL k)
          (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            W) -
        firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
          (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX L hL (k + 1))
            W)))
    (fun W => by
      by_cases hW : α.1 W = 0
      · simp only [hW, ite_true, zero_smul]
        exact isCycleFamilySumWithin_zero D sX hX k _
      · simp only [hW, ite_false]
        exact
          (isRationallyEquivalentToZeroWithin_firstChernCapCycleMap_firstChernComponentCycle_comm
            D sX hX L hL N hN W (α.2.2 W hW)).zsmul neg_mem_canonicalPrincipalDivisors _)
    (α := firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX L hL k)
        (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1)) α) -
      firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)
        (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX L hL (k + 1)) α))
    (fun Z => by
      rw [firstChernCapCycleMap_comm_sub_apply]
      refine finsum_congr fun W => ?_
      rw [AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul])
  rwa [← sub_eq_zero, ← map_sub, chowClassCanonical_eq_zero_iff]

/-- Stacks 0EQZ in the Chow group `AlgebraicGeometry.Space.chowGroup`, whose rational
equivalences quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially: the image of
`AlgebraicGeometry.Space.chowClassCanonical_firstChernCapCycleMap_firstChernCapCycleMap_comm`
under the comparison map `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`. -/
theorem canonicalFirstChernCap_firstChernCapCycleMap_comm (k : ℤ)
    (α : CycleGroup D sX (k + 1 + 1)) :
    canonicalFirstChernCap.{u, max (u + 1) v} D sX hX L hL k
        (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
          α) =
      canonicalFirstChernCap.{u, max (u + 1) v} D sX hX N hN k
        (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX L hL (k + 1))
          α) :=
  congrArg (chowGroupCanonicalToChowGroup.{max (u + 1) v} D sX hX k)
    (chowClassCanonical_firstChernCapCycleMap_firstChernCapCycleMap_comm D sX hX L hL N hN k α)

end Commutativity

end AlgebraicGeometry.Space

end
