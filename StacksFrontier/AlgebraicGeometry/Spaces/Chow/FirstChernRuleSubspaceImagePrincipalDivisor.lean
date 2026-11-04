module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceRestrictIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodIsoTransport

/-!
# Capping on a subspace and capping on its image differ by a principal divisor

In Situation 0EDT let `X/B` be good, let `𝒩` be an invertible `𝒪_X`-module, let
`V ⊆ X` be an integral closed subspace and let `T₀ ⊆ V` be an integral closed subspace of `V`
whose image `i_V(T₀) ⊆ X` (`AlgebraicGeometry.Space.integralClosedSubspaceImage`) has
δ-dimension `k + 1`.  There are then two component cycles of Stacks 0EQJ attached to `T₀`:

* `c₁(𝒩|_{i_V(T₀)}) ∩ [i_V(T₀)]`, formed on `X` for `𝒩`, and
* `c₁((𝒩|_V)|_{T₀}) ∩ [T₀]`, formed on `V` for `𝒩|_V` and carried to `i_V(T₀)` along the
  identification `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso` of `T₀` with its
  image.

They need not be equal: each is the Weil divisor of Stacks 0EQE of a regular meromorphic section
chosen **independently** on the two spaces by
`AlgebraicGeometry.Space.componentMeromorphicSection`.  This file proves that every integer
multiple of their difference is a principal divisor on `i_V(T₀)` in the canonical reading of
part (1) of Stacks 0EQ6, which is Stacks 0EPT once both cycles are read on one space.

## Main results

* `deltaDimension_integralClosedSubspaceImage`: the δ-dimension of the image of `T₀` in `X` is
  the δ-dimension of `T₀` over the base.
* `subspacePointSet_integralClosedSubspaceImage_subset`: the point set of the image of `T₀` lies
  in that of `V`.
* `locallyFinite_subspacePointSet_integralClosedSubspaceImage`: the images in `X` of a locally
  finite family of integral closed subspaces of `V` form a locally finite family.
* `isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_pushforwardCycleTransport`:
  the difference above is a principal divisor at the canonical embeddings of Stacks 0ENK.
* `integralClosedSubspacePushforward_zsmul_canonicalFirstChernRule_sub`: pushed forward to `X`,
  that multiple is the same multiple of the difference of the component cycles of Stacks 0EQJ on
  `X` and on `V`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T₀ : IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor)

/-- The δ-dimension of the image of `T₀ ⊆ V` in `X`, measured along `X → B`, is the δ-dimension of
`T₀`, measured along `T₀ → V → B`. -/
theorem deltaDimension_integralClosedSubspaceImage :
    deltaDimension D sX (integralClosedSubspaceImage D sX hX V T₀) =
      deltaDimension D (V.subspace.ι ≫ sX) T₀ :=
  IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 V.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) V.isClosedSubspace.2 T₀

/-- The point set of the image of `T₀ ⊆ V` in `X` lies in the point set of `V`. -/
theorem subspacePointSet_integralClosedSubspaceImage_subset :
    subspacePointSet D.site D.base D.base_mem X
        (integralClosedSubspaceImage D sX hX V T₀).subspace ⊆
      subspacePointSet D.site D.base D.base_mem X V.subspace :=
  (IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem hX.1
    V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) V.isClosedSubspace.2
    T₀).subset.trans (Set.image_subset_range _ _)

/-- The images in `X` of a locally finite family of integral closed subspaces of `V` form a
locally finite family of integral closed subspaces of `X`. -/
theorem locallyFinite_subspacePointSet_integralClosedSubspaceImage {J : Type*}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem V.subspace.toFunctor)
    (hW : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem V.subspace.toFunctor (W j).subspace) :
    LocallyFinite fun j : J => subspacePointSet D.site D.base D.base_mem X
      (integralClosedSubspaceImage D sX hX V (W j)).subspace :=
  locallyFinite_of_isClosedEmbedding_extend
    (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
      V.isClosedSubspace.2)
    (e := id) (fun w hw => absurd rfl (hw w))
    (fun j => (IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem hX.1
      V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) V.isClosedSubspace.2 (W j)).subset)
    hW

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ)

/-- For `V ⊆ X` an integral closed subspace of a good `X/B`, `𝒩` an invertible `𝒪_X`-module,
`T₀ ⊆ V` an integral closed subspace of `V` whose image `i_V(T₀) ⊆ X` has δ-dimension `k + 1`,
and `a : ℤ`, the cycle

`a · (c₁(𝒩|_{i_V(T₀)}) ∩ [i_V(T₀)] - (T₀ ≅ i_V(T₀))_*(c₁((𝒩|_V)|_{T₀}) ∩ [T₀]))`

is a principal divisor on `i_V(T₀)` in the canonical reading of part (1) of Stacks 0EQ6, the
component cycles being those of `AlgebraicGeometry.Space.canonicalFirstChernRule` on `X` and on
`V` respectively. -/
theorem isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_pushforwardCycleTransport
    (hT : deltaDimension D sX (integralClosedSubspaceImage D sX hX V T₀) = k + 1) (a : ℤ) :
    IsPrincipalDivisorCycleOfGood D
        ((integralClosedSubspaceImage D sX hX V T₀).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX (integralClosedSubspaceImage D sX hX V T₀))
        (integralClosedSubspaceImage D sX hX V T₀).isIntegralSpace k
      (a • (canonicalFirstChernRule D sX hX N hN k
              (integralClosedSubspaceImage D sX hX V T₀) hT -
            IntegralClosedSubspace.pushforwardCycleTransport D sX hX V.isClosedSubspace.1
                V.isClosedSubspace.2 T₀ k
              (canonicalFirstChernRule D (V.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX V)
                (integralClosedSubspaceRestrict D sX hX N V)
                (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) k T₀
                ((deltaDimension_integralClosedSubspaceImage D sX hX V T₀).symm.trans hT)))) := by
  have hT₀ : deltaDimension D (V.subspace.ι ≫ sX) T₀ = k + 1 :=
    (deltaDimension_integralClosedSubspaceImage D sX hX V T₀).symm.trans hT
  have hσreg := isRegularMeromorphicSection_componentMeromorphicSection
    (V.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX V)
    (subspaceDivisorSetupOfIsGood D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V))
    (integralClosedSubspaceRestrict D sX hX N V)
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) T₀
  have hσ'reg := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem
    T₀.subspace.toFunctor T₀.isClosedSubspace.1
    (integralClosedSubspaceRestrictPushforwardIso D sX hX V T₀ N) _ hσreg
  have hτreg := isRegularMeromorphicSection_componentMeromorphicSection sX hX
    (subspaceDivisorSetupOfIsGood D sX hX) N hN (integralClosedSubspaceImage D sX hX V T₀)
  have hτ'reg := isRegularMeromorphicSection_pullbackMeromorphicSection_algebraicSpacesIsoOfIso
    D.site D.base D.base_mem T₀.isClosedSubspace.1
    (integralClosedSubspaceImage D sX hX V T₀).isClosedSubspace.1
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 V.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) V.isClosedSubspace.2 T₀)
    (integralClosedSubspaceRestrict D sX hX N (integralClosedSubspaceImage D sX hX V T₀))
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN
      (integralClosedSubspaceImage D sX hX V T₀))
    _ hτreg
  have hkT : deltaDimensionClosed D ((integralClosedSubspaceImage D sX hX V T₀).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (integralClosedSubspaceImage D sX hX V T₀))
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX
      (integralClosedSubspaceImage D sX hX V T₀), hT]
  have hkT₀ : deltaDimensionClosed D (T₀.subspace.ι ≫ V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D (V.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX V) T₀)
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V) T₀, hT₀]
  have hpush := canonicalDivisorCycleAt_pushforwardOfIso D
    (T₀.subspace.ι ≫ V.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V) T₀)
    ((integralClosedSubspaceImage D sX hX V T₀).subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX (integralClosedSubspaceImage D sX hX V T₀))
    T₀.isIntegralSpace (integralClosedSubspaceImage D sX hX V T₀).isIntegralSpace
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 V.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) V.isClosedSubspace.2 T₀)
    (integralClosedSubspaceRestrict D sX hX N (integralClosedSubspaceImage D sX hX V T₀))
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN
      (integralClosedSubspaceImage D sX hX V T₀))
    (componentMeromorphicSection sX hX (subspaceDivisorSetupOfIsGood D sX hX) N hN
      (integralClosedSubspaceImage D sX hX V T₀))
    hτreg
    (by rw [← Category.assoc, IntegralClosedSubspace.pushforwardIso_hom_comp_ι, Category.assoc])
    hkT₀ hkT
  have hM' := isInvertibleModule_modulePullback_algebraicSpacesIsoOfIso D.site D.base D.base_mem
    T₀.isClosedSubspace.1 (integralClosedSubspaceImage D sX hX V T₀).isClosedSubspace.1
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 V.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) V.isClosedSubspace.2 T₀)
    (integralClosedSubspaceRestrict D sX hX N (integralClosedSubspaceImage D sX hX V T₀))
    (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN
      (integralClosedSubspaceImage D sX hX V T₀))
  have hcarry := canonicalDivisorCycleAt_sectionsMap_iso D
    (T₀.subspace.ι ≫ V.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V) T₀)
    T₀.isIntegralSpace
    (integralClosedSubspaceRestrict D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V)
      (integralClosedSubspaceRestrict D sX hX N V) T₀)
    _
    (isInvertibleModule_integralClosedSubspaceRestrict D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V)
      (integralClosedSubspaceRestrict D sX hX N V)
      (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) T₀)
    hM'
    (integralClosedSubspaceRestrictPushforwardIso D sX hX V T₀ N) _ hσreg hσ'reg hkT₀
  have hmain := isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D
    (T₀.subspace.ι ≫ V.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V) T₀)
    ((integralClosedSubspaceImage D sX hX V T₀).subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX (integralClosedSubspaceImage D sX hX V T₀))
    T₀.isIntegralSpace (integralClosedSubspaceImage D sX hX V T₀).isIntegralSpace
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 V.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) V.isClosedSubspace.2 T₀)
    (by rw [← Category.assoc, IntegralClosedSubspace.pushforwardIso_hom_comp_ι, Category.assoc])
    k
    (isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D
      (T₀.subspace.ι ≫ V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D (V.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX V) T₀)
      T₀.isIntegralSpace _ hM' _ _ hτ'reg hσ'reg hkT₀ a)
  rw [map_zsmul, map_sub, hpush] at hmain
  erw [hcarry] at hmain
  exact hmain

/-- For `T₀ ⊆ V` of δ-dimension `k + 1` and `a : ℤ`, the cycle of
`isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_pushforwardCycleTransport` pushed
forward from `i_V(T₀)` to `X` is

`a · (c₁(𝒩) ∩ [i_V(T₀)] - (i_V)_*(c₁(𝒩|_V) ∩ [T₀]))`,

both terms being the component cycles `AlgebraicGeometry.Space.firstChernComponentCycle` of
Stacks 0EQJ — on `X` at the image, and on `V` at `T₀` and then pushed to `X`. -/
theorem integralClosedSubspacePushforward_zsmul_canonicalFirstChernRule_sub
    (hT₀ : deltaDimension D (V.subspace.ι ≫ sX) T₀ = k + 1) (a : ℤ) :
    integralClosedSubspacePushforward D sX hX (integralClosedSubspaceImage D sX hX V T₀) k
        (a • (canonicalFirstChernRule D sX hX N hN k (integralClosedSubspaceImage D sX hX V T₀)
                ((deltaDimension_integralClosedSubspaceImage D sX hX V T₀).trans hT₀) -
              IntegralClosedSubspace.pushforwardCycleTransport D sX hX V.isClosedSubspace.1
                  V.isClosedSubspace.2 T₀ k
                (canonicalFirstChernRule D (V.subspace.ι ≫ sX)
                  (isGood_integralClosedSubspace D sX hX V)
                  (integralClosedSubspaceRestrict D sX hX N V)
                  (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) k T₀
                  hT₀))) =
      a • (firstChernComponentCycle D sX hX k (canonicalFirstChernRule D sX hX N hN k)
              (integralClosedSubspaceImage D sX hX V T₀) -
            integralClosedSubspacePushforward D sX hX V k
              (firstChernComponentCycle D (V.subspace.ι ≫ sX)
                (isGood_integralClosedSubspace D sX hX V) k
                (canonicalFirstChernRule D (V.subspace.ι ≫ sX)
                  (isGood_integralClosedSubspace D sX hX V)
                  (integralClosedSubspaceRestrict D sX hX N V)
                  (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) k) T₀)) := by
  rw [map_zsmul, map_sub,
    firstChernComponentCycle_of_deltaDimension_eq D sX hX k
      (canonicalFirstChernRule D sX hX N hN k)
      ((deltaDimension_integralClosedSubspaceImage D sX hX V T₀).trans hT₀),
    firstChernComponentCycle_of_deltaDimension_eq D (V.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V) k
      (canonicalFirstChernRule D (V.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX V)
        (integralClosedSubspaceRestrict D sX hX N V)
        (isInvertibleModule_integralClosedSubspaceRestrict D sX hX N hN V) k) hT₀,
    integralClosedSubspacePushforward_comp_pushforward D sX hX V T₀ k]

end AlgebraicGeometry.Space

end
