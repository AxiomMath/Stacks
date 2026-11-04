module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorCanonical

/-!
# Stacks 0EQT: proper pushforward and intersecting with an invertible sheaf

In Situation 0EDT let `X/B` and `Y/B` be good, let `p : X ⟶ Y` be a proper morphism over `B`,
let `ℒ` be an invertible `𝒪_Y`-module and let `α ∈ Z_{k+1}(X)`. Stacks 0EQT is the projection
formula

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`   in `CH_k(Y)`.

## Main results

* `chowClassCanonical_properPushforward_canonicalFirstChernCap_of_component`: the formula,
  from the source's final step at every integral closed subspace.

## References

* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Projection

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} (hX : D.IsGood sX) {sY : Y ⟶ D.space} (hY : D.IsGood sY)
    (q : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩)
    (hqB : q.hom ≫ sY = sX) (hq : IsProper D.site D.base D.base_mem q.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (k : ℤ)

/-- The component morphism `g : W ⟶ W'` of Stacks 0EEG, chosen once for each `W`. -/
noncomputable def chernComponentMap (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    W.subspace.toFunctor ⟶ (chernImage D hX hY q W).subspace.toFunctor :=
  (IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) q.hom W).choose

/-- The component morphism `g : W ⟶ W'` lies over `p`: `g ≫ ι_{W'} = ι_W ≫ p`. -/
theorem chernComponentMap_comp_ι (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    chernComponentMap D hX hY q W ≫ (chernImage D hX hY q W).subspace.ι = W.subspace.ι ≫ q.hom :=
  (IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) q.hom W).choose_spec

/-- **The component rule of the pulled-back sections.** On an integral closed subspace `W ⊆ X`
of δ-dimension `k + 1` it is the Weil divisor `div_{g^*(ℒ|_{W'})}(g^*t')` of Stacks 0EQE, where
`g : W ⟶ W'` is the component morphism of Stacks 0EEG and `t'` the section of `ℒ|_{W'}` chosen by
the canonical rule of Stacks 0EQJ on `Y`. It is a component rule for `c₁(p^*ℒ)`: on each `W` it
differs from the canonical one at `p^*ℒ` by a principal divisor
(`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_canonicalPullbackRule_sub`). -/
noncomputable def chernPulledRule : FirstChernComponentCycleRule D sX k := fun W hW =>
  canonicalDivisorCycleAt D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
    W.isIntegralSpace _
    (modulePullbackInvertible (chernComponentHom D hX hY q W (chernComponentMap D hX hY q W)) _
      (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL (chernImage D hX hY q W)))
    (chernPulledSection D hX hY q L hL W (chernComponentMap D hX hY q W)
      (chernComponentMap_comp_ι D hX hY q W))
    (isRegularMeromorphicSection_chernPulledSection D hX hY q L hL W
      (chernComponentMap D hX hY q W) (chernComponentMap_comp_ι D hX hY q W))
    (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hW])

/-- **The cap products with the canonical rule at `p^*ℒ` and with the rule of the pulled-back
sections have the same class in `CH_k(X)`**: on every `W` the two component cycles differ by a
principal divisor, so the two locally finite sums of Stacks 0EQ6 part (1) differ by a cycle
rationally equivalent to zero. -/
theorem chowClassCanonical_firstChernCapCycleMap_chernPulledRule (α : CycleGroup D sX (k + 1)) :
    chowClassCanonical.{u + 1} D sX hX k
        (firstChernCapCycleMap D sX hX k
          (canonicalFirstChernRule D sX hX ((modulePullback D.site D.base D.base_mem q).obj L)
            (modulePullbackInvertible q L hL) k) α) =
      chowClassCanonical.{u + 1} D sX hX k
        (firstChernCapCycleMap D sX hX k (chernPulledRule D hX hY q L hL k) α) := by
  let I := {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0}
  have hdim : ∀ i : I, deltaDimension D sX i.1 = k + 1 := fun i => α.2.2 i.1 i.2
  have hcover : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W ≠ 0 →
      ∃ i : I, i.1 = W := fun W hW => ⟨⟨W, hW⟩, rfl⟩
  have hsum := fun R => firstChernCapCycleMap_eq_cycleFamilySum D sX hX k R α Subtype.val
    Subtype.val_injective (locallyFinite_cycleSupport α) hdim hcover
  rw [hsum, hsum, ← sub_eq_zero, ← map_sub, ← cycleFamilySum_sub]
  refine chowClassCanonical_cycleFamilySum_eq_zero.{u + 1} D sX hX k Subtype.val
    (locallyFinite_cycleSupport α) _ hdim fun i => ?_
  have h := isPrincipalDivisorCycleOfGood_canonicalPullbackRule_sub D hX hY q L hL i.1
    (chernComponentMap D hX hY q i.1) (chernComponentMap_comp_ι D hX hY q i.1) k (hdim i)
    (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX i.1, hdim i]) (α.1 i.1)
  rwa [smul_sub] at h

/-- **The projection formula at the level of cycles, for the rule of the pulled-back sections.**
If Stacks 0EQS holds for the component morphism `g : W ⟶ W'` of every `W ⊆ X` of δ-dimension
`k + 1` with `dim_δ(W') = k + 1` (`hsec`), then

`p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α`   in `Z_k(Y)`,

`c₁(p^*ℒ)` being read through `AlgebraicGeometry.Space.chernPulledRule` and `c₁(ℒ)` through
the canonical rule of Stacks 0EQJ. This is the source's reduction to a single integral closed
subspace (`AlgebraicGeometry.Space.properPushforward_firstChernCapCycleMap_of_component`), the
square of Stacks 0EP2 (`properCyclePushforward_integralClosedSubspacePushforward_closureImage`)
and the source's final step (`subspaceProperCyclePushforward_chernPulledDivisor`). -/
theorem properCyclePushforward_firstChernCapCycleMap_chernPulledRule
    (α : CycleGroup D sX (k + 1)) :
    properCyclePushforward D sX hX sY hY hqB hq.2.1.2 k
        (firstChernCapCycleMap D sX hX k (chernPulledRule D hX hY q L hL k) α) =
      firstChernCapCycleMap D sY hY k (canonicalFirstChernRule D sY hY L hL k)
        (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 (k + 1) α) := by
  refine properPushforward_firstChernCapCycleMap_of_component D hX hY hqB hq k _ _
    (fun W => ?_) α
  have hg := chernComponentMap_comp_ι D hX hY q W
  have hgp := IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hX.1 hY.1 q.hom
    hq W _ (chernComponentMap D hX hY q W) hg
  rw [firstChernComponentCycle_eq_pushforward D sX hX k _ W,
    properCyclePushforward_integralClosedSubspacePushforward_closureImage D sX hX sY hY hqB hq W _
      (chernComponentMap D hX hY q W) hg k,
    firstChernComponentCycle_eq_pushforward D sY hY k _, ← map_zsmul]
  congr 1
  by_cases hW : deltaDimension D sX W = k + 1
  · rw [chernComponentCycleOrZero_of_deltaDimension_eq D sX k _ hW]
    exact subspaceProperCyclePushforward_chernPulledDivisor D hX hY q L hL W
      (chernComponentMap D hX hY q W) hg k hqB hq hW _ fun hk' =>
        properCyclePushforward_canonicalDivisorCycleAt_pullback D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) ((chernImage D hX hY q W).subspace.ι ≫ sY)
          (isGood_integralClosedSubspace D sY hY _) W.isIntegralSpace
          (chernImage D hX hY q W).isIntegralSpace _
          (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL (chernImage D hX hY q W))
          _ _ hgp (IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage D.site D.base
            D.base_mem hY.1 (D.isDecentSpace_of_isGood sY hY) q.hom W _ hg) _
          (isRegularMeromorphicSection_componentMeromorphicSection sY hY
            (subspaceDivisorSetupOfIsGood D sY hY) L hL (chernImage D hX hY q W)) _ hk'
  · rw [chernComponentCycleOrZero_of_deltaDimension_ne D sX k _ hW, map_zero]
    by_cases hdeg : properCycleDegree D sX hX sY hY q.hom W = 0
    · rw [hdeg, zero_smul]
    · have hdim := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY q.hom
        hdeg
      rw [chernComponentCycleOrZero_of_deltaDimension_ne D sY k _ (by rw [hdim]; exact hW),
        smul_zero]

/-- **Stacks 0EQT from Stacks 0EQS and Stacks 0EQC.** If Stacks 0EQS holds for the component
morphisms (`hsec`) and proper pushforward along `p` respects rational equivalence (`hrat`),
then `p_*(c₁(p^*ℒ) ∩ α) = c₁(ℒ) ∩ p_*α` in `CH_k(Y)`. -/
theorem chowClassCanonical_properPushforward_canonicalFirstChernCap_of_component
    (hrat : ∀ β : CycleGroup D sX k, IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX k β →
      IsRationallyEquivalentToZeroCanonical.{u + 1} D sY hY k
        (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 k β))
    (α : CycleGroup D sX (k + 1)) :
    chowClassCanonical.{u + 1} D sY hY k
        (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 k
          (firstChernCapCycleMap D sX hX k
            (canonicalFirstChernRule D sX hX ((modulePullback D.site D.base D.base_mem q).obj L)
              (modulePullbackInvertible q L hL) k) α)) =
      canonicalFirstChernCapCanonical.{u + 1} D sY hY L hL k
        (properCyclePushforward D sX hX sY hY hqB hq.2.1.2 (k + 1) α) := by
  unfold canonicalFirstChernCapCanonical
  rw [AddMonoidHom.comp_apply, ← properCyclePushforward_firstChernCapCycleMap_chernPulledRule D hX
    hY q hqB hq L hL k α, chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  have h := (chowClassCanonical_eq_iff_rationallyEquivalentCanonical.{u + 1} D sX hX k _ _).1
    (chowClassCanonical_firstChernCapCycleMap_chernPulledRule D hX hY q L hL k α)
  show IsRationallyEquivalentToZeroCanonical.{u + 1} D sY hY k (_ - _)
  rw [← map_sub]
  exact hrat _ h

end Projection

end AlgebraicGeometry.Space

end
