module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrierCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical

/-!
# A rational equivalence carried by a closed subspace descends to it, at the canonical embeddings

In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a closed subspace and
let `β ∈ Z_k(Y)`. This file proves

`i_*β ∼_rat 0 within |Y|`  if and only if  `β ∼_rat 0`,

where rational equivalence is taken at the canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of
Stacks 0ENK on the summands (`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical` and
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical`), and "within `|Y|`" means
that the family of integral closed subspaces presenting the rational equivalence lies in `|Y|`.

## Main results

* `exists_isPrincipalDivisorCycleOfGood_cycleClosedPushforward_pushforward`: a principal divisor
  at the canonical embeddings on the image in `X` of an integral closed subspace `V ⊆ Y` comes
  from one on `V` with the same pushforward to `X`.
* `isRationallyEquivalentToZeroWithinCanonical_cycleGroupClosedPushforward`: if `β ∼_rat 0` at
  the canonical embeddings, then `i_*β ∼_rat 0` within `|Y|` at the canonical embeddings.
* `isRationallyEquivalentToZeroCanonical_of_withinCanonical_cycleGroupClosedPushforward`:
  if `i_*β ∼_rat 0` within `|Y|` at the canonical embeddings, then `β ∼_rat 0` at the canonical
  embeddings.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Descent

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

include hY in
/-- For `Y ⊆ X` a closed subspace of a good algebraic space, `V ⊆ Y` an integral closed subspace
and `c ∈ Z_k(i(V))` a principal divisor at the canonical embeddings of Stacks 0ENK on the image
`i(V)` of `V` in `X`, there is a principal divisor `c'` at the canonical embeddings on `V` whose
pushforward to `X` through `Y` is the pushforward of `c`. -/
theorem exists_isPrincipalDivisorCycleOfGood_cycleClosedPushforward_pushforward (k : ℤ)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (c : CycleGroup D ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX) k)
    (hc : IsPrincipalDivisorCycleOfGood D
      ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 V))
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).isIntegralSpace k c) :
    ∃ c' : CycleGroup D (V.subspace.ι ≫ Y.ι ≫ sX) k,
      IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ Y.ι ≫ sX)
          (isGood_integralClosedSubspace D (Y.ι ≫ sX)
            (isGood_ι_of_isClosedSubspace D sX hX Y hY) V) V.isIntegralSpace k c' ∧
        cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
            (integralClosedSubspacePushforward D (Y.ι ≫ sX)
              (isGood_ι_of_isClosedSubspace D sX hX Y hY) V k c').1 =
          (integralClosedSubspacePushforward D sX hX
            (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
              (D.isDecentSpace_of_isGood sX hX) hY.2 V) k c).1 := by
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hVg : D.IsGood (V.subspace.ι ≫ Y.ι ≫ sX) :=
    isGood_integralClosedSubspace D (Y.ι ≫ sX) hYgood V
  have hV'g : D.IsGood ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX) :=
    isGood_integralClosedSubspace D sX hX _
  have hcomp : (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).symm.hom ≫ (V.subspace.ι ≫ Y.ι ≫ sX) =
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).subspace.ι ≫ sX := by
    rw [Iso.symm_hom, show V.subspace.ι ≫ Y.ι ≫ sX = (V.subspace.ι ≫ Y.ι) ≫ sX from
        (Category.assoc _ _ _).symm, ← Category.assoc,
      IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp]
  have hiso := isClosedImmersion_of_isIso D.site D.base D.base_mem
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V).symm.hom
  refine ⟨cycleGroupClosedPushforward D hVg.1 hV'g.1 (isDecentSpace_of_isGood D _ hVg) hiso
      _ hVg.2.2 _ hcomp k c,
    isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D _ hV'g _ hVg
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V).isIntegralSpace V.isIntegralSpace _ hcomp k hc,
    ?_⟩
  refine Eq.trans (cycleClosedPushforward_comp D hX.1 hY.1 V.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood (Y.ι ≫ sX) hYgood)
    V.isClosedSubspace.2 hY.2 _).symm ?_
  refine Eq.trans (cycleClosedPushforward_comp D hX.1 V.isClosedSubspace.1
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V).isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) (isDecentSpace_of_isGood D _ hVg) hiso
    (isClosedImmersion_comp D.site D.base D.base_mem V.subspace.ι Y.ι
      V.isClosedSubspace.2 hY.2) c.1).symm ?_
  exact cycleClosedPushforward_congr D hX.1
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V).isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) _ _
    (IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 V) c.1

include hY in
/-- For `Y ⊆ X` a closed subspace of a good algebraic space and `β ∈ Z_k(Y)` rationally
equivalent to zero at the canonical embeddings of Stacks 0ENK, the pushforward `i_*β ∈ Z_k(X)` is
rationally equivalent to zero at the canonical embeddings within `|Y|`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_cycleGroupClosedPushforward (k : ℤ)
    {β : CycleGroup D (Y.ι ≫ sX) k}
    (hβ : IsRationallyEquivalentToZeroCanonical.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k β)
      (subspacePointSet D.site D.base D.base_mem X Y) :=
  exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward.{v}
    D sX hX Y hY k hβ

include hY in
/-- In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a closed subspace
and let `β ∈ Z_k(Y)`. If the pushforward `i_*β` is rationally equivalent to zero on `X` at the
canonical embeddings of Stacks 0ENK within `|Y|`, that is, with a presenting family of integral
closed subspaces inside `|Y|`, then `β` is rationally equivalent to zero on `Y` at the canonical
embeddings. -/
theorem isRationallyEquivalentToZeroCanonical_of_withinCanonical_cycleGroupClosedPushforward
    (k : ℤ) {β : CycleGroup D (Y.ι ≫ sX) k}
    (hβ : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k β)
      (subspacePointSet D.site D.base D.base_mem X Y)) :
    IsRationallyEquivalentToZeroCanonical.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β := by
  classical
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1 hY.2
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := hβ
  have hex : ∀ j, ∃ V : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 V = W j := fun j =>
    IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood (Y.ι ≫ sX) hYgood) hY.2
      (W j) (hsub j)
  choose V hV using hex
  have hWeq : (fun j => IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)) = W := funext hV
  subst hWeq
  have hVfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y.toFunctor (V j).subspace := by
    have hpre : ∀ j, subspacePointSet D.site D.base D.base_mem Y.toFunctor (V j).subspace =
        pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X
            (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
              (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)).subspace := fun j => by
      rw [IntegralClosedSubspace.subspacePointSet_pushforward,
        Set.preimage_image_eq _ hemb.injective]
    exact (hWfin.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem Y.ι)).subset
      fun j => (hpre j).subset
  have hdim' : ∀ j, deltaDimension D (Y.ι ≫ sX) (V j) = k + 1 := fun j =>
    (IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)).symm.trans (hdim j)
  choose c' hprin' hpush using fun j =>
    exists_isPrincipalDivisorCycleOfGood_cycleClosedPushforward_pushforward D sX hX Y hY k (V j)
      (c j) (hprin j)
  refine ⟨J, V, hVfin, c', hdim', hprin', ?_⟩
  refine injective_cycleGroupClosedPushforward D hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2 (Y.ι ≫ sX) rfl k ?_
  rw [hsum]
  refine Subtype.ext (funext fun T => ?_)
  rw [cycleFamilySum_apply]
  have hterm : ∀ j : J, (integralClosedSubspacePushforward D sX hX
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
          (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)) k (c j)).1 T =
      cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
        (integralClosedSubspacePushforward D (Y.ι ≫ sX) hYgood (V j) k (c' j)).1 T := fun j =>
    (congrFun (hpush j) T).symm
  rw [finsum_congr hterm]
  change _ = cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
    (cycleFamilySum D (Y.ι ≫ sX) hYgood V hVfin k c').1 T
  by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T
  · obtain ⟨T0, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
    exact finsum_congr fun j => by rw [cycleClosedPushforward_apply_pushforward]
  · push Not at hT
    rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T hT]
    exact finsum_eq_zero_of_forall_eq_zero fun j =>
      cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T hT

end Descent

end AlgebraicGeometry.Space

end
