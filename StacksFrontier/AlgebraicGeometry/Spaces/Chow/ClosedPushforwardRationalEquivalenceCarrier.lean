module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence

/-!
# The presenting family of a pushed-forward rational equivalence is carried by the subspace

In Situation 0EDT let `X/B` be good, let `Y ⊆ X` be a closed subspace with inclusion
`i : Y ⟶ X`, and let `β ∈ Z_k(Y)` be rationally equivalent to zero. Then `i_*β` is rationally
equivalent to zero
(`AlgebraicGeometry.Space.isRationallyEquivalentToZero_cycleGroupClosedPushforward`), presented
by a family `{U_l ⊆ X}` with

`|U_l| ⊆ |Y|`   for every `l`.

The members are the integral closed subspaces of `X` on the closures of the images of the
members on `Y` (`AlgebraicGeometry.Space.closureSubspace`), whose point sets are those images
by `AlgebraicGeometry.Space.subspacePointSet_closureSubspace_ι`.

## Main results

* `Space.exists_cycleFamilySum_subset_of_isRationallyEquivalentToZero_closedPushforward`: the
  pushforward along the inclusion of a closed subspace of a cycle rationally equivalent to zero
  is a locally finite sum of pushed-forward principal divisors over integral closed subspaces of
  `X` whose point sets lie in `|Y|`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

include hY in
/-- **The family presenting a pushed-forward rational equivalence lies in the subspace pushed
from.**  For `Y ⊆ X` a closed subspace of a good algebraic space and `β ∈ Z_k(Y)` rationally
equivalent to zero, the pushforward `i_*β ∈ Z_k(X)` is the sum of Stacks 0EQ6, part (1), over a
locally finite family `{U_l ⊆ X}` of integral closed subspaces of δ-dimension `k + 1` with

`|U_l| ⊆ |Y|`,

the summands being principal divisors. -/
theorem exists_cycleFamilySum_subset_of_isRationallyEquivalentToZero_closedPushforward (k : ℤ)
    {β : CycleGroup D (Y.ι ≫ sX) k}
    (hβ : IsRationallyEquivalentToZero.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β) :
    ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hUfin : LocallyFinite fun l : K =>
        subspacePointSet D.site D.base D.base_mem X (U l).subspace)
      (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
      (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
          subspacePointSet D.site D.base D.base_mem X Y) ∧
        (∀ l, deltaDimension D sX (U l) = k + 1) ∧
          (∀ l, IsPrincipalDivisorCycle D ((U l).subspace.ι ≫ sX) k (e l)) ∧
            cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX
                hX.2.2 (Y.ι ≫ sX) rfl k β =
              cycleFamilySum D sX hX U hUfin k e := by
  classical
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  obtain ⟨J, W, hWfin, c, hdim, hprin, rfl⟩ := hβ
  have himm : IsImmersion D.site D.base D.base_mem Y.ι :=
    isImmersion_of_isClosedImmersion D.site D.base D.base_mem hY.2
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    hY.2
  have hpts := fun n => subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)
  choose m hm using fun n => IntegralClosedSubspace.exists_hom_closureImage D.site D.base
    D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) Y.ι (W n)
  have hmopen : ∀ n, IsOpenImmersion D.site D.base D.base_mem (m n) := fun n =>
    have := isIso_of_comp_ι_eq_of_subspacePointSet D sX hX Y hY (W n) _ (hpts n) (m n) (hm n)
    isOpenImmersion_of_isIso D.site D.base D.base_mem (m n)
  choose c' hprin' hcc using fun n =>
    exists_isPrincipalDivisorCycle_closureImage D sX hX (Y.ι ≫ sX) hYgood himm rfl k (W n) (c n)
      (m n) (hmopen n) (hdim n) (hprin n)
  have hW'fin : LocallyFinite fun n => subspacePointSet D.site D.base D.base_mem X
      (closureSubspace D sX hX Y.ι (W n)).subspace :=
    locallyFinite_of_isClosedEmbedding_extend hemb (e := id)
      (fun w hw => absurd rfl (hw w)) (fun n => (hpts n).subset) hWfin
  have hdim' : ∀ n, deltaDimension D sX (closureSubspace D sX hX Y.ι (W n)) = k + 1 := fun n =>
    (IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) himm (W n)).trans (hdim n)
  have hsub : ∀ n, subspacePointSet D.site D.base D.base_mem X
      (closureSubspace D sX hX Y.ι (W n)).subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Y := fun n =>
    (hpts n).subset.trans (Set.image_subset_range _ _)
  refine ⟨J, fun n => closureSubspace D sX hX Y.ι (W n), hW'fin, c', hsub, hdim', hprin', ?_⟩
  refine Subtype.ext (funext fun T => ?_)
  rw [cycleFamilySum_apply]
  have hterm := fun n => congrArg (fun e : CycleGroup D sX k => e.1 T)
    (cycleGroupClosedPushforward_integralClosedSubspacePushforward D sX hX Y hY k (W n) (hm n)
      (c n) (c' n) (hcc n))
  rw [← finsum_congr hterm]
  change cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
      (cycleFamilySum D (Y.ι ≫ sX) hYgood W hWfin k c).1 T = _
  by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T
  · obtain ⟨T0, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
    refine finsum_congr fun n => ?_
    change _ = cycleClosedPushforward D hX.1 hY.1 _ hY.2 _ _
    rw [cycleClosedPushforward_apply_pushforward]
  · push Not at hT
    rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T hT]
    exact (finsum_eq_zero_of_forall_eq_zero fun n =>
      cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T hT).symm

end AlgebraicGeometry.Space

end
