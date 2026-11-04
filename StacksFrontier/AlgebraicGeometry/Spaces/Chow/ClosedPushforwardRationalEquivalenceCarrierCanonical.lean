module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical

/-!
# The presenting family of a pushed-forward rational equivalence at the canonical embeddings

In Situation 0EDT let `X/B` be good, let `Y ⊆ X` be a closed subspace with inclusion
`i : Y ⟶ X`, and let `β ∈ Z_k(Y)` be rationally equivalent to zero **at the canonical
embeddings** `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK, that is, in the sense of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`.  Then `i_*β` is a locally finite
sum of principal divisors, again at the canonical embeddings, over integral closed subspaces of
`X` whose point sets lie in `|Y|`.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrier` proves
the same over `AlgebraicGeometry.Space.IsPrincipalDivisorCycle`, where the family of embeddings
is quantified existentially.

## Main results

* `exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward`:
  the pushforward along the inclusion of a closed subspace of a cycle rationally equivalent to
  zero at the canonical embeddings is a locally finite sum of pushed-forward principal divisors,
  at the canonical embeddings, over integral closed subspaces of `X` whose point sets lie in
  `|Y|`.

## Implementation notes

The proof is that of the coarse statement with one block replaced.  There the summand on the
closure `W'` of the image of a member `W` of the presenting family is produced by
`AlgebraicGeometry.Space.exists_isPrincipalDivisorCycle_closureImage`, which quantifies the
family of embeddings on `W'` and so cannot deliver the canonical reading.  Here the summand is
instead the pushforward of the summand on `W` along the comparison morphism
`m : W ⟶ W'`, which that proof already shows to be an *isomorphism*
(`AlgebraicGeometry.Space.isIso_of_comp_ι_eq_of_subspacePointSet`), so
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso`
applies and gives the canonical reading directly.  The coefficient compatibility
`AlgebraicGeometry.Space.cycleGroupClosedPushforward_integralClosedSubspacePushforward` asks for
is then
`AlgebraicGeometry.Space.cycleClosedPushforward_apply_pushforward`, the two indexings being
identified by `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_eq_pushforward`
(`closureImage` along a closed immersion is `pushforward`, an isomorphism being one).

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
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
/-- **The family presenting a pushed-forward rational equivalence at the canonical embeddings
lies in the subspace pushed from.**  For `Y ⊆ X` a closed subspace of a good algebraic space and
`β ∈ Z_k(Y)` rationally equivalent to zero at the canonical embeddings of Stacks 0ENK, the
pushforward `i_*β ∈ Z_k(X)` is the sum of Stacks 0EQ6, part (1), over a locally finite family
`{U_l ⊆ X}` of integral closed subspaces of δ-dimension `k + 1` with

`|U_l| ⊆ |Y|`,

the summands being principal divisors **at the canonical embeddings**.

This is `exists_cycleFamilySum_subset_of_isRationallyEquivalentToZero_closedPushforward` with both
readings of `div(f)` replaced by the canonical one. -/
theorem exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward
    (k : ℤ) {β : CycleGroup D (Y.ι ≫ sX) k}
    (hβ : IsRationallyEquivalentToZeroCanonical.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β) :
    ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hUfin : LocallyFinite fun l : K =>
        subspacePointSet D.site D.base D.base_mem X (U l).subspace)
      (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ sX) k),
      (∀ l, subspacePointSet D.site D.base D.base_mem X (U l).subspace ⊆
          subspacePointSet D.site D.base D.base_mem X Y) ∧
        (∀ l, deltaDimension D sX (U l) = k + 1) ∧
          (∀ l, IsPrincipalDivisorCycleOfGood D ((U l).subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX (U l)) (U l).isIntegralSpace k (e l)) ∧
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
  choose m hm using fun n => IntegralClosedSubspace.exists_hom_closureImage D.site D.base
    D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) Y.ι (W n)
  have hmiso : ∀ n, IsIso (m n) := fun n =>
    isIso_of_comp_ι_eq_of_subspacePointSet D sX hX Y hY (W n) _
      (subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)) (m n) (hm n)
  have hW'good : ∀ n, D.IsGood ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) := fun n =>
    isGood_integralClosedSubspace D sX hX (closureSubspace D sX hX Y.ι (W n))
  have hcomp : ∀ n, (asIso (m n)).hom ≫
      ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) =
      (W n).subspace.ι ≫ Y.ι ≫ sX := fun n => by
    rw [asIso_hom, ← Category.assoc, hm n, Category.assoc]
  let e : ∀ n, CycleGroup D ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) k := fun n =>
    cycleGroupClosedPushforward D (closureSubspace D sX hX Y.ι (W n)).isClosedSubspace.1
      (W n).isClosedSubspace.1
      (isDecentSpace_of_isGood D ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX)
        (hW'good n))
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (asIso (m n)).hom)
      ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) (hW'good n).2.2
      ((W n).subspace.ι ≫ Y.ι ≫ sX) (hcomp n) k (c n)
  refine ⟨J, fun n => closureSubspace D sX hX Y.ι (W n), ?_, e,
    ?_, ?_, ?_, ?_⟩
  · exact locallyFinite_of_isClosedEmbedding_extend hemb (e := id)
      (fun w hw => absurd rfl (hw w))
      (fun n => (subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)).subset) hWfin
  · exact fun n => (subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)).subset.trans
      (Set.image_subset_range _ _)
  · intro n
    rw [IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) himm (W n)]
    exact hdim n
  · exact fun n => isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D
      ((W n).subspace.ι ≫ Y.ι ≫ sX)
      (isGood_integralClosedSubspace D (Y.ι ≫ sX) hYgood (W n))
      ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) (hW'good n)
      (W n).isIntegralSpace (closureSubspace D sX hX Y.ι (W n)).isIntegralSpace
      (asIso (m n)) (hcomp n) k (hprin n)
  · have hcc : ∀ (n : J) (V : IntegralClosedSubspace D.site D.base D.base_mem
        (W n).subspace.toFunctor),
        (e n).1
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
            (closureSubspace D sX hX Y.ι (W n)).isClosedSubspace.1
            (closureSubspace D sX hX Y.ι (W n)).isIntegralSpace.2.1 (m n) V) = (c n).1 V := by
      intro n V
      rw [IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem
        (closureSubspace D sX hX Y.ι (W n)).isClosedSubspace.1 (W n).isClosedSubspace.1
        (closureSubspace D sX hX Y.ι (W n)).isIntegralSpace.2.1
        (isClosedImmersion_of_isIso D.site D.base D.base_mem (m n)) V]
      exact cycleClosedPushforward_apply_pushforward D _ _ _ _ (c n).1 V
    refine Subtype.ext (funext fun T => ?_)
    rw [cycleFamilySum_apply]
    have hterm := fun n => congrArg (fun e : CycleGroup D sX k => e.1 T)
      (cycleGroupClosedPushforward_integralClosedSubspacePushforward D sX hX Y hY k (W n) (hm n)
        (c n) _ (hcc n))
    rw [← finsum_congr hterm]
    show cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
        (cycleFamilySum D (Y.ι ≫ sX) hYgood W hWfin k c).1 T = _
    by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T0 = T
    · obtain ⟨T0, rfl⟩ := hT
      rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
      refine finsum_congr fun n => ?_
      show _ = cycleClosedPushforward D hX.1 hY.1 _ hY.2 _ _
      rw [cycleClosedPushforward_apply_pushforward]
    · have hne := fun γ => cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 γ T
        fun T0 hT0 => hT ⟨T0, hT0⟩
      rw [hne]
      exact (finsum_eq_zero_of_forall_eq_zero fun n => hne _).symm

end AlgebraicGeometry.Space

end
