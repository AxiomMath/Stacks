module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChernRuleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoringCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCap

/-!
# The Gysin factoring assertion of Stacks 0ERA without Stacks 0ER5

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module with a global section
`σ` and let `i : E = Z(σ) → X` be the closed immersion of its vanishing locus — the effective
Cartier divisor `(ℒ, σ, i)` of Definition 0ER1, presented as the source presents it.  **Stacks
0ERA** asserts that the refined Gysin map `i^* : Z_{k+1}(X) ⟶ Z_k(E)` of Stacks 0ER1 factors
through rational equivalence.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoringCanonical` reduces that
assertion to one member `V ⊆ X` of the presenting family of a cycle rationally equivalent to
zero: it is enough that `i^*((i_V)_* d)` is rationally equivalent to zero on `E` *within*
`i^{-1}|V|`, for `d` a principal divisor cycle on `V` at the canonical embeddings of Stacks 0ENK.
This module discharges that from a statement **on `V` alone**, and in doing so removes Stacks
0ER5 from the inputs of Stacks 0ERA.

## Stacks 0ER5 is not needed

The source transports the member's presentation to `E` by Lemma 0ER5 — the compatibility
`i^* f_* = g_* (i')^*` of the Gysin map with proper pushforward — applied to the closed immersion
`i_V : V ⟶ X`.  It is not needed: both `i^*((i_V)_* d)` and the cycle the source compares it
with become the *same* cycle on `X` after pushing forward along `i`, by two identities that assume
nothing:

* `AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap`, which
  is `i_*(i^* α) = c₁(ℒ) ∩ α` in `Z_k(X)` at the component rule
  `AlgebraicGeometry.Space.restrictedSectionChernRule`;
* `AlgebraicGeometry.Space.cycleGroupClosedPushforward_firstChernCapCycleMap`, the projection
  formula of Stacks 0EQT **along a closed immersion**, which holds at the level of cycles with
  nothing carried once the component rule on `V` is the transported
  `AlgebraicGeometry.Space.closedSubspaceChernRule`.

So `i_*(i^*((i_V)_* d)) = (i_V)_*(c₁ ∩ d)` outright, and what has to be transported to `E` is not
a cycle identity but a *rational equivalence*: by
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_preimage_of_closedPushforward`
a rational equivalence on `X` carried by a subset of `|E|` descends to `E` and keeps its carrier.

## What is left

Exactly one statement, and it is a statement about the integral space `V`: that

`(i_V)_*(c₁ ∩ d)` is rationally equivalent to zero on `X` within `|E| ∩ |V|`

at the canonical embeddings, the cap product of Stacks 0EQJ being formed on `V` at the component
rule transported from `AlgebraicGeometry.Space.restrictedSectionChernRule`.  That is precisely the
content the source gets from Lemma 0ER9 in its case `E ≠ V` and from Lemma 0EQY in its case
`E = V`: both produce a rational equivalence *carried inside the divisor*, which is why the source
states them in a Chow group of the divisor rather than of the ambient space.  A rational
equivalence on `V` that is **not** carried by `|E| ∩ |V|` — which is all that Stacks 0EQY alone
gives, since `d` is a principal divisor cycle and so `c₁ ∩ d` is rationally equivalent to zero on
the whole of `V` — does not suffice, and that is the reason Stacks 0ER9 exists.

## Main results

* `isRationallyEquivalentToZeroWithinCanonical_image_cycleGroupClosedPushforward`:
  **the pushforward of a rational equivalence together with its carrier.**  If `β` is rationally
  equivalent to zero at the canonical embeddings within `T ⊆ |Y|`, then `i_*β` is rationally
  equivalent to zero at the canonical embeddings within `i(T)`.  This refines
  `isRationallyEquivalentToZeroWithinCanonical_cycleGroupClosedPushforward`,
  which is the case `T = |Y|`.
* `isRationallyEquivalentToZeroWithinCanonical_preimage_of_closedPushforward`:
  **the descent of a rational equivalence together with its carrier.**  If `i_*β` is rationally
  equivalent to zero at the canonical embeddings within a subset `S` of `|Y|`, then `β` is
  rationally equivalent to zero at the canonical embeddings within `i^{-1}(S)`.  This
  refines the descent of `StacksDraft.AlgebraicGeometry.`
  `Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical`,
  which is the case `S = |Y|` with the carrier of the conclusion forgotten.
* `AlgebraicGeometry.Space.gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_within`:
  the reduction of Stacks 0ERA to one member, with the member's obligation stated as
  `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical`.
* `cycleGroupClosedPushforward_gysinCycleMap_integralClosedSubspacePushforward`:
  `i_*(i^*((i_V)_* d)) = (i_V)_*(c₁ ∩ d)` in `Z_k(X)`, with nothing assumed.  This is the
  identity that replaces Stacks 0ER5 at `i_V`.
* `gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithin`:
  **Stacks 0ERA from the one remaining statement**, which is about `V` and not about `E`.
* `gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithinOnMember`:
  the same with that statement moved onto `V` itself — the cap product formed on `V` is rationally
  equivalent to zero there within `i_V^{-1}|E|` — which is the shape Stacks 0ER9 and Stacks 0EQY
  have.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Descending a rational equivalence together with its carrier -/

section Descent

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)

include hY in
/-- **The pushforward of a rational equivalence at the canonical embeddings keeps its carrier.**
In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a closed subspace, let
`β ∈ Z_k(Y)` and let `T ⊆ |Y|`.  If `β` is rationally equivalent to zero at the canonical
embeddings of Stacks 0ENK within `T`, then `i_*β` is rationally equivalent to zero at the
canonical embeddings within `i(T)`.

`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_cycleGroupClosedPushforward`
is the case `T = |Y|`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_image_cycleGroupClosedPushforward (k : ℤ)
    {β : CycleGroup D (Y.ι ≫ sX) k} {T : Set (points D.site D.base D.base_mem Y.toFunctor)}
    (hβ : IsRationallyEquivalentToZeroWithinCanonical.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β T) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k β)
      (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι '' T) := by
  classical
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  obtain ⟨J, W, hWfin, c, hsubT, hdim, hprin, rfl⟩ := hβ
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
  refine ⟨J, fun n => closureSubspace D sX hX Y.ι (W n), ?_, fun n =>
    cycleGroupClosedPushforward D (closureSubspace D sX hX Y.ι (W n)).isClosedSubspace.1
      (W n).isClosedSubspace.1
      (isDecentSpace_of_isGood D ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX)
        (hW'good n))
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (asIso (m n)).hom)
      ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) (hW'good n).2.2
      ((W n).subspace.ι ≫ Y.ι ≫ sX) (hcomp n) k (c n),
    ?_, ?_, ?_, ?_⟩
  · exact locallyFinite_of_isClosedEmbedding_extend hemb (e := id)
      (fun w hw => absurd rfl (hw w))
      (fun n => (subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)).subset) hWfin
  · exact fun n => (subspacePointSet_closureSubspace_ι D sX hX Y hY (W n)).subset.trans
      (Set.image_mono (hsubT n))
  · exact fun n => (IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) himm (W n)).trans (hdim n)
  · exact fun n => isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D
      ((W n).subspace.ι ≫ Y.ι ≫ sX)
      (isGood_integralClosedSubspace D (Y.ι ≫ sX) hYgood (W n))
      ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) (hW'good n)
      (W n).isIntegralSpace (closureSubspace D sX hX Y.ι (W n)).isIntegralSpace
      (asIso (m n)) (hcomp n) k (hprin n)
  · have hcc : ∀ (n : J) (V : IntegralClosedSubspace D.site D.base D.base_mem
        (W n).subspace.toFunctor),
        (cycleGroupClosedPushforward D (closureSubspace D sX hX Y.ι (W n)).isClosedSubspace.1
            (W n).isClosedSubspace.1
            (isDecentSpace_of_isGood D ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX)
              (hW'good n))
            (isClosedImmersion_of_isIso D.site D.base D.base_mem (asIso (m n)).hom)
            ((closureSubspace D sX hX Y.ι (W n)).subspace.ι ≫ sX) (hW'good n).2.2
            ((W n).subspace.ι ≫ Y.ι ≫ sX) (hcomp n) k (c n)).1
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
            (closureSubspace D sX hX Y.ι (W n)).isClosedSubspace.1
            (closureSubspace D sX hX Y.ι (W n)).isIntegralSpace.2.1 (m n) V) = (c n).1 V := by
      intro n V
      rw [IntegralClosedSubspace.closureImage_eq_pushforward D.site D.base D.base_mem
        (closureSubspace D sX hX Y.ι (W n)).isClosedSubspace.1 (W n).isClosedSubspace.1
        (closureSubspace D sX hX Y.ι (W n)).isIntegralSpace.2.1
        (isClosedImmersion_of_isIso D.site D.base D.base_mem (m n)) V]
      exact cycleClosedPushforward_apply_pushforward D _ _ _ _ (c n).1 V
    refine Subtype.ext (funext fun T₀ => ?_)
    rw [cycleFamilySum_apply]
    have hterm := fun n => congrArg (fun e : CycleGroup D sX k => e.1 T₀)
      (cycleGroupClosedPushforward_integralClosedSubspacePushforward D sX hX Y hY k (W n) (hm n)
        (c n) _ (hcc n))
    rw [← finsum_congr hterm]
    change cycleClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2
        (cycleFamilySum D (Y.ι ≫ sX) hYgood W hWfin k c).1 T₀ = _
    by_cases hT : ∃ T1, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        (D.isDecentSpace_of_isGood sX hX) hY.2 T1 = T₀
    · obtain ⟨T1, rfl⟩ := hT
      rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply]
      refine finsum_congr fun n => ?_
      change _ = cycleClosedPushforward D hX.1 hY.1 _ hY.2 _ _
      rw [cycleClosedPushforward_apply_pushforward]
    · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T₀
        fun T1 hT1 => hT ⟨T1, hT1⟩]
      exact (finsum_eq_zero_of_forall_eq_zero fun n =>
        cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T₀
          fun T1 hT1 => hT ⟨T1, hT1⟩).symm

include hY in
/-- **A rational equivalence at the canonical embeddings descends to a closed subspace together
with its carrier.**  In Situation 0EDT let `X/B` be good, let `i : Y ⟶ X` be the inclusion of a
closed subspace, let `β ∈ Z_k(Y)` and let `S ⊆ |Y|`.  If the pushforward `i_*β` is rationally
equivalent to zero on `X` at the canonical embeddings of Stacks 0ENK within `S`, then `β` is
rationally equivalent to zero on `Y` at the canonical embeddings within `i^{-1}(S)`.

The descent of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical`
is this statement with `S = |Y|` and the carrier of the conclusion forgotten. -/
theorem isRationallyEquivalentToZeroWithinCanonical_preimage_of_closedPushforward (k : ℤ)
    {β : CycleGroup D (Y.ι ≫ sX) k} {S : Set (points D.site D.base D.base_mem X)}
    (hS : S ⊆ subspacePointSet D.site D.base D.base_mem X Y)
    (hβ : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k
      (cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hY.2 sX hX.2.2
        (Y.ι ≫ sX) rfl k β) S) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D (Y.ι ≫ sX)
      (isGood_ι_of_isClosedSubspace D sX hX Y hY) k β
      (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ⁻¹' S) := by
  classical
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1 hY.2
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := hβ
  choose V hV using fun j =>
    IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood (Y.ι ≫ sX) hYgood) hY.2
      (W j) ((hsub j).trans hS)
  have hWeq : (fun j => IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)) = W := funext hV
  subst hWeq
  have hpre : ∀ j, subspacePointSet D.site D.base D.base_mem Y.toFunctor (V j).subspace =
      pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
            (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)).subspace := by
    intro j
    rw [IntegralClosedSubspace.subspacePointSet_pushforward,
      Set.preimage_image_eq _ hemb.injective]
  have hVfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y.toFunctor (V j).subspace :=
    (hWfin.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem Y.ι)).subset
      fun j => (hpre j).subset
  have hVsub : ∀ j, subspacePointSet D.site D.base D.base_mem Y.toFunctor (V j).subspace ⊆
      pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι ⁻¹' S := fun j =>
    (hpre j).subset.trans (Set.preimage_mono (hsub j))
  have hdim' : ∀ j, deltaDimension D (Y.ι ≫ sX) (V j) = k + 1 := fun j =>
    (IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
      (D.isDecentSpace_of_isGood sX hX) hY.2 (V j)).symm.trans (hdim j)
  choose c' hprin' hpush using fun j =>
    exists_isPrincipalDivisorCycleOfGood_cycleClosedPushforward_pushforward D sX hX Y hY k (V j)
      (c j) (hprin j)
  refine ⟨J, V, hVfin, c', hVsub, hdim', hprin', ?_⟩
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
    refine finsum_congr fun j => ?_
    rw [cycleClosedPushforward_apply_pushforward]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T
      fun T0 hT0 => hT ⟨T0, hT0⟩]
    exact finsum_eq_zero_of_forall_eq_zero fun j =>
      cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 _ hY.2 _ T
        fun T0 hT0 => hT ⟨T0, hT0⟩

end Descent

/-! ### The reduction of Stacks 0ERA to one member, at the carrier predicate -/

section Within

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    (rule : GysinComponentRule D p E k)

/-- **The reduction of Stacks 0ERA to one member of the presenting family, stated at the carrier
predicate.**  The hypothesis of
`gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_pushforwardDivisor`
is an unfolded presentation of `i^*((i_V)_* d)` over integral closed subspaces of `E` lying in
`i^{-1}|V|`; that is literally
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical` with carrier `i^{-1}|V|`,
and this is the same statement said so. -/
theorem gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_within
    (hgys : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D p V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ p) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp V) V.isIntegralSpace (k + 1) d →
          IsRationallyEquivalentToZeroWithinCanonical.{v} D (E.1.ι ≫ p) hE k
            (gysinCycleMap D p E hE k rule
              (integralClosedSubspacePushforward D p hp V (k + 1) d))
            (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
              subspacePointSet D.site D.base D.base_mem X V.subspace)) :
    GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule :=
  gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_pushforwardDivisor D p hp E hE k rule
    hgys

end Within

/-! ### Stacks 0ERA from a rational equivalence carried by the divisor -/

section ChernCap

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (σ : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)
    (chern : FirstChernComponentCycleRule D p k)

/-- **The identity that replaces Stacks 0ER5 at the inclusion of a member.**  For `V ⊆ X` an
integral closed subspace and `d ∈ Z_{k+1}(V)`,

`i_*(i^*((i_V)_* d)) = (i_V)_*(c₁ ∩ d)`  in  `Z_k(X)`,

the cap product of Stacks 0EQJ being formed on `V` at the component rule transported from
`AlgebraicGeometry.Space.restrictedSectionChernRule` by
`AlgebraicGeometry.Space.closedSubspaceChernRule`.  Nothing is assumed. -/
theorem cycleGroupClosedPushforward_gysinCycleMap_integralClosedSubspacePushforward
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (d : CycleGroup D (V.subspace.ι ≫ p) (k + 1)) :
    cycleGroupClosedPushforward D hp.1 (vanishingLocus D p hp L σ).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L σ).2.2 p hp.2.2
        ((vanishingLocus D p hp L σ).1.ι ≫ p) rfl k
        (gysinCycleMap D p (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
          (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L σ)
            (isGood_vanishingLocus D p hp L σ) k chern)
          (integralClosedSubspacePushforward D p hp V (k + 1) d)) =
      integralClosedSubspacePushforward D p hp V k
        (firstChernCapCycleMap D (V.subspace.ι ≫ p)
          (isGood_integralClosedSubspace D p hp V) k
          (closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
            (restrictedSectionChernRule D p hp L σ hL k chern)) d) := by
  rw [cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D p hp L σ hL k chern
    (integralClosedSubspacePushforward D p hp V (k + 1) d)]
  exact (cycleGroupClosedPushforward_firstChernCapCycleMap D p hp V.subspace
    V.isClosedSubspace k (restrictedSectionChernRule D p hp L σ hL k chern) d).symm

/-- **Stacks 0ERA from a rational equivalence carried by the divisor, with Stacks 0ER5 not among
the inputs.**  In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module with a
global section `σ` and let `i : E = Z(σ) → X` be the closed immersion of its vanishing locus — the
triple `(ℒ, σ, i)` of Definition 0ER1.  Suppose that for every integral closed subspace `V ⊆ X` of
δ-dimension `k + 2` and every `(k+1)`-cycle `d` on `V` which is a principal divisor cycle at the
canonical embeddings of Stacks 0ENK, the cap product

`c₁(ℒ) ∩ (i_V)_* d`

of Stacks 0EQJ at `AlgebraicGeometry.Space.restrictedSectionChernRule` is rationally equivalent to
zero at the canonical embeddings **within `|E| ∩ |V|`**.  Then the refined Gysin map of Stacks
0ER1 carries every cycle rationally equivalent to zero on `X` at the canonical embeddings to one
rationally equivalent to zero on `E` at the canonical embeddings, which is the assertion of
Stacks 0ERA; `AlgebraicGeometry.Space.gysinChowGroupMapCanonical` then produces
`i^* : CH_{k+1}(X) ⟶ CH_k(E)`.

What the hypothesis asks differs from the summand statement of Stacks 0EQY (proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonicalSummand`)
in exactly two respects, and both are essential:

* the carrier must be `|E| ∩ |V|` and not `|V|` — a rational equivalence on `V` that strays
  outside the divisor does not descend to `E`, and this is the whole reason the source proves
  Lemma 0ER9 instead of quoting Lemma 0EQY;
* the component rule must be `AlgebraicGeometry.Space.restrictedSectionChernRule`, the rule
  through which the Gysin map is read, and not
  `AlgebraicGeometry.Space.canonicalFirstChernRule`.

Those two are the source's Lemma 0ER9 in its case `E ≠ V` and its Lemma 0EQY in its case
`E = V`. -/
theorem gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithin
    (hcap : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D p V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ p) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp V) V.isIntegralSpace (k + 1) d →
          IsRationallyEquivalentToZeroWithinCanonical.{v} D p hp k
            (firstChernCapCycleMap D p hp k (restrictedSectionChernRule D p hp L σ hL k chern)
              (integralClosedSubspacePushforward D p hp V (k + 1) d))
            (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L σ).1 ∩
              subspacePointSet D.site D.base D.base_mem X V.subspace)) :
    GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp
      (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
      (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L σ)
        (isGood_vanishingLocus D p hp L σ) k chern) := by
  refine gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_within.{v} D p hp
    (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k _ fun V hV d hd => ?_
  refine IsRationallyEquivalentToZeroWithinCanonical.mono
    (T := pointsMap D.site D.base D.base_mem (vanishingLocus D p hp L σ).1.toFunctor
      (vanishingLocus D p hp L σ).1.ι ⁻¹'
      (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L σ).1 ∩
        subspacePointSet D.site D.base D.base_mem X V.subspace)) ?_
    (Set.preimage_mono Set.inter_subset_right)
  refine isRationallyEquivalentToZeroWithinCanonical_preimage_of_closedPushforward.{v} D p hp
    (vanishingLocus D p hp L σ).1 (vanishingLocus D p hp L σ).2 k Set.inter_subset_left ?_
  rw [cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D p hp L σ hL k chern
    (integralClosedSubspacePushforward D p hp V (k + 1) d)]
  exact hcap V hV d hd

/-- **Stacks 0ERA from a statement about the member alone.**  Same as
`gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithin`
with the remaining obligation moved onto `V`, where Stacks 0ER9 and Stacks 0EQY live: it is enough
that for every integral closed subspace `V ⊆ X` of δ-dimension `k + 2` and every principal divisor
cycle `d` on `V` at the canonical embeddings, the cap product of Stacks 0EQJ formed **on `V`** at
the transported rule is rationally equivalent to zero on `V` at the canonical embeddings within
`i_V^{-1}|E|`, the part of `V` lying in the divisor.

`V` is good and integral and `ℒ|_V` is invertible, so this is exactly the hypothesis of Stacks
0ER9 for the triple `(V, ℒ|_V, σ|_V)` — with `E ∩ V = Z(σ|_V)` by
`AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme` when `V ⊄ E`, and with `E ∩ V = V`,
the case of Stacks 0EQY, when `V ⊆ E`. -/
theorem gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithinOnMember
    (hcap : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D p V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ p) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp V) V.isIntegralSpace (k + 1) d →
          IsRationallyEquivalentToZeroWithinCanonical.{v} D (V.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp V) k
            (firstChernCapCycleMap D (V.subspace.ι ≫ p)
              (isGood_integralClosedSubspace D p hp V) k
              (closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
                (restrictedSectionChernRule D p hp L σ hL k chern)) d)
            (pointsMap D.site D.base D.base_mem V.subspace.toFunctor V.subspace.ι ⁻¹'
              subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L σ).1)) :
    GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp
      (vanishingLocus D p hp L σ) (isGood_vanishingLocus D p hp L σ) k
      (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L σ)
        (isGood_vanishingLocus D p hp L σ) k chern) := by
  refine gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_firstChernCapWithin.{v} D p hp
    L σ hL k chern fun V hV d hd => ?_
  have hpf : firstChernCapCycleMap D p hp k (restrictedSectionChernRule D p hp L σ hL k chern)
        (integralClosedSubspacePushforward D p hp V (k + 1) d) =
      cycleGroupClosedPushforward D hp.1 V.isClosedSubspace.1
        (D.isDecentSpace_of_isGood p hp) V.isClosedSubspace.2 p hp.2.2 (V.subspace.ι ≫ p) rfl k
        (firstChernCapCycleMap D (V.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp V) k
          (closedSubspaceChernRule D p hp V.subspace V.isClosedSubspace k
            (restrictedSectionChernRule D p hp L σ hL k chern)) d) :=
    (cycleGroupClosedPushforward_firstChernCapCycleMap D p hp V.subspace V.isClosedSubspace k
      (restrictedSectionChernRule D p hp L σ hL k chern) d).symm
  rw [hpf]
  refine IsRationallyEquivalentToZeroWithinCanonical.mono
    (T := pointsMap D.site D.base D.base_mem V.subspace.toFunctor V.subspace.ι ''
      (pointsMap D.site D.base D.base_mem V.subspace.toFunctor V.subspace.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L σ).1))
    (isRationallyEquivalentToZeroWithinCanonical_image_cycleGroupClosedPushforward.{v} D p hp
      V.subspace V.isClosedSubspace k (hcap V hV d hd))
    (Set.subset_inter (Set.image_preimage_subset _ _) (Set.image_subset_range _ _))

end ChernCap

end AlgebraicGeometry.Space

end
