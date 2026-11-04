module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The incidence variety of lines over the distinct pairs has dimension at most `dim Y + dim Z + 1`

The projection of the incidence variety of Tag 0B1R to its base has relative dimension at most
one at every point
(`AlgebraicGeometry.ProjectiveSpaceOfModule.relativeDimensionLE_incidenceVarietyToBase`), and the
base — the distinct pairs in `Y ×_k Z` — has dimension at most `dim Y + dim Z`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodOfClosedOffSnd_le`, which is
Tag 0B2M). This file puts the two together.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.locallyOfFiniteType_prodOfClosedOffSndToProdTwo`:
  the base of the incidence variety is of finite type over `𝐏(V) ×_k 𝐏(V)`, hence over `Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.noetherianSpace_prodOfClosedOffSnd` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.compactSpace_incidenceVariety`: the base and the
  incidence variety have Noetherian and compact underlying spaces, which is what the fibre
  dimension theory asks of them. The base is an *open* subscheme, so its Noetherian space comes
  from the inducing inclusion and not from a subset instance, which does not apply to the carrier
  of an open subscheme.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_incidenceVariety_le`: **the
  incidence variety over the distinct pairs has dimension at most `dim Y + dim Z + 1`.**

## Implementation notes

The bound is read off pointwise rather than through
`AlgebraicGeometry.RelativeDimensionLE.comp`: the dimension of a space is the supremum of its
local dimensions, and the local dimension at a point is at most the local dimension of the fibre
through it plus the local dimension of the base at its image, which is part (3) of Tag 0B2L and
needs no irreducibility. That avoids having to turn a dimension bound on the base into a
relative-dimension bound for its structure morphism, which would ask for the fibre of a scheme
over `Spec k` to be identified with the scheme itself.

Dimensions take values in `WithBot ℕ∞`, so the bound is additive throughout and no subtraction
appears.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]
  (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) (hZ : IsClosed Z)

/-- **The base of the incidence variety of Tag 0B1R is of finite type over `𝐏(V) ×_k 𝐏(V)`.** -/
public theorem locallyOfFiniteType_prodOfClosedOffSndToProdTwo :
    LocallyOfFiniteType (prodOfClosedOffSndToProdTwo k V Y Z hY hZ) := by
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Y hY
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Z hZ
  have hmapfst : prodOfClosedToProdTwo k V Y Z hY hZ ≫
      pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) =
      pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfι k V Y hY := pullback.lift_fst _ _ _
  have hfstlft : LocallyOfFiniteType (pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hcomp : prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoToSpec k V =
      pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfToSpec k V Y hY := by
    rw [prodTwoToSpec, ← Category.assoc, hmapfst]
    exact Category.assoc _ _ _
  have : LocallyOfFiniteType (prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoToSpec k V) := by
    rw [hcomp]
    exact MorphismProperty.comp_mem _ _ _ hfstlft inferInstance
  have : LocallyOfFiniteType (prodOfClosedToProdTwo k V Y Z hY hZ) :=
    locallyOfFiniteType_of_comp _ (prodTwoToSpec k V)
  rw [prodOfClosedOffSndToProdTwo]
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

/-- The reduced closed subscheme attached to a closed subset of `𝐏(V)` is quasi-compact over
`Spec k`. -/
public theorem quasiCompact_closedSubschemeOfToSpec :
    QuasiCompact (closedSubschemeOfToSpec k V Y hY) := by
  have : IsProper (projectiveSpaceOfModuleToSpec k V) :=
    isProper_projectiveSpaceOfModuleToSpec k V
  have : QuasiCompact (closedSubschemeOfι k V Y hY) :=
    inferInstanceAs (QuasiCompact
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨Y, hY⟩ : Closeds (projectiveSpaceOfModule k V))).subschemeι)
  exact inferInstanceAs (QuasiCompact
    (closedSubschemeOfι k V Y hY ≫ projectiveSpaceOfModuleToSpec k V))

/-- **The base of the incidence variety of Tag 0B1R has a Noetherian underlying space.** It is an
open subscheme of the product of two closed subschemes of `𝐏(V)`, which is of finite type over
`Spec k` and compact. -/
public theorem noetherianSpace_prodOfClosedOffSnd :
    NoetherianSpace (prodOfClosedOffSnd k V Y Z hY hZ).toScheme := by
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Y hY
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Z hZ
  have := quasiCompact_closedSubschemeOfToSpec k V Y hY
  have := quasiCompact_closedSubschemeOfToSpec k V Z hZ
  have hfstqc : QuasiCompact (pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hfstlft : LocallyOfFiniteType (pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hqc : QuasiCompact (pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ) ≫ closedSubschemeOfToSpec k V Y hY) :=
    MorphismProperty.comp_mem _ _ _ hfstqc inferInstance
  have hlft : LocallyOfFiniteType (pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ) ≫ closedSubschemeOfToSpec k V Y hY) :=
    MorphismProperty.comp_mem _ _ _ hfstlft inferInstance
  have : CompactSpace (prodOfClosed k V Y Z hY hZ) :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ _ hqc _
  have : IsLocallyNoetherian (prodOfClosed k V Y Z hY hZ) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ _ hlft _
  have : IsNoetherian (prodOfClosed k V Y Z hY hZ) := ⟨⟩
  have : NoetherianSpace (prodOfClosed k V Y Z hY hZ) := inferInstance
  exact (((prodOfClosedOffSnd k V Y Z hY hZ).ι.isOpenEmbedding.isEmbedding).isInducing
    ).noetherianSpace

/-- **The incidence variety of lines over the distinct pairs has a compact underlying space.**
Its projection to the base is a base change of the projection of the collinearity subscheme,
which is quasi-compact, and the base is compact. -/
public theorem compactSpace_incidenceVariety :
    CompactSpace (incidenceVariety k V (prodOfClosedOffSndToProdTwo k V Y Z hY hZ)) := by
  have : IsProper (projectiveSpaceOfModuleToSpec k V) :=
    isProper_projectiveSpaceOfModuleToSpec k V
  have : NoetherianSpace (prodOfClosedOffSnd k V Y Z hY hZ).toScheme :=
    noetherianSpace_prodOfClosedOffSnd k V Y Z hY hZ
  have : CompactSpace (prodOfClosedOffSnd k V Y Z hY hZ).toScheme :=
    ⟨NoetherianSpace.isCompact Set.univ⟩
  have : QuasiCompact (prFst k V) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (prodTwoToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).flip inferInstance
  have : IsClosedImmersion (collinearSubschemeι k V) := isClosedImmersion_collinearSubschemeι k V
  have : QuasiCompact (collinearSubschemeι k V) :=
    inferInstanceAs (QuasiCompact (collinearIdeal k V).subschemeι)
  have : QuasiCompact (collinearProj k V) :=
    inferInstanceAs (QuasiCompact (collinearSubschemeι k V ≫ prFst k V))
  have hqc : QuasiCompact (incidenceVarietyToBase k V
      (prodOfClosedOffSndToProdTwo k V Y Z hY hZ)) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (collinearProj k V)
        (prodOfClosedOffSndToProdTwo k V Y Z hY hZ)) inferInstance
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ hqc _

/-- **The incidence variety of lines over the distinct pairs has dimension at most
`dim Y + dim Z + 1`.** The projection to the base has relative dimension at most one, and the
base has dimension at most `dim Y + dim Z`. -/
public theorem topologicalKrullDim_incidenceVariety_le [IsAlgClosed k] :
    topologicalKrullDim (incidenceVariety k V (prodOfClosedOffSndToProdTwo k V Y Z hY hZ)) ≤
      topologicalKrullDim (closedSubschemeOf k V Y hY) +
        topologicalKrullDim (closedSubschemeOf k V Z hZ) + 1 := by
  set f := prodOfClosedOffSndToProdTwo k V Y Z hY hZ with hf
  have : LocallyOfFiniteType f := locallyOfFiniteType_prodOfClosedOffSndToProdTwo k V Y Z hY hZ
  have : LocallyOfFiniteType (prodTwoToSpec k V) := inferInstance
  set pB : (prodOfClosedOffSnd k V Y Z hY hZ).toScheme ⟶ Spec (.of k) :=
    f ≫ prodTwoToSpec k V with hpB
  have : LocallyOfFiniteType pB := by rw [hpB]; infer_instance
  set q := incidenceVarietyToBase k V f with hq
  have : LocallyOfFiniteType q := by rw [hq]; infer_instance
  have hrel := relativeDimensionLE_incidenceVarietyToBase k V Y Z hY hZ
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  refine le_trans (topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target k
    (q ≫ pB) pB q rfl x) ?_
  have h1 : topologicalKrullDimAt (q.fiber (q.base x)) (q.asFiber x) ≤ (1 : WithBot ℕ∞) := by
    have := hrel x
    rw [relativeDimensionLEAt_iff] at this
    simpa using this
  have h2 : topologicalKrullDimAt (prodOfClosedOffSnd k V Y Z hY hZ).toScheme (q.base x) ≤
      topologicalKrullDim (closedSubschemeOf k V Y hY) +
        topologicalKrullDim (closedSubschemeOf k V Z hZ) :=
    le_trans (topologicalKrullDimAt_le_topologicalKrullDim _)
      (topologicalKrullDim_prodOfClosedOffSnd_le k V Y Z hY hZ)
  refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
  rw [add_comm]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
