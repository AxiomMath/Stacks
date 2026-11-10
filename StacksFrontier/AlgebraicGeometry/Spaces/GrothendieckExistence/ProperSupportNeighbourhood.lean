module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.ClosedAffineBases
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair.Chow
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfRepresentablePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent

/-!
# Proper support near the closed fibre in Situation 0CX4

In Situation [Stacks, Tag 0CX4] let `W ⊆ X` be an open subspace containing the points of the
closed fibre `X₀`, and let `F` be a quasi-coherent `𝒪_W`-module of finite type whose restriction
to `Xₙ` is `Fₙ`. [Stacks, Tag 0CXA] says that after shrinking `W`, still containing `X₀`, the
support of `F` is proper over `A`. This file proves the source's argument for any such `W` and
`F`; Stacks 0CXA itself is the case `W` of [Stacks, Tag 0CX9] and `F = H⁰(K)|_W`.

The source's proof: `(A, Iₙ)`, `Iₙ = Ker(A → Aₙ)`, is a henselian pair ([Stacks, Tag 0CT7]); the
support `Z` of `F` meets `Xₙ` in the support of `Fₙ`, which is proper over `Aₙ = A/Iₙ`; by
[Stacks, Tag 0CWI] `Z = Z₁ ⊔ Z₂` with `Z₁` proper over `A` and `Z₂` missing `X₀`; and
`W ∖ Z₂` is the shrunk neighbourhood.

## Main results

* `AlgebraicGeometry.Space.exists_isProperOver_split_of_henselianPair`: over a henselian pair,
  a closed set of points of a separated finite type space whose part over `A/I` is proper over
  `A/I` splits into a closed piece proper over `A` and a closed piece missing the closed fibre.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isProperOver_trace_of_henselianPair`: the
  point-set form of the shrinking.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.henselianPair_stageIdeal`: the pair
  `(A, Ker(A → Aₙ))` is henselian (Stacks 0CT7).
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.exists_isOpenSubspace_hasProperSupport`:
  the source's proof of Stacks 0CXA for any open neighbourhood of `Xₙ` and any quasi-coherent
  module of finite type on it restricting to `Fₙ`.

## Implementation notes

Stacks 0CWI, the algebraic-space form of the scheme statement Stacks 0CT9, is
`AlgebraicGeometry.Space.exists_isOpenSubspace_isClosedSubspace_isProper_of_henselianPair`
(`StacksFrontier/AlgebraicGeometry/Spaces/ClopenLiftOverHenselianPair.lean`). No declaration of this
file carries a Stacks tag; Stacks 0CXA is registered on
`FlatSheafExistenceSituation.exists_isExistenceNeighbourhood_hasProperSupport`.

The equality of closed fibres in the conclusion of Stacks 0CWI is an isomorphism over the closed
fibre of `X`; only its effect on points is used here: every point of the closed fibre of the
reduced induced subspace lies over the open and closed subspace produced.

## References

* [Stacks Project, Tag 0CXA](https://stacks.math.columbia.edu/tag/0CXA)
* [Stacks Project, Tag 0CWI](https://stacks.math.columbia.edu/tag/0CWI)
* [Stacks Project, Tag 0CT7](https://stacks.math.columbia.edu/tag/0CT7)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0CZF](https://stacks.math.columbia.edu/tag/0CZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt baseProjection surjective_limit_π)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Splitting off the proper part over a henselian pair -/

section Henselian

variable (B : BigFppfSite.{u}) (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
  (I : Ideal A) (hI : HenselianPair A I) (hT : B.Contains (Spec (.of (A ⧸ I))))
  (qSite : B.obj hT ⟶ B.obj hA)
  (hqSite : B.inclusion.map qSite = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

include hI hqSite in
/-- **The part of a closed set of points proper over a henselian pair.** Let `(A, I)` be a
henselian pair, `f : X ⟶ Spec A` separated and of finite type, and `T ⊆ |X|` a closed set whose
part `T₀` over `Spec (A ⧸ I)`, a closed subset of the closed fibre
`X₀ = X ×_{Spec A} Spec (A ⧸ I)`, is proper over `Spec (A ⧸ I)`. Then `T` is the disjoint union
of two closed pieces `T₁` and `T ∖ T₁`, where `T₁` is proper over `Spec A` and `T ∖ T₁` has no
point over `Spec (A ⧸ I)`.

This is Stacks 0CWI applied to the reduced induced closed
subspace `Z` on `T`, with the whole closed fibre of `Z` as the open and closed subspace: that
closed fibre is the inverse image of `Z` in `X₀`, a closed subspace with points `T₀`, hence
proper over `Spec (A ⧸ I)` by Stacks 0CZC. -/
theorem exists_isProperOver_split_of_henselianPair
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hsep : IsSeparated B (Spec (.of A)) hA f) (hft : IsFiniteType B (Spec (.of A)) hA f)
    (T : Set (points B (Spec (.of A)) hA X)) (hTc : IsClosed T)
    (hf₀ : IsLocallyOfFiniteType B (Spec (.of A)) hA (pullback.snd f
      (yoneda.map (Over.homMk qSite : Over.mk qSite ⟶ Over.mk (𝟙 (B.obj hA))))))
    (hT₀ : IsProperOver B (Spec (.of A)) hA
      (isAlgebraicSpace_pullback B (Spec (.of A)) hA f _ hX
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _)
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _))
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _) _ hf₀
      (pointsMap B (Spec (.of A)) hA _ (pullback.fst _ _) ⁻¹' T)
      (hTc.preimage (continuous_pointsMap B (Spec (.of A)) hA _))) :
    ∃ (T₁ : Set (points B (Spec (.of A)) hA X)) (hT₁ : IsClosed T₁), T₁ ⊆ T ∧
      IsClosed (T \ T₁) ∧
      IsProperOver B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _) f
        hft.1 T₁ hT₁ ∧
      pointsMap B (Spec (.of A)) hA _ (pullback.fst f
        (yoneda.map (Over.homMk qSite : Over.mk qSite ⟶ Over.mk (𝟙 (B.obj hA))))) ⁻¹' T₁ =
        pointsMap B (Spec (.of A)) hA _ (pullback.fst _ _) ⁻¹' T := by
  classical
  let base : BigFppfOver B (Spec (.of A)) hA := Over.mk (𝟙 (B.obj hA))
  let qT : (Over.mk qSite : BigFppfOver B (Spec (.of A)) hA) ⟶ base := Over.homMk qSite
  let q := yoneda.map qT
  have hbase := isAlgebraicSpace_yoneda B (Spec (.of A)) hA base
  have hTT := isAlgebraicSpace_yoneda B (Spec (.of A)) hA (Over.mk qSite)
  have hX₀ : IsAlgebraicSpace B (Spec (.of A)) hA (pullback f q) :=
    isAlgebraicSpace_pullback B (Spec (.of A)) hA f q hX hTT hbase
  let Z := reducedClosedSubspace B (Spec (.of A)) hA X hX T hTc
  have hZc : IsClosedSubspace B (Spec (.of A)) hA Z :=
    isClosedSubspace_reducedClosedSubspace B (Spec (.of A)) hA X hX T hTc
  have hZr : Set.range (pointsMap B (Spec (.of A)) hA _ Z.ι) = T :=
    range_pointsMap_ι_reducedClosedSubspace B (Spec (.of A)) hA X hX T hTc
  have hZinj : Function.Injective (pointsMap B (Spec (.of A)) hA _ Z.ι) :=
    injective_pointsMap_of_isImmersion B (Spec (.of A)) hA hX Z.ι
      (isImmersion_of_isClosedImmersion B (Spec (.of A)) hA hZc.2)
  have hZcm : IsClosedMap (pointsMap B (Spec (.of A)) hA _ Z.ι) :=
    isClosed_of_universallyClosed B (Spec (.of A)) hA hX Z.ι
      (universallyClosed_of_isClosedImmersion B (Spec (.of A)) hA hZc.1 hX _ hZc.2)
  let g := Z.ι ≫ f
  have hgsep : IsSeparated B (Spec (.of A)) hA g :=
    isSeparated_comp B (Spec (.of A)) hA Z.ι f
      (isSeparated_of_isClosedImmersion B (Spec (.of A)) hA Z.ι hZc.2) hsep
  have hgft : IsFiniteType B (Spec (.of A)) hA g :=
    isFiniteType_comp B (Spec (.of A)) hA hZc.1 hX hbase Z.ι f
      (isFiniteType_of_isClosedImmersion B (Spec (.of A)) hA Z.ι hZc.2) hft
  have hZ₀ : IsAlgebraicSpace B (Spec (.of A)) hA (pullback g q) :=
    isAlgebraicSpace_pullback B (Spec (.of A)) hA g q hZc.1 hTT hbase
  let P := Z.preimage (pullback.fst f q)
  have hPc : IsClosedSubspace B (Spec (.of A)) hA P :=
    isClosedSubspace_preimage B (Spec (.of A)) hA (pullback.fst f q) Z hX hX₀ hZc
  have hPr : Set.range (pointsMap B (Spec (.of A)) hA _ P.ι) =
      pointsMap B (Spec (.of A)) hA _ (pullback.fst f q) ⁻¹' T := by
    rw [range_pointsMap_ι_preimage B (Spec (.of A)) hA hX₀ hX _ Z hZc.1, hZr]
  have hPp : IsProper B (Spec (.of A)) hA (P.ι ≫ pullback.snd f q) :=
    isProper_ι_comp_of_isProper_ι_comp B (Spec (.of A)) hA hX₀ hTT _ hf₀ _
      (hTc.preimage (continuous_pointsMap B (Spec (.of A)) hA _)) _
      (isClosedSubspace_reducedClosedSubspace B (Spec (.of A)) hA _ hX₀ _ _)
      (range_pointsMap_ι_reducedClosedSubspace B (Spec (.of A)) hA _ hX₀ _ _) hT₀ P hPc hPr
  have hpaste : IsPullback (P.ι ≫ pullback.snd f q) (Z.fromPreimage (pullback.fst f q)) q g :=
    IsPullback.paste_horiz (Subfunctor.isPullback_preimage (pullback.fst f q) Z).flip
      (IsPullback.of_hasPullback f q).flip
  let e := hpaste.flip.isoPullback
  have hYp : IsProper B (Spec (.of A)) hA
      ((⊤ : Subfunctor (pullback g q)).ι ≫ pullback.snd g q) := by
    have h : (⊤ : Subfunctor (pullback g q)).ι ≫ pullback.snd g q =
        (⊤ : Subfunctor (pullback g q)).ι ≫ e.inv ≫ (P.ι ≫ pullback.snd f q) := by
      rw [← hpaste.flip.isoPullback_hom_snd, Iso.inv_hom_id_assoc]
    rw [h]
    exact isProper_comp B (Spec (.of A)) hA (isOpenSubspace_top hZ₀).1 hZ₀ hTT _ _
      (isProper_of_isIso B (Spec (.of A)) hA _)
      (isProper_comp B (Spec (.of A)) hA hZ₀ hPc.1 hTT _ _
        (isProper_of_isIso B (Spec (.of A)) hA _) hPp)
  obtain ⟨WZ, hWo, hWc, hWp, eW, heW⟩ :=
    exists_isOpenSubspace_isClosedSubspace_isProper_of_henselianPair A I hI B hA hT qSite hqSite
      Z.toFunctor hZc.1 g hgsep hgft ⊤
      (isOpenSubspace_top hZ₀) (isClosedSubspace_top_subfunctor B (Spec (.of A)) hA hZ₀) hYp
  have hWY : ∀ z₀ : points B (Spec (.of A)) hA (pullback g q),
      pointsMap B (Spec (.of A)) hA _ (pullback.fst g q) z₀ ∈
        Set.range (pointsMap B (Spec (.of A)) hA _ WZ.ι) := by
    intro z₀
    let t := (pointsHomeomorphOfIso B (Spec (.of A)) hA
      (asIso (⊤ : Subfunctor (pullback g q)).ι)).symm z₀
    have ht : pointsMap B (Spec (.of A)) hA _ (⊤ : Subfunctor (pullback g q)).ι t = z₀ :=
      (pointsHomeomorphOfIso B (Spec (.of A)) hA
        (asIso (⊤ : Subfunctor (pullback g q)).ι)).apply_symm_apply z₀
    refine ⟨pointsMap B (Spec (.of A)) hA _
      (eW.hom ≫ pullback.fst (WZ.ι ≫ g) q) t, ?_⟩
    rw [← ht, ← pointsMap_comp_apply, ← pointsMap_comp_apply, ← heW, Category.assoc,
      Category.assoc, pullback.lift_fst]
  let RW := Set.range (pointsMap B (Spec (.of A)) hA _ WZ.ι)
  have hRWo : IsOpen RW := (openSubspacesOrderIso B (Spec (.of A)) hA _ hZc.1 ⟨WZ, hWo⟩).2
  have hRWc : IsClosed RW :=
    isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of A)) hA hZc.1 WZ.ι hWc.2
  let T₁ := pointsMap B (Spec (.of A)) hA _ Z.ι '' RW
  have hT₁c : IsClosed T₁ := hZcm _ hRWc
  have hT₁T : T₁ ⊆ T := hZr ▸ Set.image_subset_range _ _
  refine ⟨T₁, hT₁c, hT₁T, ?_, ?_, ?_⟩
  · have h := hZcm _ hRWo.isClosed_compl
    rwa [Set.image_compl_eq_range_sdiff_image hZinj, hZr] at h
  · let R₁ := reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    have hR₁ := isAlgebraicSpace_reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    have hR₁red :=
      hasEtaleLocalProperty_isReduced_reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    obtain ⟨g₁, hg₁⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B
      (Spec (.of A)) hA X hX T hTc hR₁ hR₁red R₁.ι).2
        (by rwa [range_pointsMap_ι_reducedClosedSubspace])
    obtain ⟨v, hv⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B (Spec (.of A)) hA
      hZc.1 hR₁ WZ hWc hR₁red g₁).2 (by
        rintro _ ⟨r, rfl⟩
        have hr : pointsMap B (Spec (.of A)) hA _ R₁.ι r ∈ T₁ := by
          rw [← range_pointsMap_ι_reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c]
          exact ⟨r, rfl⟩
        obtain ⟨z, hz, hze⟩ := hr
        rw [← hg₁, pointsMap_comp_apply] at hze
        exact hZinj hze ▸ hz)
    have hv' : v ≫ (WZ.ι ≫ Z.ι) = R₁.ι := by rw [← Category.assoc, hv, hg₁]
    have hvp : IsProper B (Spec (.of A)) hA v :=
      isProper_of_comp_eq_ι_reducedClosedSubspace B (Spec (.of A)) hA X hX hWo.1 T₁ hT₁c
        (WZ.ι ≫ Z.ι) inferInstance v hv'
    change IsProper B (Spec (.of A)) hA (R₁.ι ≫ f)
    rw [← hv', Category.assoc, Category.assoc]
    exact isProper_comp B (Spec (.of A)) hA hR₁ hWo.1 hbase v (WZ.ι ≫ g) hvp hWp
  · refine Set.Subset.antisymm (Set.preimage_mono hT₁T) fun y hy => ?_
    rw [Set.mem_preimage, ← hZr] at hy
    obtain ⟨z, hz⟩ := hy
    have hcomp : pointsMap B (Spec (.of A)) hA _ g z =
        pointsMap B (Spec (.of A)) hA _ q
          (pointsMap B (Spec (.of A)) hA _ (pullback.snd f q) y) := by
      rw [pointsMap_comp_apply, hz, ← pointsMap_comp_apply, ← pointsMap_comp_apply,
        pullback.condition]
    obtain ⟨z₀, hz₀, -⟩ := exists_points_of_isPullback B (Spec (.of A)) hA
      (IsPullback.of_hasPullback g q) z _ hcomp
    obtain ⟨w, hw⟩ := hWY z₀
    rw [hz₀] at hw
    exact ⟨z, ⟨w, hw⟩, hz⟩

/-- **Shrinking an open neighbourhood of the closed fibre to make a closed set proper.** Let
`(A, I)` be a henselian pair, `f : X ⟶ Spec A` separated and of finite type, `W ⊆ X` an open
subspace containing every point of the closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ I)`, and
`C ⊆ |W|` closed. Suppose the part over `Spec (A ⧸ I)` of the closure `C̄` of `C` in `|X|`, a
closed subset of `|X₀|`, is proper over `Spec (A ⧸ I)`. Then there is an open subspace `W' ≤ W`,
still containing every point of `X₀`, in which the trace of `C` is proper over `Spec A`.

This is the point-set content of Stacks 0CXA, with `C` the support of the module. The closed
set `C̄` splits as `T₁ ⊔ T₂` with `T₁` proper over `Spec A` and `T₂` missing `X₀`
(`AlgebraicGeometry.Space.exists_isProperOver_split_of_henselianPair`, i.e. Stacks 0CWI);
the henselian property puts `T₁` inside `W`, and `W' = W ∖ T₂`. -/
theorem exists_isOpenSubspace_isProperOver_trace_of_henselianPair
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (I : Ideal A) (hI : HenselianPair A I)
    (hT : B.Contains (Spec (.of (A ⧸ I)))) (qSite : B.obj hT ⟶ B.obj hA)
    (hqSite : B.inclusion.map qSite = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    {X : (BigFppfOver B (Spec A) hA)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec A) hA X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hsep : IsSeparated B (Spec A) hA f) (hft : IsFiniteType B (Spec A) hA f)
    (W : Subfunctor X) (hW : IsOpenSubspace B (Spec A) hA W)
    (hW₀ : Set.range (pointsMap B (Spec A) hA _ (pullback.fst f
      (yoneda.map (Over.homMk qSite : Over.mk qSite ⟶ Over.mk (𝟙 (B.obj hA)))))) ⊆
        Set.range (pointsMap B (Spec A) hA _ W.ι))
    (C : Set (points B (Spec A) hA W.toFunctor)) (hC : IsClosed C)
    (hf₀ : IsLocallyOfFiniteType B (Spec A) hA (pullback.snd f
      (yoneda.map (Over.homMk qSite : Over.mk qSite ⟶ Over.mk (𝟙 (B.obj hA))))))
    (hC₀ : IsProperOver B (Spec A) hA
      (isAlgebraicSpace_pullback B (Spec A) hA f _ hX (isAlgebraicSpace_yoneda B (Spec A) hA _)
        (isAlgebraicSpace_yoneda B (Spec A) hA _))
      (isAlgebraicSpace_yoneda B (Spec A) hA _) _ hf₀
      (pointsMap B (Spec A) hA _ (pullback.fst _ _) ⁻¹'
        closure (pointsMap B (Spec A) hA _ W.ι '' C))
      (isClosed_closure.preimage (continuous_pointsMap B (Spec A) hA _))) :
    ∃ (W' : Subfunctor X) (hW' : IsOpenSubspace B (Spec A) hA W') (hle : W' ≤ W),
      Set.range (pointsMap B (Spec A) hA _ (pullback.fst f
        (yoneda.map (Over.homMk qSite : Over.mk qSite ⟶ Over.mk (𝟙 (B.obj hA)))))) ⊆
        Set.range (pointsMap B (Spec A) hA _ W'.ι) ∧
      ∃ (hlft : IsLocallyOfFiniteType B (Spec A) hA (W'.ι ≫ f))
        (hC' : IsClosed (pointsMap B (Spec A) hA _ (Subfunctor.homOfLe hle) ⁻¹' C)),
        IsProperOver B (Spec A) hA hW'.1 (isAlgebraicSpace_yoneda B (Spec A) hA _) (W'.ι ≫ f)
          hlft _ hC' := by
  obtain ⟨A, _⟩ := A
  classical
  let base : BigFppfOver B (Spec (.of A)) hA := Over.mk (𝟙 (B.obj hA))
  let qT : (Over.mk qSite : BigFppfOver B (Spec (.of A)) hA) ⟶ base := Over.homMk qSite
  let q := yoneda.map qT
  have hbase := isAlgebraicSpace_yoneda B (Spec (.of A)) hA base
  let e := pointsMap B (Spec (.of A)) hA _ W.ι
  have he : Topology.IsOpenEmbedding e := isOpenEmbedding_pointsMap_ι B (Spec (.of A)) hA hW
  obtain ⟨T₁, hT₁c, hT₁C, hT₂c, hT₁p, hpre⟩ :=
    exists_isProperOver_split_of_henselianPair B A hA I hI hT qSite hqSite hX f hsep hft
      (closure (e '' C)) isClosed_closure hf₀ hC₀
  have hfib : ∀ x : points B (Spec (.of A)) hA X,
      (pointsToScheme B (Spec (.of A)) hA base (pointsMap B (Spec (.of A)) hA _ f x) :
        PrimeSpectrum A) ∈
        PrimeSpectrum.zeroLocus (I : Set A) →
      x ∈ Set.range (pointsMap B (Spec (.of A)) hA _ (pullback.fst f q)) := by
    intro x hz
    have hrq : Set.range ((BigFppfOver.toScheme B (Spec (.of A)) hA).map qT) =
        PrimeSpectrum.zeroLocus (I : Set A) := by
      change Set.range (B.inclusion.map qSite) = _
      rw [hqSite]
      exact range_spec_map_quotient_mk I
    obtain ⟨s, hs⟩ : pointsToScheme B (Spec (.of A)) hA base (pointsMap B (Spec (.of A)) hA _ f x) ∈
        Set.range ((BigFppfOver.toScheme B (Spec (.of A)) hA).map qT) := hrq ▸ hz
    obtain ⟨t, rfl⟩ := (bijective_pointsToScheme B (Spec (.of A)) hA _).2 s
    have ht : pointsMap B (Spec (.of A)) hA _ f x = pointsMap B (Spec (.of A)) hA _ q t := by
      apply (bijective_pointsToScheme B (Spec (.of A)) hA base).1
      rw [pointsToScheme_pointsMap_yoneda B (Spec (.of A)) hA qT t, hs]
    obtain ⟨y, hy, -⟩ := exists_points_of_isPullback B (Spec (.of A)) hA
      (IsPullback.of_hasPullback f q) x t ht
    exact ⟨y, hy⟩
  have hT₁W : T₁ ⊆ Set.range e := by
    let R := reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    have hR := isAlgebraicSpace_reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    have hRr : Set.range (pointsMap B (Spec (.of A)) hA _ R.ι) = T₁ :=
      range_pointsMap_ι_reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    let fR : points B (Spec (.of A)) hA R.toFunctor → PrimeSpectrum A := fun x =>
      pointsToScheme B (Spec (.of A)) hA base (pointsMap B (Spec (.of A)) hA _ (R.ι ≫ f) x)
    have hfR : IsClosedMap fR :=
      (schemePointsHomeomorph B (Spec (.of A)) hA base).isClosedMap.comp
        (isClosed_of_universallyClosed B (Spec (.of A)) hA hbase _ hT₁p.2.2)
    have hsub := subset_of_isClosed_of_forall_mem_zeroLocus I hI fR hfR isClosed_univ
      ((he.isOpenMap.isOpen_range).preimage (continuous_pointsMap B (Spec (.of A)) hA R.ι)) (by
        intro x hz _
        simp only [fR, pointsMap_comp_apply] at hz
        obtain ⟨y, hy⟩ := hfib _ hz
        exact hW₀ ⟨y, hy⟩)
    rw [← hRr]
    rintro _ ⟨x, rfl⟩
    exact hsub (Set.mem_univ x)
  let T₂ := closure (e '' C) \ T₁
  let W' := openSubspaceOfPoints B (Spec (.of A)) hA X (Set.range e \ T₂)
  have hW'o : IsOpenSubspace B (Spec (.of A)) hA W' :=
    isOpenSubspace_openSubspaceOfPoints B (Spec (.of A)) hA hX _ (he.isOpen_range.sdiff hT₂c)
  have hW'r : Set.range (pointsMap B (Spec (.of A)) hA _ W'.ι) = Set.range e \ T₂ :=
    range_pointsMap_ι_openSubspaceOfPoints B (Spec (.of A)) hA _
  have hle : W' ≤ W :=
    le_of_range_pointsMap_ι_subset B (Spec (.of A)) hA hW (hW'r ▸ Set.sdiff_subset)
  let k := Subfunctor.homOfLe hle
  have hk : k ≫ W.ι = W'.ι := Subfunctor.homOfLe_ι hle
  let C' := pointsMap B (Spec (.of A)) hA _ k ⁻¹' C
  have hC'c : IsClosed C' := hC.preimage (continuous_pointsMap B (Spec (.of A)) hA k)
  have hW'ι : ∀ x, pointsMap B (Spec (.of A)) hA _ W'.ι x =
      e (pointsMap B (Spec (.of A)) hA _ k x) := fun x => by rw [← hk, pointsMap_comp_apply]
  have himage : pointsMap B (Spec (.of A)) hA _ W'.ι '' C' = T₁ := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : pointsMap B (Spec (.of A)) hA _ W'.ι x ∈ Set.range e \ T₂ := hW'r ▸ ⟨x, rfl⟩
      by_contra hn
      refine h1.2 ⟨?_, hn⟩
      rw [hW'ι]
      exact subset_closure ⟨_, hx, rfl⟩
    · intro ht
      obtain ⟨x, rfl⟩ : t ∈ Set.range (pointsMap B (Spec (.of A)) hA _ W'.ι) := by
        rw [hW'r]
        exact ⟨hT₁W ht, fun h => h.2 ht⟩
      refine ⟨x, ?_, rfl⟩
      have hcl := hT₁C ht
      rw [hW'ι] at hcl
      change pointsMap B (Spec (.of A)) hA _ k x ∈ C
      rwa [← hC.closure_eq, he.isEmbedding.closure_eq_preimage_closure_image]
  refine ⟨W', hW'o, hle, ?_, isLocallyOfFiniteType_comp B (Spec (.of A)) hA hW'o.1 hX hbase W'.ι f
    (isLocallyOfFiniteType_of_isEtale' B (Spec (.of A)) hA _
      (isEtale_of_isOpenImmersion B (Spec (.of A)) hA hW'o.2)) hft.1, hC'c, ?_⟩
  · rintro _ ⟨y, rfl⟩
    rw [hW'r]
    exact ⟨hW₀ ⟨y, rfl⟩, fun h => h.2 ((Set.ext_iff.mp hpre y).2 h.1)⟩
  · let R := reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    have hR := isAlgebraicSpace_reducedClosedSubspace B (Spec (.of A)) hA X hX T₁ hT₁c
    let R' := reducedClosedSubspace B (Spec (.of A)) hA W'.toFunctor hW'o.1 C' hC'c
    have hR' :=
      isAlgebraicSpace_reducedClosedSubspace B (Spec (.of A)) hA W'.toFunctor hW'o.1 C' hC'c
    obtain ⟨v, hv⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B
      (Spec (.of A)) hA
      X hX T₁ hT₁c hR' (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B (Spec (.of A)) hA
        W'.toFunctor hW'o.1 C' hC'c) (R'.ι ≫ W'.ι)).2 (by
        rw [pointsMap_comp, Set.range_comp, range_pointsMap_ι_reducedClosedSubspace, himage])
    have hRle : Subfunctor.range R.ι ≤ W' := by
      have h := range_le_openSubspaceOfPoints_range_pointsMap R.ι
      rw [range_pointsMap_ι_reducedClosedSubspace] at h
      refine h.trans (openSubspaceOfPoints_mono B (Spec (.of A)) hA fun t ht => ?_)
      exact ⟨hT₁W ht, fun h => h.2 ht⟩
    let u := Subfunctor.lift R.ι hRle
    have hu : u ≫ W'.ι = R.ι := Subfunctor.lift_ι _ _
    have : Mono u := mono_of_mono_fac hu
    have hvu : v ≫ u = R'.ι := by
      rw [← cancel_mono W'.ι, Category.assoc, hu, hv]
    have hvp : IsProper B (Spec (.of A)) hA v :=
      isProper_of_comp_eq_ι_reducedClosedSubspace B (Spec (.of A)) hA W'.toFunctor hW'o.1 hR C' hC'c
        u inferInstance v hvu
    change IsProper B (Spec (.of A)) hA (R'.ι ≫ W'.ι ≫ f)
    rw [← Category.assoc, ← hv, Category.assoc]
    exact isProper_comp B (Spec (.of A)) hA hR' hR hbase v (R.ι ≫ f) hvp hT₁p


end Henselian

/-! ### Situation 0CX4 -/

/-- Properness over the base of a closed set of points only depends on the set. -/
private theorem isProperOver_of_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    {hY : IsAlgebraicSpace B S hS Y} {f : X ⟶ Y} {hf : IsLocallyOfFiniteType B S hS f}
    {T T' : Set (points B S hS X)} (h : T = T') {hT : IsClosed T} {hT' : IsClosed T'}
    (hp : IsProperOver B S hS hX hY f hf T hT) : IsProperOver B S hS hX hY f hf T' hT' := by
  subst h
  exact hp

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The kernel `Iₙ = Ker(A → Aₙ)` of the projection of the inverse-limit ring onto level `n`. -/
abbrev stageIdeal (n : ℕ) : Ideal (limit D.system : CommRingCat.{u}) :=
  RingHom.ker (limit.π D.system (op n)).hom

/-- **The pair `(A, Ker(A → Aₙ))` is henselian** (Stacks 0CT7): the transitions of the inverse
system are onto with locally nilpotent kernels. -/
theorem henselianPair_stageIdeal (n : ℕ) :
    HenselianPair (limit D.system : CommRingCat.{u}) (D.stageIdeal n) := by
  have : HenselianRing (limit D.system : CommRingCat.{u}) (D.stageIdeal n) :=
    henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical D.system (limit.cone D.system)
      (limit.isLimit D.system)
      (fun m => ⟨D.transition_surjective m,
        fun x hx => mem_nilradical.mpr (D.transition_locallyNilpotent m x hx)⟩) n
  exact henselianPair_of_henselianRing _ _

/-- `A ⧸ Ker(A → Aₙ) ≅ Aₙ`, the projection being onto. -/
def stageQuotientEquiv (n : ℕ) :
    (limit D.system : CommRingCat.{u}) ⧸ D.stageIdeal n ≃+* D.system.obj (op n) :=
  RingHom.quotientKerEquivOfSurjective (surjective_limit_π D.system D.transition_surjective n)

/-- `Spec (A ⧸ Iₙ) ≅ Spec Aₙ`. -/
def stageQuotientSpecIso (n : ℕ) :
    Spec (CommRingCat.of ((limit D.system : CommRingCat.{u}) ⧸ D.stageIdeal n)) ≅
      baseAt D.system n :=
  Scheme.Spec.mapIso (D.stageQuotientEquiv n).toCommRingCatIso.symm.op

/-- The isomorphism `Spec (A ⧸ Iₙ) ≅ Spec Aₙ` followed by the projection `Spec Aₙ ⟶ Spec A` is
the closed immersion `Spec (A ⧸ Iₙ) ⟶ Spec A`. -/
lemma stageQuotientSpecIso_hom_comp (n : ℕ) :
    (D.stageQuotientSpecIso n).hom ≫ baseProjection D.system n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.stageIdeal n))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  change (D.stageQuotientEquiv n).symm ((limit.π D.system (op n)).hom a) = _
  rw [RingEquiv.symm_apply_eq]
  exact (RingHom.quotientKerEquivOfSurjective_apply_mk _ a).symm

/-- `Spec (A ⧸ Iₙ)` lies in the site, being isomorphic to `Spec Aₙ`. -/
theorem contains_stageQuotient (n : ℕ) :
    D.B.Contains (Spec (CommRingCat.of ((limit D.system : CommRingCat.{u}) ⧸ D.stageIdeal n))) :=
  lt_of_eq_of_lt (Scheme.size_congr (D.stageQuotientSpecIso n)) (D.containsBaseAt n)

/-- The closed immersion `Spec (A ⧸ Iₙ) ⟶ Spec A` as a morphism of the site. -/
def stageQuotientSite (n : ℕ) :
    D.B.obj (D.contains_stageQuotient n) ⟶ D.B.obj D.containsLimitBase :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.stageIdeal n))))

/-- `Spec (A ⧸ Iₙ)` and `Spec Aₙ` are isomorphic objects over `Spec A`. -/
def stageQuotientOverIso (n : ℕ) :
    (Over.mk (D.stageQuotientSite n) : BigFppfOver D.B D.S D.containsLimitBase) ≅
      baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n :=
  Over.isoMk (ObjectProperty.isoMk _ (D.stageQuotientSpecIso n))
    (ObjectProperty.hom_ext _ (D.stageQuotientSpecIso_hom_comp n))

/-- The structure morphism `Spec (A ⧸ Iₙ) ⟶ Spec A`, on represented presheaves. -/
def stageQuotientFibreMap (n : ℕ) :
    yoneda.obj (Over.mk (D.stageQuotientSite n) : BigFppfOver D.B D.S D.containsLimitBase) ⟶
      (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).1 :=
  yoneda.map (Over.homMk (D.stageQuotientSite n) :
    (Over.mk (D.stageQuotientSite n) : BigFppfOver D.B D.S D.containsLimitBase) ⟶
      Over.mk (𝟙 (D.B.obj D.containsLimitBase)))

/-- The isomorphism `Spec (A ⧸ Iₙ) ≅ Spec Aₙ` over `Spec A`, on represented presheaves. -/
def stageQuotientBaseMap (n : ℕ) :
    yoneda.obj (Over.mk (D.stageQuotientSite n) : BigFppfOver D.B D.S D.containsLimitBase) ⟶
      (schemeSpace (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).1 :=
  yoneda.map (D.stageQuotientOverIso n).hom

/-- The inverse of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageQuotientBaseMap`. -/
def stageQuotientBaseInv (n : ℕ) :
    (schemeSpace (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).1 ⟶
      yoneda.obj (Over.mk (D.stageQuotientSite n) : BigFppfOver D.B D.S D.containsLimitBase) :=
  yoneda.map (D.stageQuotientOverIso n).inv

/-- `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageQuotientBaseInv` is a right inverse
of `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageQuotientBaseMap`. -/
@[reassoc (attr := simp)]
lemma stageQuotientBaseInv_comp_stageQuotientBaseMap (n : ℕ) :
    D.stageQuotientBaseInv n ≫ D.stageQuotientBaseMap n = 𝟙 _ :=
  (yoneda.mapIso (D.stageQuotientOverIso n)).inv_hom_id

/-- The isomorphism `Spec (A ⧸ Iₙ) ≅ Spec Aₙ` commutes with the structure morphisms to
`Spec A`. -/
lemma stageQuotientBaseMap_comp (n : ℕ) :
    D.stageQuotientBaseMap n ≫
        (baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt n).hom =
      D.stageQuotientFibreMap n := by
  have h : (D.stageQuotientOverIso n).hom ≫
      baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n =
        Over.homMk (D.stageQuotientSite n) := Over.OverMorphism.ext (by
    simp only [Over.mk_left, baseObjectAt, stageQuotientOverIso, baseObjectProjection, Over.mk_hom,
      Over.comp_left, Over.isoMk_hom_left, ObjectProperty.isoMk_hom, Over.homMk_left]
    exact ObjectProperty.hom_ext _ (D.stageQuotientSpecIso_hom_comp n))
  exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map h)

/-- The closed fibre `X ×_{Spec A} Spec (A ⧸ Iₙ)` of the henselian statement is the stage `Xₙ`:
the comparison morphism to `Xₙ = Spec Aₙ ×_{Spec A} X`, over `Spec (A ⧸ Iₙ) ≅ Spec Aₙ`. -/
def stageQuotientFibreComparison (n : ℕ) :
    pullback D.X.hom.hom (D.stageQuotientFibreMap n) ⟶ (D.stage n).1 :=
  pullback.lift (pullback.snd D.X.hom.hom (D.stageQuotientFibreMap n) ≫
      D.stageQuotientBaseMap n) (pullback.fst D.X.hom.hom (D.stageQuotientFibreMap n))
    (by rw [Category.assoc, D.stageQuotientBaseMap_comp n, ← pullback.condition])

/-- The comparison morphism to `Xₙ` followed by the closed immersion `Xₙ ⟶ X` is the projection
of the closed fibre to `X`. -/
lemma stageQuotientFibreComparison_comp_closedImmersion (n : ℕ) :
    D.stageQuotientFibreComparison n ≫ (D.closedImmersion n).hom =
      pullback.fst D.X.hom.hom (D.stageQuotientFibreMap n) :=
  pullback.lift_snd _ _ _

/-- The closed fibre over `Spec (A ⧸ Iₙ)` and the stage `Xₙ` form a cartesian square over the
isomorphism `Spec (A ⧸ Iₙ) ≅ Spec Aₙ`. -/
theorem isPullback_stageQuotientFibreComparison (n : ℕ) :
    IsPullback (D.stageQuotientFibreComparison n)
      (pullback.snd D.X.hom.hom (D.stageQuotientFibreMap n)) (D.stageToBase n).hom
      (D.stageQuotientBaseMap n) := by
  refine IsPullback.of_right (h₁₂ := (D.closedImmersion n).hom)
    (h₂₂ := (baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt n).hom)
    (v₁₃ := D.X.hom.hom) ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  rw [D.stageQuotientFibreComparison_comp_closedImmersion n, D.stageQuotientBaseMap_comp n]
  exact IsPullback.of_hasPullback _ _


/-- **Shrinking a neighbourhood of `Xₙ` so that a closed set becomes proper over `A`.** In
Situation 0CX4 let `W ⊆ X` be an open subspace containing the points of `Xₙ` and `C ⊆ |W|` a
closed set whose trace on `Xₙ` is the support of `Fₙ`. Then there is an open subspace
`W' ≤ W`, still containing the points of `Xₙ`, in which the trace of `C` is proper over `A`.

This is `AlgebraicGeometry.Space.exists_isOpenSubspace_isProperOver_trace_of_henselianPair`
for the henselian pair `(A, Ker(A → Aₙ))` (Stacks 0CT7): the closed fibre over
`A ⧸ Ker(A → Aₙ)` is `Xₙ` by a cartesian square, the closure of the image of `C` meets it in the
support of `Fₙ` (the points of `Xₙ` lie in `W`, where `C` is closed), and the support of `Fₙ`
is proper over `Aₙ` by hypothesis of the situation, hence its preimage is proper over
`A ⧸ Ker(A → Aₙ)` (Stacks 0CZF). -/
theorem exists_isOpenSubspace_isProperOver_of_preimage_eq_support (n : ℕ)
    (W : Subfunctor D.X.left.1) (hW : IsOpenSubspace D.B D.S D.containsLimitBase W)
    (hWn : Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom) ⊆
      Set.range (pointsMap D.B D.S D.containsLimitBase _ W.ι))
    (C : Set (points D.B D.S D.containsLimitBase W.toFunctor)) (hC : IsClosed C)
    (hCn : pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom ⁻¹'
        (pointsMap D.B D.S D.containsLimitBase _ W.ι '' C) =
      supportOfSheaf D.B D.S D.containsLimitBase (D.stage n).1
        ((SheafOfModules.toSheaf _).obj (D.F n))) :
    ∃ (W' : Subfunctor D.X.left.1) (hW' : IsOpenSubspace D.B D.S D.containsLimitBase W')
      (hle : W' ≤ W),
      Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom) ⊆
        Set.range (pointsMap D.B D.S D.containsLimitBase _ W'.ι) ∧
      ∃ (hlft : IsLocallyOfFiniteType D.B D.S D.containsLimitBase (W'.ι ≫ D.X.hom.hom))
        (hC' : IsClosed (pointsMap D.B D.S D.containsLimitBase _
          (Subfunctor.homOfLe hle) ⁻¹' C)),
        IsProperOver D.B D.S D.containsLimitBase hW'.1
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
          (W'.ι ≫ D.X.hom.hom) hlft _ hC' := by
  classical
  let B := D.B
  let hA := D.containsLimitBase
  let f := D.X.hom.hom
  let Q : BigFppfOver B D.S hA := Over.mk (D.stageQuotientSite n)
  let q := D.stageQuotientFibreMap n
  let g' := D.stageQuotientFibreComparison n
  let ιn := (D.closedImmersion n).hom
  let e := pointsMap B D.S hA _ W.ι
  have he : Topology.IsOpenEmbedding e := isOpenEmbedding_pointsMap_ι _ _ _ hW
  have hsq := D.isPullback_stageQuotientFibreComparison n
  have hY' : IsAlgebraicSpace B D.S hA (yoneda.obj Q) := isAlgebraicSpace_yoneda _ _ _ Q
  have hX₀ : IsAlgebraicSpace B D.S hA (pullback f q) :=
    isAlgebraicSpace_pullback _ _ _ f q D.X.left.2 hY' (isAlgebraicSpace_yoneda _ _ _ _)
  let X₀ : AlgebraicSpaces B D.S hA := ⟨pullback f q, hX₀⟩
  let Y' : AlgebraicSpaces B D.S hA := ⟨yoneda.obj Q, hY'⟩
  have hsqA : IsPullback (ObjectProperty.homMk g' : X₀ ⟶ _)
      (ObjectProperty.homMk (pullback.snd f q) : X₀ ⟶ Y') (D.stageToBase n)
      (ObjectProperty.homMk (D.stageQuotientBaseMap n) : Y' ⟶ _) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B D.S hA)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B D.S hA F)) hsq
  have hlftn := isLocallyOfFiniteType_spaceBaseProjection_of_isFinitePresentation D.system D.B
    D.containsLimitBase D.containsBaseAt D.X D.finitePresentation n
  obtain ⟨hcln, hpropn⟩ := D.properSupport n
  have hf₀ : IsLocallyOfFiniteType B D.S hA (pullback.snd f q) :=
    (isLocallyOfFiniteType_isStableUnderBaseChange _ _ _).of_isPullback hsqA hlftn
  have hp := isProperOver_preimage _ _ _ hsqA hlftn _ hcln hpropn
  have hfst : ∀ y, pointsMap B D.S hA _ (pullback.fst f q) y =
      pointsMap B D.S hA _ ιn (pointsMap B D.S hA _ g' y) := by
    intro y
    rw [← pointsMap_comp_apply, D.stageQuotientFibreComparison_comp_closedImmersion n]
  have hset : pointsMap B D.S hA _ g' ⁻¹'
        supportOfSheaf D.B D.S D.containsLimitBase (D.stage n).1
          ((SheafOfModules.toSheaf _).obj (D.F n)) =
      pointsMap B D.S hA _ (pullback.fst f q) ⁻¹' closure (e '' C) := by
    rw [← hCn]
    ext y
    simp only [Set.mem_preimage]
    rw [hfst y]
    obtain ⟨w, hw⟩ := hWn ⟨pointsMap B D.S hA _ g' y, rfl⟩
    rw [← hw, he.injective.mem_set_image]
    change w ∈ C ↔ w ∈ e ⁻¹' closure (e '' C)
    rw [← he.isEmbedding.closure_eq_preimage_closure_image, hC.closure_eq]
  have hC₀ : IsProperOver B D.S hA hX₀ hY' (pullback.snd f q) hf₀
      (pointsMap B D.S hA _ (pullback.fst f q) ⁻¹' closure (e '' C))
      (isClosed_closure.preimage (continuous_pointsMap _ _ _ _)) :=
    isProperOver_of_eq hset hp
  have hW₀ : Set.range (pointsMap B D.S hA _ (pullback.fst f q)) ⊆ Set.range e := by
    rintro _ ⟨y, rfl⟩
    rw [hfst y]
    exact hWn ⟨_, rfl⟩
  have hft : IsFiniteType B D.S hA f :=
    isFiniteType_of_isFinitePresentation _ _ _ D.finitePresentation
  obtain ⟨W', hW', hle, hrange, hlft, hC', hprop⟩ :=
    exists_isOpenSubspace_isProperOver_trace_of_henselianPair B (limit D.system)
      hA (D.stageIdeal n) (D.henselianPair_stageIdeal n) (D.contains_stageQuotient n)
      (D.stageQuotientSite n) rfl D.X.left.2 f D.separated hft W hW hW₀ C hC hf₀ hC₀
  refine ⟨W', hW', hle, ?_, hlft, hC', hprop⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy, -⟩ := exists_points_of_isPullback B D.S hA hsq x
    (pointsMap B D.S hA _ (D.stageQuotientBaseInv n)
      (pointsMap B D.S hA _ (D.stageToBase n).hom x)) (by
      rw [← pointsMap_comp_apply, stageQuotientBaseInv_comp_stageQuotientBaseMap, pointsMap_id]
      rfl)
  rw [← hy, ← hfst y]
  exact hrange ⟨y, rfl⟩

/-- **The trace on `Xₙ` of the support of a module whose pullback to `Xₙ` is `Fₙ`.** Let
`W ⊆ X` be an open subspace through which `Xₙ ⟶ X` factors as `k : Xₙ ⟶ W`, and `F` a
quasi-coherent `𝒪_W`-module of finite type with `k^*F ≅ Fₙ`. Then the points of `Xₙ` lying in
(the image in `|X|` of) the support of `F` are exactly the support of `Fₙ` (Stacks 07TZ (3)). -/
theorem preimage_image_supportOfSheaf_eq_support (n : ℕ) (W : Subfunctor D.X.left.1)
    (hW : IsOpenSubspace D.B D.S D.containsLimitBase W)
    (k : D.stage n ⟶ (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces D.B D.S D.containsLimitBase))
    (hk : k.hom ≫ W.ι = (D.closedImmersion n).hom)
    (F : Modules.{u, u} D.B D.S D.containsLimitBase W.toFunctor hW.1)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (eF : (modulePullback D.B D.S D.containsLimitBase k).obj F ≅ D.F n) :
    pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom ⁻¹'
        (pointsMap D.B D.S D.containsLimitBase _ W.ι ''
          supportOfSheaf D.B D.S D.containsLimitBase W.toFunctor
            ((SheafOfModules.toSheaf _).obj F)) =
      supportOfSheaf D.B D.S D.containsLimitBase (D.stage n).1
        ((SheafOfModules.toSheaf _).obj (D.F n)) := by
  rw [← supportOfSheaf_eq_of_iso D.B D.S D.containsLimitBase _ eF,
    supportOfSheaf_modulePullback_eq D.B D.S D.containsLimitBase k F hqc hft]
  ext x
  simp only [Set.mem_preimage]
  rw [← hk, pointsMap_comp_apply, (isOpenEmbedding_pointsMap_ι _ _ _ hW).injective.mem_set_image]

/-- **The source's proof of Stacks 0CXA, for any neighbourhood of `Xₙ` and any module
restricting to `Fₙ`.** In Situation 0CX4 let `W ⊆ X` be an open subspace through which
`Xₙ ⟶ X` factors as `k : Xₙ ⟶ W`, and `F` a quasi-coherent `𝒪_W`-module of finite type with
`k^*F ≅ Fₙ`. Then, after shrinking `W` to an open subspace `W'` still containing the points of
`Xₙ`, the support of `F|_{W'}` is proper over `A`.

The scheme-theoretic support of `F` meets `Xₙ` in the support of `Fₙ`, which is proper over
`Aₙ`; by Stacks 0CWI it splits off a part proper over `A` from a part
missing the closed fibre, and `W'` is the complement of the second part. -/
theorem exists_isOpenSubspace_hasProperSupport (n : ℕ) (W : Subfunctor D.X.left.1)
    (hW : IsOpenSubspace D.B D.S D.containsLimitBase W)
    (k : D.stage n ⟶ (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces D.B D.S D.containsLimitBase))
    (hk : k.hom ≫ W.ι = (D.closedImmersion n).hom)
    (F : Modules.{u, u} D.B D.S D.containsLimitBase W.toFunctor hW.1)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (eF : (modulePullback D.B D.S D.containsLimitBase k).obj F ≅ D.F n) :
    ∃ (W' : Subfunctor D.X.left.1) (hW' : IsOpenSubspace D.B D.S D.containsLimitBase W')
      (hle : W' ≤ W),
      Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom) ⊆
        Set.range (pointsMap D.B D.S D.containsLimitBase _ W'.ι) ∧
      ∃ hlft : IsLocallyOfFiniteType D.B D.S D.containsLimitBase (W'.ι ≫ D.X.hom.hom),
        HasProperSupport D.B D.S D.containsLimitBase hW'.1
          (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
          (W'.ι ≫ D.X.hom.hom) hlft
          ((SheafOfModules.toSheaf _).obj
            ((modulePullback D.B D.S D.containsLimitBase
              (ObjectProperty.homMk (Subfunctor.homOfLe hle) :
                (⟨W'.toFunctor, hW'.1⟩ : AlgebraicSpaces D.B D.S D.containsLimitBase) ⟶
                  ⟨W.toFunctor, hW.1⟩)).obj F)) := by
  have hWn : Set.range (pointsMap D.B D.S D.containsLimitBase _ (D.closedImmersion n).hom) ⊆
      Set.range (pointsMap D.B D.S D.containsLimitBase _ W.ι) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨pointsMap D.B D.S D.containsLimitBase _ k.hom x, ?_⟩
    rw [← pointsMap_comp_apply, hk]
  have hC : IsClosed (supportOfSheaf D.B D.S D.containsLimitBase W.toFunctor
      ((SheafOfModules.toSheaf _).obj F)) :=
    let := hft
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite D.B D.S D.containsLimitBase W.toFunctor hW.1 F
  obtain ⟨W', hW', hle, hrange, hlft, hC', hprop⟩ :=
    D.exists_isOpenSubspace_isProperOver_of_preimage_eq_support n W hW hWn _ hC
      (D.preimage_image_supportOfSheaf_eq_support n W hW k hk F hqc hft eF)
  refine ⟨W', hW', hle, hrange, hlft, ?_⟩
  have h := supportOfSheaf_modulePullback_eq D.B D.S D.containsLimitBase
    (X' := ⟨W'.toFunctor, hW'.1⟩) (X := ⟨W.toFunctor, hW.1⟩)
    (ObjectProperty.homMk (Subfunctor.homOfLe hle)) F hqc hft
  have hcl := isClosed_supportOfSheaf_modulePullback D.B D.S D.containsLimitBase
    (X' := ⟨W'.toFunctor, hW'.1⟩) (X := ⟨W.toFunctor, hW.1⟩)
    (ObjectProperty.homMk (Subfunctor.homOfLe hle)) F hft
  exact ⟨hcl, isProperOver_of_eq h.symm hprop⟩

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
