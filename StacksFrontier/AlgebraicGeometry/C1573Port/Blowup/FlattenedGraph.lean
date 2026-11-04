module

public import StacksFrontier.AlgebraicGeometry.C1573Port.Blowup.StrictTransformOfDenseOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport

namespace AlgebraicGeometry.C1573
end AlgebraicGeometry.C1573
namespace Stacks.FlattenedGraph.C1573
end Stacks.FlattenedGraph.C1573

/-!
# Flattening the closure of a graph

Let `ι : D ⟶ Z` be an open immersion of schemes over `S` and let `P` carry morphisms `p : P ⟶ V`
and `q : P ⟶ D` over `S` with `(p, q) : P ⟶ V ×_S D` a closed immersion. The composite
`γ : P ⟶ V ×_S Z` is an immersion; let `W` be its scheme-theoretic image, with projection
`f : W ⟶ Z`. Then `P` is an open subscheme of `W`, namely the inverse image of `D`.

If `q` is flat, Raynaud–Gruson flattening (Stacks 0815) gives a centre `K` on `Z` supported
exactly on the complement of `D` such that the strict transform of `W` along the blowup
`Z' ⟶ Z` in `K` is flat over `Z'`; and that strict transform is the scheme-theoretic image of
`P` in `W ×_Z Z'`.

## Main results

* `AlgebraicGeometry.C1573.exists_flat_strictTransformToBlowUp_of_flat_restrict`: Stacks 0815
  at the structure sheaf, with the centre supported exactly on the complement of the open.
* `Stacks.FlattenedGraph.C1573.range_toImage`: `P` is the inverse image of `D` in `W`.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry.C1573
/-- **Stacks 0815 at the structure sheaf, with the centre supported on the complement of the
open.** A morphism locally of finite presentation from a quasi-compact scheme to a quasi-compact
quasi-separated scheme, flat over a quasi-compact open `D`, has a finitely presented centre `K`
supported exactly on the complement of `D` along whose blowup the strict transform is flat. -/
theorem C1573.exists_flat_strictTransformToBlowUp_of_flat_restrict {W Z : Scheme.{u}}
    [CompactSpace W] [CompactSpace Z] [QuasiSeparatedSpace Z] (f : W ⟶ Z)
    [LocallyOfFinitePresentation f]
    (D : Z.Opens) (hD : IsCompact (D : Set Z)) [Flat (f ∣_ D)] :
    ∃ K : Z.IdealSheafData, FinitePresentation K.subschemeι ∧
      K.supportSet = (D : Set Z)ᶜ ∧ Flat (strictTransformToBlowUp f K) := by
  have : W.unitModule.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (Scheme.unitModule W)
  have hfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ D).ι).obj W.unitModule).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (f ⁻¹ᵁ D).toScheme.ringCatSheaf).prop_of_iso
      (Scheme.Modules.pullbackUnitIso (f ⁻¹ᵁ D).ι).symm inferInstance
  have hfl : IsFlatOver (f ∣_ D).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ D).ι).obj W.unitModule) :=
    (isFlatOver_iff_of_moduleIso _ (Scheme.Modules.pullbackUnitIso (f ⁻¹ᵁ D).ι)).mpr
      (isFlatOver_unit_of_flat (f ∣_ D))
  obtain ⟨K, hKfp, hKsupp, hKflat⟩ :=
    exists_flatteningCentre_supportSet_eq_compl f W.unitModule D hD hfp hfl
  exact ⟨K, hKfp, hKsupp, (flat_strictTransformToBlowUp_iff f K).mpr hKflat⟩

end AlgebraicGeometry

namespace Stacks.FlattenedGraph

open _root_.Stacks.FlattenedGraph.C1573 _root_.AlgebraicGeometry.C1573
variable {S V D Z P : Scheme.{u}} (pV : V ⟶ S) (pD : D ⟶ S) (pZ : Z ⟶ S) (ι : D ⟶ Z)
  [IsOpenImmersion ι] (hι : ι ≫ pZ = pD) (p : P ⟶ V) (q : P ⟶ D) (hpq : p ≫ pV = q ≫ pD)

/-- The morphism `(p, q) : P ⟶ V ×_S D`. -/
abbrev C1573.graph : P ⟶ pullback pV pD := pullback.lift p q hpq

/-- The open immersion `V ×_S D ⟶ V ×_S Z`. -/
abbrev C1573.graphOpen : pullback pV pD ⟶ pullback pV pZ :=
  pullback.map pV pD pV pZ (𝟙 V) ι (𝟙 S) (by simp) (by simp [hι])

/-- The composite `γ : P ⟶ V ×_S Z`. -/
abbrev C1573.graphZ : P ⟶ pullback pV pZ := graph pV pD p q hpq ≫ graphOpen pV pD pZ ι hι

/-- The projection `f : W ⟶ Z` of the scheme-theoretic image of `γ`. -/
abbrev C1573.imageToZ : (graphZ pV pD pZ ι hι p q hpq).image ⟶ Z :=
  (graphZ pV pD pZ ι hι p q hpq).imageι ≫ pullback.snd pV pZ

/-- The square exhibiting `V ×_S X` as the base change of `V ×_S Y` along `g : X ⟶ Y`. -/
private theorem isPullback_map_snd {X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (g : X ⟶ Y)
    (h : g ≫ pY = pX) :
    IsPullback (pullback.map pV pX pV pY (𝟙 V) g (𝟙 S) (by simp) (by simp [h]))
      (pullback.snd pV pX) (pullback.snd pV pY) g := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback pV pY)
  rw [pullback.lift_fst, Category.comp_id, h]
  exact IsPullback.of_hasPullback pV pX

omit [IsOpenImmersion ι] in
/-- The square exhibiting `V ×_S D` as the inverse image of `D` in `V ×_S Z`. -/
theorem C1573.isPullback_graphOpen : IsPullback (graphOpen pV pD pZ ι hι) (pullback.snd pV pD)
    (pullback.snd pV pZ) ι :=
  isPullback_map_snd pV pD pZ ι hι

/-- The open `V ×_S D` of `V ×_S Z` is the inverse image of `D`. -/
theorem C1573.range_graphOpen : Set.range (graphOpen pV pD pZ ι hι).base =
    (pullback.snd pV pZ ⁻¹ᵁ ι.opensRange : Set ↥(pullback pV pZ)) := by
  have h := isPullback_graphOpen pV pD pZ ι hι
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (show Function.Surjective h.isoPullback.hom.base from
      h.isoPullback.hom.homeomorph.surjective).range_eq, Set.image_univ,
    IsOpenImmersion.range_pullbackFst]

namespace C1573
/-- The morphism `V ×_S D ⟶ V ×_S Z` is an open immersion. -/
instance : IsOpenImmersion (graphOpen pV pD pZ ι hι) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_graphOpen pV pD pZ ι hι).flip inferInstance

end C1573
variable [IsClosedImmersion (graph pV pD p q hpq)]

namespace C1573
/-- The composite `γ : P ⟶ V ×_S Z` is an immersion. -/
instance : IsImmersion (graphZ pV pD pZ ι hι p q hpq) := inferInstance

end C1573
omit [IsOpenImmersion ι] [IsClosedImmersion (graph pV pD p q hpq)] in
/-- The range of `γ` is the range of `(p, q)` in the open `V ×_S D`. -/
theorem C1573.range_graphZ_eq : Set.range (graphZ pV pD pZ ι hι p q hpq).base =
    (graphOpen pV pD pZ ι hι).base '' Set.range (graph pV pD p q hpq).base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

variable [QuasiCompact (graphZ pV pD pZ ι hι p q hpq)]

namespace C1573
/-- The morphism from `P` to the scheme-theoretic image of `γ` is an open immersion. -/
instance : IsOpenImmersion (graphZ pV pD pZ ι hι p q hpq).toImage :=
  isOpenImmersion_toImage _ (.inl inferInstance)

end C1573
/-- **`P` is the inverse image of `D` in the scheme-theoretic image `W` of `γ`.** -/
theorem C1573.range_toImage : Set.range (graphZ pV pD pZ ι hι p q hpq).toImage.base =
    ((imageToZ pV pD pZ ι hι p q hpq) ⁻¹ᵁ ι.opensRange : Set _) := by
  set γ := graphZ pV pD pZ ι hι p q hpq
  set m := graphOpen pV pD pZ ι hι
  set c := graph pV pD p q hpq
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    show ((γ.toImage ≫ γ.imageι) ≫ pullback.snd pV pZ).base x ∈ Set.range ι.base
    rw [Scheme.Hom.toImage_imageι]
    show ((c ≫ m) ≫ pullback.snd pV pZ).base x ∈ _
    rw [Category.assoc, pullback.lift_snd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro w hw
    obtain ⟨d, hd⟩ := hw
    -- the image of `w` lies in the open `V ×_S D`
    have hmem : γ.imageι.base w ∈ Set.range m.base := by
      rw [range_graphOpen]
      exact ⟨d, hd⟩
    obtain ⟨y, hy⟩ := hmem
    -- the range of `c` is closed, and `w` lies in the closure of the range of `γ`
    have hcl : γ.imageι.base w ∈ closure (Set.range γ.base) := by
      rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    have hy' : y ∈ Set.range c.base := by
      rw [← c.isClosedEmbedding.isClosed_range.closure_eq,
        m.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
      show m.base y ∈ closure (m.base '' Set.range c.base)
      rw [hy, ← range_graphZ_eq]
      exact hcl
    obtain ⟨x, rfl⟩ := hy'
    refine ⟨x, γ.imageι.isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι, ← hy]
    rfl

omit [IsOpenImmersion ι] [IsClosedImmersion (graph pV pD p q hpq)]
  [QuasiCompact (graphZ pV pD pZ ι hι p q hpq)] in
/-- The projection `W ⟶ Z` of the scheme-theoretic image is, over `D`, the morphism `q`. -/
theorem C1573.toImage_imageToZ : (graphZ pV pD pZ ι hι p q hpq).toImage ≫
    imageToZ pV pD pZ ι hι p q hpq = q ≫ ι := by
  rw [imageToZ, ← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc, pullback.lift_snd,
    ← Category.assoc, pullback.lift_snd]

/-- The morphism `V ×_S Z' ⟶ V ×_S Z` induced by a morphism `b : Z' ⟶ Z`. -/
abbrev C1573.baseMap {Z' : Scheme.{u}} (b : Z' ⟶ Z) : pullback pV (b ≫ pZ) ⟶ pullback pV pZ :=
  pullback.map pV (b ≫ pZ) pV pZ (𝟙 V) b (𝟙 S) (by simp) (by simp)

/-- The square exhibiting `V ×_S Z'` as the base change of `V ×_S Z` along `b : Z' ⟶ Z`. -/
theorem C1573.isPullback_baseMap {Z' : Scheme.{u}} (b : Z' ⟶ Z) :
    IsPullback (baseMap pV pZ b) (pullback.snd pV (b ≫ pZ)) (pullback.snd pV pZ) b :=
  isPullback_map_snd pV (b ≫ pZ) pZ b rfl

/-- The comparison `W ×_Z Z' ⟶ V ×_S Z'` for a morphism `b : Z' ⟶ Z`, the base change of the
closed immersion `W ⟶ V ×_S Z`. -/
abbrev C1573.imageBaseChange {Z' : Scheme.{u}} (b : Z' ⟶ Z) :
    pullback (imageToZ pV pD pZ ι hι p q hpq) b ⟶ pullback pV (b ≫ pZ) :=
  pullback.lift (pullback.fst _ b ≫ (graphZ pV pD pZ ι hι p q hpq).imageι ≫ pullback.fst pV pZ)
    (pullback.snd _ b) (by
      have h := pullback.condition (f := imageToZ pV pD pZ ι hι p q hpq) (g := b)
      simp only [imageToZ, Category.assoc] at h ⊢
      rw [pullback.condition, reassoc_of% h])

omit [IsOpenImmersion ι] [IsClosedImmersion (graph pV pD p q hpq)]
  [QuasiCompact (graphZ pV pD pZ ι hι p q hpq)] in
/-- The square exhibiting `W ×_Z Z' ⟶ V ×_S Z'` as the base change of the closed immersion
`W ⟶ V ×_S Z` along `V ×_S Z' ⟶ V ×_S Z`. -/
theorem C1573.isPullback_imageBaseChange {Z' : Scheme.{u}} (b : Z' ⟶ Z) :
    IsPullback (imageBaseChange pV pD pZ ι hι p q hpq b) (pullback.fst _ b) (baseMap pV pZ b)
      (graphZ pV pD pZ ι hι p q hpq).imageι := by
  refine IsPullback.of_right ?_ ?_ (isPullback_baseMap pV pZ b).flip
  · rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback (imageToZ pV pD pZ ι hι p q hpq) b).flip
  · apply pullback.hom_ext
    · simp only [baseMap, imageBaseChange, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [baseMap, imageBaseChange, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]
      simpa [imageToZ] using
        (pullback.condition (f := imageToZ pV pD pZ ι hι p q hpq) (g := b)).symm

namespace C1573
/-- The comparison `W ×_Z Z' ⟶ V ×_S Z'` is a closed immersion. -/
instance {Z' : Scheme.{u}} (b : Z' ⟶ Z) :
    IsClosedImmersion (imageBaseChange pV pD pZ ι hι p q hpq b) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_imageBaseChange pV pD pZ ι hι p q hpq b).flip inferInstance

end C1573
/-- **Flattening the closure of a graph.** If `q` is flat there is a finitely presented centre
`K` on `Z` supported exactly on the complement of `D` and a closed immersion `j : T ⟶ V ×_S Z'`
into the base change along the blowup `Z' ⟶ Z` in `K`, flat over `Z'`, with the same kernel
ideal sheaf as the graph `P ⟶ V ×_S Z'` of `p` and of `q` followed by the section of the blowup
over `D`: `T` is the strict transform of `W`, the scheme-theoretic image of `P`. -/
theorem C1573.exists_flat_closure_graph [CompactSpace ↥(pullback pV pZ)] [CompactSpace Z]
    [QuasiSeparatedSpace Z] (hDc : IsCompact (ι.opensRange : Set Z)) [Flat q]
    [LocallyOfFinitePresentation (imageToZ pV pD pZ ι hι p q hpq)] :
    ∃ (K : Z.IdealSheafData) (hK : K.supportSet = (ι.opensRange : Set Z)ᶜ),
      FinitePresentation K.subschemeι ∧
      ∃ (T : Scheme.{u}) (j : T ⟶ pullback pV (AlgebraicGeometry.blowUpToBase K ≫ pZ)),
        IsClosedImmersion j ∧ Flat (j ≫ pullback.snd _ _) ∧
        j.ker = (pullback.lift p (q ≫ ι.isoOpensRange.hom ≫
          Stacks.Blowup.C1573.sectionOver ι.opensRange K hK) (by
            rw [Category.assoc, Category.assoc, Stacks.Blowup.C1573.sectionOver_comp_assoc,
              Scheme.Hom.isoOpensRange_hom_ι_assoc, hι, hpq])).ker := by
  set γ := graphZ pV pD pZ ι hι p q hpq
  set f := imageToZ pV pD pZ ι hι p q hpq
  set D' := ι.opensRange
  have : CompactSpace γ.image :=
    γ.imageι.isClosedEmbedding.compactSpace
  -- `P` is the open `f⁻¹ D'` of `W`
  have hrange := range_toImage pV pD pZ ι hι p q hpq
  -- flatness of `f` over `D'`
  set e := IsOpenImmersion.isoOfRangeEq γ.toImage (f ⁻¹ᵁ D').ι
    (by rw [hrange, Scheme.Opens.range_ι])
  have he : e.hom ≫ (f ⁻¹ᵁ D').ι = γ.toImage := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hfe : e.hom ≫ (f ∣_ D') = q ≫ ι.isoOpensRange.hom := by
    rw [← cancel_mono D'.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he,
      toImage_imageToZ, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have : Flat (f ∣_ D') := by
    rw [show f ∣_ D' = e.inv ≫ q ≫ ι.isoOpensRange.hom by rw [← hfe, Iso.inv_hom_id_assoc]]
    infer_instance
  obtain ⟨K, hKfp, hKsupp, hflat⟩ :=
    exists_flat_strictTransformToBlowUp_of_flat_restrict f D' hDc
  refine ⟨K, hKsupp, hKfp, _,
    (Stacks.StrictTransform.ideal f (AlgebraicGeometry.blowUpToBase K)
      (exceptionalIdeal K)).subschemeι ≫
      imageBaseChange pV pD pZ ι hι p q hpq (AlgebraicGeometry.blowUpToBase K),
    inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullback.lift_snd]
    exact hflat
  · have hγ : pullback.lift p
        (q ≫ ι.isoOpensRange.hom ≫ Stacks.Blowup.C1573.sectionOver D' K hKsupp) (by
          rw [Category.assoc, Category.assoc, Stacks.Blowup.C1573.sectionOver_comp_assoc,
            Scheme.Hom.isoOpensRange_hom_ι_assoc, hι, hpq]) =
        Stacks.Blowup.C1573.liftOver D' K hKsupp f γ.toImage hrange ≫
          imageBaseChange pV pD pZ ι hι p q hpq (AlgebraicGeometry.blowUpToBase K) := by
      have htoOpen :
          Stacks.Blowup.C1573.toOpen D' f γ.toImage hrange = q ≫ ι.isoOpensRange.hom := by
        rw [← cancel_mono D'.ι, Stacks.Blowup.C1573.toOpen, IsOpenImmersion.lift_fac,
          Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, toImage_imageToZ]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst,
          Stacks.Blowup.C1573.liftOver, pullback.lift_fst_assoc, ← Category.assoc,
          Scheme.Hom.toImage_imageι]
        simp only [γ, graphZ, graph, graphOpen, Category.assoc, pullback.lift_fst,
          Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Stacks.Blowup.C1573.liftOver,
          pullback.lift_snd, htoOpen, Category.assoc]
    rw [hγ]
    simp only [Scheme.Hom.ker_comp]
    rw [Stacks.Blowup.C1573.ker_liftOver, Scheme.IdealSheafData.ker_subschemeι]

end Stacks.FlattenedGraph

end
