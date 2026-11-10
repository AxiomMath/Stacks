module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionPurityContainment

/-!
# The key case of Stacks 0CX1

In Situation 0CWU, assume `f` and `F` of finite presentation and `F` pure relative to `Y`. Let `V`
be an affine test scheme over `Y` whose structure morphism is locally quasi-finite, and assume
that `F_V` is flat over `V` in dimensions `≥ n + 1`. Then the locus `F_n` over `V` is cut out by
a monomorphism of finite presentation, étale locally on `V` and hence over `V`.

This is the last paragraph of the source's proof. Around a point `v` of `V`, an affine surjective
étale chart `U` of `X_V` presents `F_n` by a scheme-level situation of finite presentation, and
Stacks 05HU gives an elementary étale neighbourhood `(V', v')` and finitely many étale charts
`hⱼ : Wⱼ ⟶ U ×_V V'` covering the fibre over `v'`, each with a complete dévissage. Purity makes
the images of the `hⱼ` in `X_{V'}` contain the relative assassin over a neighbourhood of `v'`
(`AlgebraicGeometry.Space.FlatDimensionSituation.exists_isOpen_relativeAssassin_subset_image`),
so over that neighbourhood `F_n` is the intersection of the functors of the `hⱼ`: this is the
second assertion of Stacks 05UD, applied to the charts `Wⱼ ×_U (U ×_{X_{V'}} U) ⟶ U`, whose
images are the preimages in the chart of the images of the `hⱼ` in `X_{V'}`
(`AlgebraicGeometry.FlatDimensionSituation.isFlat_iff_forall_etaleChart_of_relation`). Each of
those functors is represented near `v'` by Stacks 05UF.

## Main results

* `AlgebraicGeometry.Space.FlatDimensionSituation.isRepresentedOver_of_isAffine_of_isFlat`:
  the key case.

## References

* [Stacks Project, Tag 0CX1](https://stacks.math.columbia.edu/tag/0CX1)
* [Stacks Project, Tag 05UF](https://stacks.math.columbia.edu/tag/05UF)
* [Stacks Project, Tag 05UD](https://stacks.math.columbia.edu/tag/05UD)
* [Stacks Project, Tag 05HU](https://stacks.math.columbia.edu/tag/05HU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Stacks.Flatness

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] _root_.AlgebraicGeometry.isQuasicoherent_pullback_obj'
  _root_.AlgebraicGeometry.isFiniteType_pullback_obj'
  _root_.AlgebraicGeometry.isFinitePresentation_pullback_obj

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u} B S hS)

/-- The structure morphism of a test scheme over a test scheme with locally quasi-finite
structure morphism, through an étale morphism of schemes, is locally quasi-finite. -/
theorem isLocallyQuasiFinite_schemesOverOfContained (V : SchemesOver D.Y)
    (hqf : IsLocallyQuasiFinite B S hS V.hom.hom) {Z : Scheme.{u}} (hZ : B.Contains Z)
    (φ : Z ⟶ (BigFppfOver.toScheme B S hS).obj V.left) [LocallyOfFiniteType φ]
    [LocallyQuasiFinite φ] :
    IsLocallyQuasiFinite B S hS (schemesOverOfContained V hZ φ).hom.hom :=
  isLocallyQuasiFinite_comp B S hS (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) D.Y.2 _ _
    ((isLocallyQuasiFinite_yoneda_map_iff B S hS _).2 ⟨inferInstanceAs (LocallyOfFiniteType φ),
      inferInstanceAs (LocallyQuasiFinite φ)⟩) hqf

/-- **The key case of Stacks 0CX1.** Let `V` be an affine test scheme over `Y` whose structure
morphism is locally quasi-finite, and assume that `F_V` is flat over `V` in dimensions `≥ n + 1`.
Then the locus `F_n` over `V` is cut out by a monomorphism of finite presentation. -/
theorem isRepresentedOver_of_isAffine_of_isFlat (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) (n : ℕ) (V : SchemesOver D.Y)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.left))
    (hqf : IsLocallyQuasiFinite B S hS V.hom.hom)
    (hflat : D.Presented (n + 1) V (Over.mk (𝟙 _))) : D.IsRepresentedOver n V := by
  classical
  obtain ⟨U, hUaff, hUs⟩ :=
    exists_isAffine_isSurjective_chart_baseChangeSpace B S hS D.f hf.2.1 V hVaff
  let E := D.stageSituation B S hS n V U
  suffices key : IsCutOutByMonoFP E.IsFlatInDimensionsGEAfterBaseChange from
    key.of_iff fun Z ↦ (D.presented_iff n V U hUs Z).symm
  have : IsAffine E.S := hVaff
  have : IsAffine E.X := hUaff
  have : LocallyOfFinitePresentation E.f :=
    D.locallyOfFinitePresentation_stageSituation_f B S hS n hf.1 V U
  have : QuasiCompact E.f := D.quasiCompact_stageSituation_f B S hS n V hVaff U hUaff
  have : QuasiSeparated E.f := inferInstance
  have : E.F.IsFinitePresentation := D.isFinitePresentation_stageSituation_F B S hS n hF V U
  have hflatE : _root_.AlgebraicGeometry.IsFlatOverInDimensionsGE E.f E.F (n + 1) :=
    (D.stageSituation B S hS (n + 1) V U).isFlat_id_iff.1
      ((D.presented_iff (n + 1) V U hUs _).1 hflat)
  refine IsCutOutByMonoFP.of_etale_local _
    (fun g h ↦ E.isFlatInDimensionsGEAfterBaseChange_of_hom g h) E.isSheaf_propertyFunctor
    fun v ↦ ?_
  obtain ⟨Nb, -, hNbaff, m, Yj, h, het, hl, hq, ht, hdev, hcov⟩ :=
    exists_isAffine_etaleNeighborhood_completeDevissage_cover E.f E.F v
  have := hNbaff
  have := het
  let qV : Nb.scheme ⟶ (BigFppfOver.toScheme B S hS).obj V.left := Nb.toBase
  have hqVet : Etale qV := Nb.etale_toBase
  -- the neighbourhood as a test scheme
  have hNbc : B.Contains Nb.scheme :=
    B.contains_of_locallyOfFinitePresentation qV V.left.left.2
  let V' := schemesOverOfContained V hNbc qV
  let β : V' ⟶ V := schemesOverOfContainedMap V hNbc qV
  have hqfV' : IsLocallyQuasiFinite B S hS V'.hom.hom :=
    D.isLocallyQuasiFinite_schemesOverOfContained V hqf hNbc qV
  let U' := stageChart B S hS D.f β U
  have hU's : IsSurjective B S hS U'.obj.hom := isSurjective_stageChart B S hS D.f β U hUs
  let E' := D.stageSituation B S hS n V' U'
  let E'' := E.baseChange Nb.toBase
  let φ : E'.X ≅ E''.X := D.stageChartIsoPullback n β U
  have : IsAffine E''.X := inferInstanceAs (IsAffine (Limits.pullback E.f Nb.toBase))
  have hE'aff : IsAffine E'.X := IsAffine.of_isIso φ.hom
  have hE'iff : ∀ Z, E'.IsFlatInDimensionsGEAfterBaseChange Z ↔
      E''.IsFlatInDimensionsGEAfterBaseChange Z :=
    D.stageSituation_stageChart_isFlat_iff_baseChange n β U
  -- the charts, transported to the scheme of the base-changed chart
  let h' : ∀ j, Yj j ⟶ E'.X := fun j ↦ h j ≫ φ.inv
  have het' : ∀ j, Etale (h' j) := fun j ↦ inferInstance
  have hchart : ∀ j T, (E'.etaleChart (h' j)).IsFlatInDimensionsGEAfterBaseChange T ↔
      (E''.etaleChart (h j)).IsFlatInDimensionsGEAfterBaseChange T := by
    intro j T
    have hfj : h' j ≫ E'.f = h j ≫ E''.f :=
      (Category.assoc _ _ _).trans (congrArg (h j ≫ ·) (D.stageChartIsoPullback_inv_f n β U))
    let eφ : (Scheme.Modules.pullback φ.inv).obj E'.F ≅ E''.F :=
      (Scheme.Modules.pullback φ.inv).mapIso (D.stageChartModuleIso n β U) ≪≫
        (Scheme.Modules.pullbackComp φ.inv φ.hom).app E''.F ≪≫
        (Scheme.Modules.pullbackCongr φ.inv_hom_id).app E''.F ≪≫
        (Scheme.Modules.pullbackId _).app E''.F
    let ej : (Scheme.Modules.pullback (h' j)).obj E'.F ≅
        (Scheme.Modules.pullback (h j)).obj E''.F :=
      ((Scheme.Modules.pullbackComp (h j) φ.inv).app E'.F).symm ≪≫
        (Scheme.Modules.pullback (h j)).mapIso eφ
    exact @_root_.AlgebraicGeometry.FlatDimensionSituation.isFlat_mk_iff_of_eq_of_iso _ _ _ _
      hfj inferInstance (hl j) _ _ _ _ _ _ ej n T
  -- the étale relation `U' ×_{X_{V'}} U'`
  let R := chartPair U' U'
  let p₁ : chartScheme R ⟶ E'.X := chartSchemeMap (chartPairFst U' U')
  let p₂ : chartScheme R ⟶ E'.X := chartSchemeMap (chartPairSnd U' U')
  have : Etale p₁ := etale_chartSchemeMap _
  have : Etale p₂ := etale_chartSchemeMap _
  have hp : p₁ ≫ E'.f = p₂ ≫ E'.f :=
    (D.stageSituation_f_eq_of_chartMap n (chartPairFst U' U')).symm.trans
      (D.stageSituation_f_eq_of_chartMap n (chartPairSnd U' U'))
  let ρ := @restrictToChartMapIso B S hS (baseChangeSpace D.f V')
    (D.toFlatnessSituation.baseChangeModule V') (D.isQuasicoherentOnSite_baseChangeModule B S hS V')
  let eR : (Scheme.Modules.pullback p₁).obj E'.F ≅ (Scheme.Modules.pullback p₂).obj E'.F :=
    ρ (chartPairFst U' U') ≪≫ (ρ (chartPairSnd U' U')).symm
  -- purity: the images of the charts capture the relative assassin near `v'`
  let O : Set E'.X := ⋃ j, Set.range (h' j)
  have hO : IsOpen O := isOpen_iUnion fun j ↦ (h' j).isOpenMap.isOpen_range
  have hvO : E'.f ⁻¹' {Nb.point} ⊆ O := by
    intro x hx
    have hx' : φ.hom x ∈ pullback.snd E.f Nb.toBase ⁻¹' {Nb.point} := by
      change (φ.hom ≫ pullback.snd E.f Nb.toBase) x = Nb.point
      rwa [show φ.hom ≫ pullback.snd E.f Nb.toBase = E'.f from
        D.stageChartIsoPullback_hom_snd n β U]
    obtain ⟨j, w, hw⟩ := Set.mem_iUnion.1 (hcov hx')
    refine Set.mem_iUnion.2 ⟨j, w, ?_⟩
    change φ.inv (h j w) = x
    rw [hw]
    exact congrFun (congrArg (fun k : E'.X ⟶ E'.X ↦ (k : E'.X → E'.X)) φ.hom_inv_id) x
  obtain ⟨W₀, hW₀o, hvW₀, hW₀⟩ := D.exists_isOpen_relativeAssassin_subset_image hf hF hpure n V'
    hNbaff hqfV' U' hU's hE'aff Nb.point O hO hvO
  -- each chart is represented near `v'`, by Stacks 05UF
  have hloc (i : Fin m) : ∃ W : E''.S.Opens, Nb.point ∈ W ∧
      IsCutOutByMonoFP (fun T : Over W.toScheme ↦
        (E''.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange ((Over.map W.ι).obj T)) := by
    let G := (Scheme.Modules.pullback (h i ≫ pullback.fst E.f Nb.toBase)).obj E.F
    let eC : (E''.etaleChart (h i)).F ≅ G :=
      (Scheme.Modules.pullbackComp (h i) (pullback.fst E.f Nb.toBase)).app E.F
    let C : _root_.AlgebraicGeometry.FlatDimensionSituation.{u} :=
      { E''.etaleChart (h i) with F := G, isQuasicoherent := hq i, isFiniteType := ht i }
    have hiff (T : Over E''.S) : (E''.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange T ↔
        C.IsFlatInDimensionsGEAfterBaseChange T :=
      (E''.etaleChart (h i)).isFlat_iff_of_moduleIso G eC T
    have hflatE'' : _root_.AlgebraicGeometry.IsFlatOverInDimensionsGE E''.f E''.F (n + 1) :=
      _root_.AlgebraicGeometry.IsFlatOverInDimensionsGE.of_isPullback
        (IsPullback.of_hasPullback E.f Nb.toBase) E.F _ hflatE
    obtain ⟨d⟩ := hdev i
    cases d with
    | empty hz =>
      refine ⟨⊤, trivial, IsCutOutByMonoFP.of_forall fun T ↦ (hiff _).mpr ?_⟩
      exact C.isFlat_of_isFlatOverInDimensionsGE
        (_root_.AlgebraicGeometry.isFlatOverInDimensionsGE_of_isZero C.f C.F hz C.n) _
    | nonempty data =>
      have : IsAffine (Yj i) := isAffine_source_of_devissageChain data.chain
      have hfpC : FinitePresentation C.f :=
        FinitePresentation.mk inferInstance inferInstance inferInstance
      have hflatC : _root_.AlgebraicGeometry.IsFlatOverInDimensionsGE C.f C.F (C.n + 1) :=
        (_root_.AlgebraicGeometry.isFlatOverInDimensionsGE_iff_of_moduleIso _ eC _).mp
          (hflatE''.etale_comp (h i) E''.f E''.F)
      obtain ⟨W, hsW, Z, hm, hfp, ⟨e⟩⟩ :=
        C.exists_mono_finitePresentation_representableBy Nb.point ⟨.nonempty data⟩ hfpC hflatC
      exact ⟨W, hsW, (C.isCutOutByMonoFP_of_representableBy W hm hfp e).of_iff
        fun T ↦ (hiff _).symm⟩
  choose W hsW hW using hloc
  let V₀ : E''.S.Opens := ⟨W₀, hW₀o⟩ ⊓ ⨅ i, W i
  have hV₀W (i : Fin m) : V₀ ≤ W i := inf_le_right.trans (iInf_le _ i)
  have hV₀W₀ : (V₀ : Set E''.S) ⊆ W₀ := fun x hx ↦ hx.1
  have hsV₀ : Nb.point ∈ V₀ := by
    refine ⟨hvW₀, ?_⟩
    change Nb.point ∈ ((⨅ i, W i : E''.S.Opens) : Set E''.S)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hsW
  have hcharts (i : Fin m) : IsCutOutByMonoFP (fun T : Over V₀.toScheme ↦
      (E''.etaleChart (h i)).IsFlatInDimensionsGEAfterBaseChange ((Over.map V₀.ι).obj T)) := by
    refine ((hW i).baseChange (E''.S.homOfLE (hV₀W i))).of_iff fun T ↦ ?_
    refine (E''.etaleChart (h i)).isFlat_mk_congr ?_
    change (T.hom ≫ E''.S.homOfLE (hV₀W i)) ≫ (W i).ι = T.hom ≫ V₀.ι
    rw [Category.assoc, Scheme.homOfLE_ι]
  have hV₀ : IsCutOutByMonoFP (fun T : Over V₀.toScheme ↦
      E''.IsFlatInDimensionsGEAfterBaseChange ((Over.map V₀.ι).obj T)) := by
    refine (IsCutOutByMonoFP.finite_inf hcharts).of_iff fun T ↦ ?_
    refine Iff.trans ?_ (hE'iff _)
    refine Iff.trans ?_ (E'.isFlat_iff_forall_etaleChart_of_relation p₁ p₂ hp eR h' _ ?_).symm
    · exact forall_congr' fun j ↦ (hchart j _).symm
    · rintro x hx ⟨t, ht⟩
      have hxW : E'.f x ∈ W₀ := by
        rw [← ht]
        exact hV₀W₀ (T.hom t).2
      obtain ⟨a, haO, ha⟩ := hW₀ x hx hxW
      obtain ⟨j, w, rfl⟩ := Set.mem_iUnion.1 haO
      obtain ⟨r, hr₁, hr₂⟩ := exists_chartPair_point U' U' _ x ha
      exact ⟨j, w, r, hr₁.symm, hr₂⟩
  refine ⟨V₀.toScheme, V₀.ι ≫ Nb.toBase, inferInstance, ⟨⟨Nb.point, hsV₀⟩, Nb.map_point⟩, ?_⟩
  rw [E.isCutOutByMonoFP_comp_iff]
  exact hV₀.of_iff fun T ↦ E.baseChange_isFlat_iff Nb.toBase _

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
