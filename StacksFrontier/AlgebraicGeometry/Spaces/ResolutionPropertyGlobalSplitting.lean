module

public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyLocalSplitting

/-!
# The split section of `π_*𝒪_Y` over the whole chart `V`, through `π_*(ℐ^m)`

In the situation of [Stacks, Tag 0GUY] the étale neighbourhood that the proof of
[Stacks, Tag 0GUZ] chooses near a point of `V` can be taken to be the chart `V` itself, with the
étale morphism `φ = j ≫ π : V ⟶ X`: the base change `V ×_X Y` is the disjoint union of the graph
of `j`, which maps isomorphically onto `V` and into `j(V)`, and of its complement.  So there is
**one** split section `ε : 𝒪_V ⟶ (π_*𝒪_Y)|_V` — the indicator of the graph — factoring through
`(π_*(ℐ^m))|_V` for every `m`.

`AlgebraicGeometry.Space.exists_etale_split_section_factorsThrough_idealSheafPow` produces the
same data with the étale neighbourhood left existential; here the neighbourhood is the affine
chart, which is what a statement about sections over an affine chart needs.

## Main results

* `AlgebraicGeometry.Space.exists_clopen_decomposition_graph`: the decomposition of `A ×_Y X`
  along the graph of an open immersion `a : A ⟶ X` with `a ≫ f` étale and `f` separated.
* `AlgebraicGeometry.Space.exists_chart_split_section_factorsThrough_idealSheafPow`: the split
  section over the chart.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **The decomposition of `A ×_Y X` along the graph of an open immersion.**  Let `f : X ⟶ Y` be
a separated morphism of algebraic spaces over `S` and `a : A ⟶ X` an open immersion with `a ≫ f`
étale.  Then `A ×_Y X` (the base change of `f` along `a ≫ f`) is the disjoint union of two open
and closed subspaces `W` and `V`, with `V ⟶ A` an isomorphism and `V ⟶ X` factoring through `a`.

This is the decomposition of
`AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_factorsThrough` with the étale
neighbourhood `A` itself, which that statement leaves existential. -/
theorem exists_clopen_decomposition_graph
    {A X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hsep : IsSeparated B S hS f)
    (a : A ⟶ X) (ha : IsOpenImmersion B S hS a) (haf : IsEtale B S hS (a ≫ f)) :
    ∃ (W V : Subfunctor (pullback (a ≫ f) f)),
      IsOpenSubspace B S hS W ∧
      IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧
      IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor (pullback (a ≫ f) f)).sheafify (BigFppfOver.topology B S hS) ∧
      IsIso (V.ι ≫ pullback.fst (a ≫ f) f) ∧
      (∃ t : V.toFunctor ⟶ A, t ≫ a = V.ι ≫ pullback.snd (a ≫ f) f) := by
  have hcomm : 𝟙 A ≫ (a ≫ f) = a ≫ f := Category.id_comp _
  have hΓfst : pullback.lift (𝟙 A) a hcomm ≫ pullback.fst (a ≫ f) f = 𝟙 A :=
    pullback.lift_fst _ _ _
  have hΓsnd : pullback.lift (𝟙 A) a hcomm ≫ pullback.snd (a ≫ f) f = a :=
    pullback.lift_snd _ _ _
  have hΓopen : IsOpenImmersion B S hS (pullback.lift (𝟙 A) a hcomm) :=
    isOpenImmersion_pullbackLift_id_of_isEtale B S hS hX hY hA hcomm haf ha
  have hΓclosed : IsClosedImmersion B S hS (pullback.lift (𝟙 A) a hcomm) :=
    isClosedImmersion_of_isSeparated_of_section B S hS (pullback.fst (a ≫ f) f)
      (isSeparated_pullbackFst B S hS (a ≫ f) hsep)
      (pullback.lift (𝟙 A) a hcomm) hΓfst
  have hP : IsAlgebraicSpace B S hS (pullback (a ≫ f) f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (a ≫ f) f hA hX hY
  have hVo : IsOpenSubspace B S hS (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)) :=
    isOpenSubspace_subfunctorRange B S hS hA hΓopen
  have hVc : IsClosedSubspace B S hS (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)) :=
    isClosedSubspace_range_of_isClosedImmersion B S hS _ hA hΓclosed
  have hiso : IsIso ((Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι ≫
      pullback.fst (a ≫ f) f) :=
    isIso_range_ι_comp_pullbackFst_pullbackLift_id B S hS hcomm
  have hmono : Mono (pullback.lift (𝟙 A) a hcomm) := mono_of_mono_fac hΓfst
  have hfac : ((Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι ≫
        pullback.fst (a ≫ f) f) ≫ a =
      (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι ≫ pullback.snd (a ≫ f) f := by
    refine (cancel_epi (Subfunctor.toRange (pullback.lift (𝟙 A) a hcomm))).1 ?_
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Subfunctor.toRange_ι,
      hΓfst, hΓsnd, Category.id_comp]
  obtain ⟨T, hTdef⟩ : ∃ T : Set (points B S hS (pullback (a ≫ f) f)),
      T = Set.range (pointsMap B S hS
        (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).toFunctor
        (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι) := ⟨_, rfl⟩
  have hTo : IsOpen T :=
    hTdef ▸ isOpen_range_pointsMap_of_isOpenImmersion B S hS
      (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι hVo.2
  have hTc : IsClosed T :=
    hTdef ▸ isClosed_range_pointsMap_of_isClosedImmersion B S hS hP
      (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι hVc.2
  have hVeq : Subfunctor.range (pullback.lift (𝟙 A) a hcomm) =
      openSubspaceOfPoints B S hS (pullback (a ≫ f) f) T := by
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openSubspaceOfPoints B S hS hP T hTo) ?_)
      (le_of_range_pointsMap_ι_subset B S hS hVo ?_) <;>
      rw [range_pointsMap_ι_openSubspaceOfPoints, hTdef]
  rw [hVeq] at hVo hVc hiso hfac
  exact ⟨openSubspaceOfPoints B S hS (pullback (a ≫ f) f) Tᶜ,
    openSubspaceOfPoints B S hS (pullback (a ≫ f) f) T,
    isOpenSubspace_openSubspaceOfPoints B S hS hP Tᶜ hTc.isOpen_compl,
    isClosedSubspace_openSubspaceOfPoints B S hS hP Tᶜ hTc.isOpen_compl hTo.isClosed_compl,
    hVo, hVc, sheafify_sup_openSubspaceOfPoints_eq_top B S hS T hTo hTc,
    inf_openSubspaceOfPoints_eq_sheafify_bot B S hS T, hiso, ⟨_, hfac⟩⟩

variable (hZ : B.Contains (⊤_ Scheme.{u}))

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- The chart `V` of the situation of Stacks 0GUY, as an algebraic space. -/
abbrev ResolutionPropertyDescentSituation.chartSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj D.V, isAlgebraicSpace_yoneda B S hS D.V⟩

/-- The étale morphism `φ = j ≫ π : V ⟶ X` of the situation of Stacks 0GUY, as a morphism of
algebraic spaces. -/
abbrev ResolutionPropertyDescentSituation.chartHom :
    D.chartSpace B S hS hZ X hqc hqs ⟶ X :=
  ObjectProperty.homMk (D.j ≫ D.π)

/-- The morphism `φ : V ⟶ X` of the situation of Stacks 0GUY is étale. -/
theorem ResolutionPropertyDescentSituation.isEtale_chartHom :
    IsEtale B S hS (D.chartHom B S hS hZ X hqc hqs).hom := by
  show IsEtale B S hS (D.j ≫ D.π)
  rw [D.comp_eq]
  exact D.isEtale_φ

/-- **Over the whole chart `V` there is one split section `ε : 𝒪_V ⟶ (π_*𝒪_Y)|_V` factoring through
`(π_*(ℐ^m))|_V` for every `m`.**  The base change `V ×_X Y` splits off the graph of `j`
(`AlgebraicGeometry.Space.exists_clopen_decomposition_graph`), which maps isomorphically onto `V`
and through `j`, and `ℐ^m` is the unit ideal there; the indicator of the graph and the restriction
to it are the section and its retraction of
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenSplitSection.lean`. -/
theorem exists_chart_split_section_factorsThrough_idealSheafPow :
    ∃ (ε : SheafOfModules.unit (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)) ⟶
          (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
            (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
            (directImageAlgebraUnitModule B S hS (D.piHom B S hS hZ X hqc hqs)))
        (pr : (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
            (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
            (directImageAlgebraUnitModule B S hS (D.piHom B S hS hZ X hqc hqs)) ⟶
          SheafOfModules.unit (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs))),
        ε ≫ pr = 𝟙 _ ∧
        ∀ m : ℕ, ∃ (εK : SheafOfModules.unit
            (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)) ⟶
          (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
            (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
            ((modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).obj
              (SheafOfModules.idealSheafPow D.I m).toSheafOfModules)),
        (εK ≫ (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
            (D.isEtale_chartHom B S hS hZ X hqc hqs)).map
            ((modulePushforward B S hS (D.piHom B S hS hZ X hqc hqs)).map
              (SheafOfModules.idealSheafPow D.I m).ι) :
          SheafOfModules.unit (structureRingSheaf B S hS (D.chartSpace B S hS hZ X hqc hqs)) ⟶
            (etaleModulePullback B S hS (D.chartHom B S hS hZ X hqc hqs)
              (D.isEtale_chartHom B S hS hZ X hqc hqs)).obj
              (pushforwardStructureModule B S hS (D.piHom B S hS hZ X hqc hqs))) = ε := by
  obtain ⟨W, WV, hWo, hWc, hWVo, hWVc, hsup, hinf, hiso, ⟨t, ht⟩⟩ :=
    exists_clopen_decomposition_graph B S hS (isAlgebraicSpace_yoneda B S hS D.V) D.Y.2 X.2 D.π
      (isSeparated_of_isFinite B S hS D.π D.Y.2 X.2 D.isFinite_π)
      D.j D.isOpenImmersion_j (D.comp_eq ▸ D.isEtale_φ)
  let Usp := D.chartSpace B S hS hZ X hqc hqs
  let gsp := D.chartHom B S hS hZ X hqc hqs
  have hg := D.isEtale_chartHom B S hS hZ X hqc hqs
  let π := D.piHom B S hS hZ X hqc hqs
  let P : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS gsp π
  let pP : P ⟶ Usp := ObjectProperty.homMk (pullback.fst gsp.hom π.hom)
  let iP : P ⟶ D.Y := ObjectProperty.homMk (pullback.snd gsp.hom π.hom)
  have sqP : IsPullback iP pP π gsp := (AlgebraicSpaces.isPullback_fiberProduct B S hS gsp π).flip
  let Wsp : AlgebraicSpaces B S hS := ⟨W.toFunctor, hWo.1⟩
  let WVsp : AlgebraicSpaces B S hS := ⟨WV.toFunctor, hWVo.1⟩
  let a : WVsp ⟶ P := ObjectProperty.homMk WV.ι
  let a' : Wsp ⟶ P := ObjectProperty.homMk W.ι
  have hcov : Set.range (pointsMap B S hS WVsp.1 a.hom) ∪
      Set.range (pointsMap B S hS Wsp.1 a'.hom) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    rcases mem_range_pointsMap_ι_or_of_sheafify_sup_eq_top B S hS W WV hsup z with hz | hz
    · exact Or.inr hz
    · exact Or.inl hz
  have hdisj : Disjoint (Set.range (pointsMap B S hS WVsp.1 a.hom))
      (Set.range (pointsMap B S hS Wsp.1 a'.hom)) :=
    disjoint_range_pointsMap_ι_of_inf_eq_sheafify_bot B S hS WV W (by rw [inf_comm]; exact hinf)
  have haE : IsEtale B S hS a.hom := isEtale_of_isOpenImmersion B S hS hWVo.2
  have ha'E : IsEtale B S hS a'.hom := isEtale_of_isOpenImmersion B S hS hWo.2
  have : IsIso (a ≫ pP) := by
    have h : IsIso ((ObjectProperty.ι _).map (a ≫ pP)) := hiso
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  have hiE : IsEtale B S hS iP.hom := isEtale_of_isPullback B S hS pP iP gsp π sqP.flip hg
  have hai : IsEtale B S hS (a ≫ iP).hom := fun T φ hφ => by
    have h := hiE T (φ ≫ a.hom) (haE T φ hφ)
    rwa [Category.assoc] at h
  have hK' : ∀ m : ℕ, IsIso ((modulePullback B S hS a).map ((etaleModulePullback B S hS iP
      (isEtale_of_isPullback B S hS pP iP gsp π sqP.flip hg)).map
        (SheafOfModules.idealSheafPow D.I m).ι)) := fun m =>
    isIso_modulePullback_map_etaleModulePullback_map B S hS a iP _ hai _
      (isIso_etaleModulePullback_map_idealSheafPow_ι_of_comp_eq_chart B S hS hZ X hqc hqs D
        (a ≫ iP) hai t ht m)
  exact exists_split_section_factorsThrough_idealSheafPow_of_clopen B S hS π gsp hg iP pP sqP
    a a' haE ha'E hWVc.2 hWc.2 hcov hdisj D.I hK'

end AlgebraicGeometry.Space

end
