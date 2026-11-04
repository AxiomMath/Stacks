module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Descending flatness of a module along a limit of base changes

Let `X₀` be an algebraic space over `S` and `T : I ⥤ (Sch/S)` a cofiltered system of affine
schemes over `S` with limit `c`. For a quasi-coherent module `𝒢` of finite presentation on a
base change `h_{T i₀} ⨯ X₀` whose pullback to `h_{c.pt} ⨯ X₀` is flat over `c.pt`, the pullback of
`𝒢` to some `h_{T j} ⨯ X₀` is already flat over `T j`, provided `X₀` is locally of finite
presentation over `S`. This is Limits of Spaces, Lemma 70.6.12.

## Main definitions

* `AlgebraicGeometry.Space.productChartMap`: the chart `U₀ ×_{T₀} V ⟶ h_V ⨯ X₀` obtained from
  a chart `U₀ ⟶ h_{T₀} ⨯ X₀` and a morphism `V ⟶ T₀`.
* `AlgebraicGeometry.Space.productChartDiagram`: the commuting square of étale charts of the
  projection `h_V ⨯ X₀ ⟶ h_V` it forms with the identity chart of `V`.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_productSpaceFst_iff`: flatness over `V` of the pullback of
  a quasi-coherent module to `h_V ⨯ X₀` is flatness over `V` of the Zariski pullback of its
  restriction to `U₀`.
* `AlgebraicGeometry.eventually_isFlatOver_pullback_snd`: for a cofiltered system `E` of affine
  schemes with limit `c` and `f : X ⟶ E i` locally of finite presentation, flatness over `c.pt`
  of the pullback of a quasi-coherent module of finite presentation to `X ×_{E i} c.pt` descends
  to flatness over `E j` of its pullback to some `X ×_{E i} E j`.
* `AlgebraicGeometry.Space.eventually_isFlatOver_productSpaceFst`: flatness over `c.pt` of the
  pullback of `𝒢` to `h_{c.pt} ⨯ X₀` descends to flatness over `T j` of its pullback to some
  `h_{T j} ⨯ X₀`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)
  {T₀ : BigFppfOver B S hS} {U₀ : BigFppfOver B S hS}
  (a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ T₀).1)

/-! ### Charts of the base changes -/

/-- The structure morphism `U₀ ⟶ T₀` of a scheme over the base change `h_{T₀} ⨯ X₀`. -/
noncomputable def productChartBase : U₀ ⟶ T₀ :=
  Yoneda.fullyFaithful.preimage (a₀ ≫ prod.fst)

/-- The image of `productChartBase X₀ a₀` under the Yoneda embedding is `a₀ ≫ prod.fst`. -/
theorem yoneda_map_productChartBase :
    yoneda.map (productChartBase X₀ a₀) = a₀ ≫ prod.fst :=
  Yoneda.fullyFaithful.map_preimage _

/-- The base change `U₀ ×_{T₀} V ⟶ h_V ⨯ X₀` of a morphism `U₀ ⟶ h_{T₀} ⨯ X₀` along the
morphism `h_V ⨯ X₀ ⟶ h_{T₀} ⨯ X₀` induced by `k : V ⟶ T₀`. -/
noncomputable def productChartMap {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    yoneda.obj (pullback (productChartBase X₀ a₀) k) ⟶ (productSpace X₀ V).1 :=
  prod.lift (yoneda.map (pullback.snd _ _)) (yoneda.map (pullback.fst _ _) ≫ a₀ ≫ prod.snd)

/-- The chart `productChartMap X₀ a₀ k` followed by the first projection is the image of the
second projection `U₀ ×_{T₀} V ⟶ V` under the Yoneda embedding. -/
theorem productChartMap_fst {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartMap X₀ a₀ k ≫ prod.fst = yoneda.map (pullback.snd _ _) :=
  prod.lift_fst _ _

/-- The chart of `h_V ⨯ X₀` is the base change of the chart of `h_{T₀} ⨯ X₀`. -/
theorem isPullback_productChartMap {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    IsPullback (yoneda.map (pullback.fst (productChartBase X₀ a₀) k)) (productChartMap X₀ a₀ k)
      a₀ (productSpaceMap X₀ k).hom := by
  have hbig : IsPullback (yoneda.map (pullback.fst (productChartBase X₀ a₀) k))
      (productChartMap X₀ a₀ k ≫ prod.fst) (a₀ ≫ prod.fst) (yoneda.map k) := by
    rw [productChartMap_fst, ← yoneda_map_productChartBase]
    exact (IsPullback.of_hasPullback (productChartBase X₀ a₀) k).map yoneda
  refine IsPullback.of_bot hbig ?_ (isPullback_productSpaceMap X₀ k)
  apply prod.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (yoneda_map_productChartBase X₀ a₀).symm).trans
      ((yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map pullback.condition).trans
        ((yoneda.map_comp _ _).trans ((congrArg (· ≫ _) (productChartMap_fst X₀ a₀ k).symm).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (prod.map_fst _ _).symm).trans
            (Category.assoc _ _ _).symm)))))))
  · exact (Category.assoc _ _ _).trans ((prod.lift_snd _ _).symm.trans
      ((congrArg (_ ≫ ·) ((prod.map_snd _ _).trans (Category.comp_id _)).symm).trans
        (Category.assoc _ _ _).symm))

variable {a₀}

/-- A property of schemes stable under base change passes from a chart to its base change. -/
private theorem presheaf_productChartMap (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (h : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf a₀)
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (productChartMap X₀ a₀ k) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_productChartMap X₀ a₀ k) h

/-- The base change of an étale chart is an étale chart. -/
theorem productChartMap_etale
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (productChartMap X₀ a₀ k) :=
  presheaf_productChartMap X₀ _ ha₀ k

/-- The base change of a surjective chart is surjective. -/
theorem productChartMap_surjective
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (productChartMap X₀ a₀ k) :=
  presheaf_productChartMap X₀ _ hs₀ k

variable (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)

/-- The chart `U₀ ⟶ h_{T₀} ⨯ X₀` as an object of the small étale site. -/
noncomputable def productBaseChart : SmallEtale B S hS (productSpace X₀ T₀).1 :=
  ⟨CostructuredArrow.mk a₀, ha₀⟩

/-- The chart `U₀ ×_{T₀} V ⟶ h_V ⨯ X₀` as an object of the small étale site. -/
noncomputable def productChart {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    SmallEtale B S hS (productSpace X₀ V).1 :=
  ⟨CostructuredArrow.mk (productChartMap X₀ a₀ k), productChartMap_etale X₀ ha₀ k⟩

/-- The commuting square of étale charts of the projection `h_V ⨯ X₀ ⟶ h_V` formed by the chart
`U₀ ×_{T₀} V` and the identity chart of `V`. -/
noncomputable def productChartDiagram {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    ChartDiagram B S hS (productSpace X₀ V).1 (schemeSpace V).1 (productSpaceFst X₀ V).hom where
  U := productChart X₀ ha₀ k
  V := idEtaleChart B S hS V
  g := pullback.snd _ _
  comm := (productChartMap_fst X₀ a₀ k).trans (Category.comp_id _).symm

/-! ### Flatness on the charts -/

/-- **Flatness over `V` of the pullback of a quasi-coherent module to `h_V ⨯ X₀` is flatness of
the Zariski pullback of its restriction to the chart `U₀` over `V`.** -/
theorem isFlatOver_productSpaceFst_iff
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    (G : Modules.{u, u} B S hS (productSpace X₀ T₀).1 (productSpace X₀ T₀).2)
    (hG : G.IsQuasicoherentOnSite) {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    IsFlatOver B S hS (productSpace X₀ V).2 (productSpaceFst X₀ V).hom
        ((modulePullback B S hS (productSpaceMap X₀ k)).obj G) ↔
      AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map
          (pullback.snd (productChartBase X₀ a₀) k)).toLRSHom.toShHom
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
            (pullback.fst (productChartBase X₀ a₀) k))).obj
          (restrictToChart B S hS (productSpace X₀ T₀).2 G (productBaseChart X₀ ha₀))) := by
  have : ((modulePullback B S hS (productSpaceMap X₀ k)).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hG
  let e := restrictToChartBaseChangeIso B S hS (productSpaceMap X₀ k) G hG
    (productBaseChart X₀ ha₀) (productChart X₀ ha₀ k) (pullback.fst _ _)
    (isPullback_productChartMap X₀ a₀ k).w
  have hd : IsFlatOverOnChartDiagram B S hS (productSpace X₀ V).2
        ((modulePullback B S hS (productSpaceMap X₀ k)).obj G) (productChartDiagram X₀ ha₀ k) ↔
      AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map
          (pullback.snd (productChartBase X₀ a₀) k)).toLRSHom.toShHom
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
            (pullback.fst (productChartBase X₀ a₀) k))).obj
          (restrictToChart B S hS (productSpace X₀ T₀).2 G (productBaseChart X₀ ha₀))) :=
    forall_congr' fun x => (flatOverAt_iff_of_iso _ e x).symm
  refine ⟨fun h => hd.1 (h _), fun h => ?_⟩
  refine (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (productSpaceFst X₀ V) _).2
    fun xbar => isFlatOver_of_isFlatOverOnChartDiagram_of_surjective B S hS
      (productSpaceFst X₀ V) _ (productChartDiagram X₀ ha₀ k) ?_ (hd.2 h) xbar
  exact (surjective_iff_surjective_pointsMap B S hS _ (productSpace X₀ V).2 _ _).mp
    (productChartMap_surjective X₀ hs₀ k)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

open RingedSpaceModuleAdjunction

/-- **Flatness of a module of finite presentation over the second factor descends along a
limit.** Let `E` be a cofiltered system of affine schemes with limit `c`, `f : X ⟶ E i` a
morphism locally of finite presentation from an affine scheme and `F` a quasi-coherent module of
finite presentation on `X`. If the pullback of `F` to `X ×_{E i} c.pt` is flat over `c.pt`, then
its pullback to some `X ×_{E i} E j` is flat over `E j`. -/
theorem eventually_isFlatOver_pullback_snd {J : Type u} [Category.{u} J] [IsCofiltered J]
    (E : J ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c) [∀ j, IsAffine (E.obj j)] (i : J)
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ E.obj i) [LocallyOfFinitePresentation f]
    (F : X.Modules) (hF : F.IsQuasicoherent) (hF' : F.IsFinitePresentation)
    (hflat : IsFlatOver (pullback.snd f (c.π.app i)).toLRSHom.toShHom
      ((modulePullback (pullback.fst f (c.π.app i)).toLRSHom.toShHom).obj F)) :
    ∃ (j : J) (e : j ⟶ i), IsFlatOver (pullback.snd f (E.map e)).toLRSHom.toShHom
      ((modulePullback (pullback.fst f (E.map e)).toLRSHom.toShHom).obj F) := by
  let f₀ : Over.mk f ⟶ Over.mk (𝟙 (E.obj i)) := Over.homMk f (by simp)
  have hfpX : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have hfpY : FinitePresentation (𝟙 (E.obj i)) := ⟨inferInstance, inferInstance, inferInstance⟩
  let F' : SheafOfModules.{u} (structureSheafRing (Over.mk f).left.toRingedSpace) := F
  have : F'.IsQuasicoherent := hF
  have : F'.IsFinitePresentation := hF'
  obtain ⟨j, e, he⟩ := eventually_isFlatOver_modulePullback E c hc i (Over.mk f)
    (Over.mk (𝟙 (E.obj i))) hfpX hfpY f₀ F'
    ((isFlatOver_overPullback_map_iff (Over.mk f) (c.π.app i) _).mpr hflat)
  exact ⟨j, e, (isFlatOver_overPullback_map_iff (Over.mk f) (E.map e) _).mp he⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

open RingedSpaceModuleAdjunction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)

/-- The flatness condition on the chart `U₀ ×_{T₀} V` of `h_V ⨯ X₀`, read on the fibre product
of schemes. -/
private theorem isFlatOver_productSpaceFst_iff_scheme {T₀ U₀ : BigFppfOver B S hS}
    {a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ T₀).1}
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    (G : Modules.{u, u} B S hS (productSpace X₀ T₀).1 (productSpace X₀ T₀).2)
    (hG : G.IsQuasicoherentOnSite) {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    IsFlatOver B S hS (productSpace X₀ V).2 (productSpaceFst X₀ V).hom
        ((modulePullback B S hS (productSpaceMap X₀ k)).obj G) ↔
      AlgebraicGeometry.IsFlatOver
        (pullback.snd ((BigFppfOver.toScheme B S hS).map (productChartBase X₀ a₀))
          ((BigFppfOver.toScheme B S hS).map k)).toLRSHom.toShHom
        ((RingedSpaceModuleAdjunction.modulePullback
            (pullback.fst ((BigFppfOver.toScheme B S hS).map (productChartBase X₀ a₀))
              ((BigFppfOver.toScheme B S hS).map k)).toLRSHom.toShHom).obj
          (restrictToChart B S hS (productSpace X₀ T₀).2 G (productBaseChart X₀ ha₀))) :=
  have hq :
      (restrictToChart B S hS (productSpace X₀ T₀).2 G (productBaseChart X₀ ha₀)).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS (productSpace X₀ T₀) G hG _
  let e := PreservesPullback.iso (BigFppfOver.toScheme B S hS) (productChartBase X₀ a₀) k
  (isFlatOver_productSpaceFst_iff X₀ ha₀ hs₀ G hG k).trans <| by
    rw [← PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) (productChartBase X₀ a₀) k,
      ← PreservesPullback.iso_hom_snd (BigFppfOver.toScheme B S hS) (productChartBase X₀ a₀) k]
    exact (@isFlatOver_pullback_iff_of_iso _ _ _ _ _ _ e _ hq).symm.trans
      (isFlatOver_iff_of_moduleIso _ ((Stacks.ProjectiveBundleQuotients.pullbackIso _).app _))

/-- **Flatness of a module descends along a limit of base changes.** Let `T` be a cofiltered
system of affine schemes over `S` with limit `c`, and `𝒢` a quasi-coherent module of finite
presentation on `h_{T i₀} ⨯ X₀`, which is quasi-compact and locally of finite presentation over
`T i₀`. If the pullback of `𝒢` to `h_{c.pt} ⨯ X₀` is flat over `c.pt`, then its pullback to some
`h_{T j} ⨯ X₀` is flat over `T j`. -/
theorem eventually_isFlatOver_productSpaceFst {I : Type u} [Category.{u} I] [IsCofiltered I]
    (T : I ⥤ BigFppfOver B S hS) [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (c : Cone T) (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (i₀ : I)
    (hqc : IsQuasiCompactSpace B S hS (productSpace X₀ (T.obj i₀)).1)
    (hlfp : IsLocallyOfFinitePresentation B S hS (productSpaceFst X₀ (T.obj i₀)).hom)
    (G : Modules.{u, u} B S hS (productSpace X₀ (T.obj i₀)).1 (productSpace X₀ (T.obj i₀)).2)
    (hG : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (hflat : IsFlatOver B S hS (productSpace X₀ c.pt).2 (productSpaceFst X₀ c.pt).hom
      ((modulePullback B S hS (productSpaceMap X₀ (c.π.app i₀))).obj G)) :
    ∃ (j : I) (e : j ⟶ i₀), IsFlatOver B S hS (productSpace X₀ (T.obj j)).2
      (productSpaceFst X₀ (T.obj j)).hom
      ((modulePullback B S hS (productSpaceMap X₀ (T.map e))).obj G) := by
  obtain ⟨U₀, a₀, hU₀, hs₀, ha₀'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _
      (productSpace X₀ (T.obj i₀)).2).mp hqc
  have ha₀ := (isEtale_iff_presheaf_of_yoneda B S hS a₀).mp ha₀'
  have : ∀ j, IsAffine ((T ⋙ BigFppfOver.toScheme B S hS).obj j) := fun j =>
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj j)))
  have : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (productChartBase X₀ a₀)) :=
    hlfp U₀ (T.obj i₀) a₀ (𝟙 _) (productChartBase X₀ a₀) ha₀
      (idEtaleChart B S hS (T.obj i₀)).property
      ((Category.comp_id _).trans (yoneda_map_productChartBase X₀ a₀))
  let F₀ := restrictToChart B S hS (productSpace X₀ (T.obj i₀)).2 G (productBaseChart X₀ ha₀)
  have hF₀ : F₀.IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS (productSpace X₀ (T.obj i₀)) G hG _
  have hF₀' : F₀.IsFinitePresentation :=
    isFinitePresentation_restrictToChart B S hS (productSpace X₀ (T.obj i₀)) G hG hGfp _
  obtain ⟨j, e, he⟩ := eventually_isFlatOver_pullback_snd (T ⋙ BigFppfOver.toScheme B S hS)
    ((BigFppfOver.toScheme B S hS).mapCone c) hc i₀
    ((BigFppfOver.toScheme B S hS).map (productChartBase X₀ a₀)) F₀ hF₀ hF₀'
    ((isFlatOver_productSpaceFst_iff_scheme X₀ ha₀ hs₀ G hG (c.π.app i₀)).mp hflat)
  exact ⟨j, e, (isFlatOver_productSpaceFst_iff_scheme X₀ ha₀ hs₀ G hG (T.map e)).mpr he⟩

end AlgebraicGeometry.Space

end
