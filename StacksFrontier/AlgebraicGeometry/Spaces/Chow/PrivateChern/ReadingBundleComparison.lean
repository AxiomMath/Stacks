module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ReadingBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative

/-!
# The reading bundles over a scheme are the base changes of the projective bundle

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module and `π : 𝐏(ℰ) ⟶ X` its
projective bundle, glued over the presenting chart `U ⟶ X`. For a scheme `T` with a morphism
`ψ : T ⟶ X`, the projective bundle `𝐏(ℰ_ψ)` of the reading of `ℰ` on `T` maps to `𝐏(ℰ)` over `ψ`,
and the resulting square is cartesian: `𝐏(ℰ_ψ) = T ×_X 𝐏(ℰ)`.

## Main definitions

* `readingBundleToSpace`: The comparison morphism `𝐏(ℰ_T) ⟶ 𝐏(ℰ)`.

## Main results

* `readingBundleToSpace_comp_proj`: The comparison lies over `ψ`.
* `isPullback_readingBundleToSpace`: The square formed by the comparison, the two bundle
  projections and `ψ` is cartesian.
* `readingBundleSiteMap_comp_readingBundleToSpace`: The comparison is natural in `T`.
* `isPullback_projectiveBundleSpaceChart_relation`: The kernel pair of the chart `𝐏(ℰ_U) ⟶ 𝐏(ℰ)`
  is `𝐏(ℰ_R)`, where `R = U ×_X U`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

variable {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X)

/-- The fibre product `T' = T ×_X U` of `T` with the presenting chart of `X`, an object of the
site. -/
abbrev chartBaseChange : BigFppfOver B S hS :=
  (relativelyRepresentable_chartToSpace B S hS X (bundleBaseChart X)).pullback ψ.hom

/-- Its projection `T' ⟶ T`. -/
abbrev chartBaseChangeToBase : chartBaseChange ψ ⟶ T :=
  (relativelyRepresentable_chartToSpace B S hS X (bundleBaseChart X)).snd ψ.hom

/-- Its projection `T' ⟶ U` to the presenting chart. -/
def chartBaseChangeToChart :
    chartBaseChange ψ ⟶ (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X) :=
  Yoneda.fullyFaithful.preimage
    ((relativelyRepresentable_chartToSpace B S hS X (bundleBaseChart X)).fst ψ.hom)

/-- The Yoneda image of `T' ⟶ U` is the first projection of the fibre product `T ×_X U`. -/
theorem yoneda_map_chartBaseChangeToChart :
    yoneda.map (chartBaseChangeToChart ψ) =
      (relativelyRepresentable_chartToSpace B S hS X (bundleBaseChart X)).fst ψ.hom :=
  Yoneda.fullyFaithful.map_preimage _

/-- The square `T' = T ×_X U`. -/
theorem isPullback_chartBaseChange :
    IsPullback (yoneda.map (chartBaseChangeToChart ψ)) (yoneda.map (chartBaseChangeToBase ψ))
      (chartToSpace B S hS X (bundleBaseChart X)).hom ψ.hom := by
  rw [yoneda_map_chartBaseChangeToChart]
  exact (relativelyRepresentable_chartToSpace B S hS X (bundleBaseChart X)).isPullback ψ.hom

/-- The two morphisms `T' ⟶ X` agree. -/
theorem chartBaseChange_w :
    representedSpaceMap B S hS (chartBaseChangeToChart ψ) ≫
        chartToSpace B S hS X (bundleBaseChart X) =
      representedSpaceMap B S hS (chartBaseChangeToBase ψ) ≫ ψ :=
  ObjectProperty.hom_ext _ (isPullback_chartBaseChange ψ).w

/-! ### The relation of the presenting chart is identified by the glued chart -/

/-- The two composites `𝐏(ℰ_R) ⟶ 𝐏(ℰ_U) ⟶ 𝐏(ℰ)`, along the two projections of the relation
`R ⟶ U` of the presenting chart, agree. -/
theorem siteMap_bundleRelFst_comp_projectiveBundleSpaceChart (E : Modules.{u, u} B S hS X.1 X.2)
    [E.IsQuasicoherentOnSite] (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    yoneda.map ((projectiveBundleChartFamily E hfree).siteMap (presentationRelationTargetHom
        (projectiveBundlePresentation X))) ≫
        projectiveBundleChart E hfree =
      yoneda.map ((projectiveBundleChartFamily E hfree).siteMap (presentationRelationSourceHom
          (projectiveBundlePresentation X))) ≫
        projectiveBundleChart E hfree := by
  ext ⟨T'⟩ x
  show (projectiveBundleChart E hfree).app _ (x ≫ _) =
    (projectiveBundleChart E hfree).app _ (x ≫ _)
  refine Stacks.Groupoids.quotientChart_app_eq_of_rel _ _ _ _
    ⟨(Over.post B.inclusion).map x, ?_, ?_⟩
  · exact (congrArg ((Over.post B.inclusion).map x ≫ ·) (prod.lift_fst _ _)).trans
      ((Over.post B.inclusion).map_comp _ _).symm
  · exact (congrArg ((Over.post B.inclusion).map x ≫ ·) (prod.lift_snd _ _)).trans
      ((Over.post B.inclusion).map_comp _ _).symm

/-! ### The bundle over `T' = T ×_X U` and its kernel pair over `T` -/

/-- The base-change morphism only depends on the morphism of the site. -/
theorem readingBundleSiteMap_congr (E : Modules.{u, u} B S hS X.1 X.2) [E.IsQuasicoherentOnSite]
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) {T' T : BigFppfOver B S hS}
    {g₁ g₂ : T' ⟶ T} (hg : g₁ = g₂) {ψ₀ : representedAlgebraicSpace B S hS T ⟶ X}
    {ψ₁ : representedAlgebraicSpace B S hS T' ⟶ X}
    (w₁ : representedSpaceMap B S hS g₁ ≫ ψ₀ = ψ₁) (w₂ : representedSpaceMap B S hS g₂ ≫ ψ₀ = ψ₁) :
    readingBundleSiteMap E hfree g₁ w₁ = readingBundleSiteMap E hfree g₂ w₂ := by
  subst hg
  rfl

section Cover

variable (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The morphism `T' ⟶ X`. -/
abbrev chartBaseChangeToSpace : representedAlgebraicSpace B S hS (chartBaseChange ψ) ⟶ X :=
  representedSpaceMap B S hS (chartBaseChangeToBase ψ) ≫ ψ

/-- The base change `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)` of the bundle along `T' ⟶ T`. -/
abbrev bundleCover :
    readingBundleSite E hfree (chartBaseChangeToSpace ψ) ⟶ readingBundleSite E hfree ψ :=
  readingBundleSiteMap E hfree (chartBaseChangeToBase ψ) rfl

/-- The morphism `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U)` over `T' ⟶ U`. -/
abbrev bundleCoverToChart :
    readingBundleSite E hfree (chartBaseChangeToSpace ψ) ⟶
      (projectiveBundleChartFamily E hfree).site (bundleBaseChart X) :=
  readingBundleSiteMap E hfree (chartBaseChangeToChart ψ) (chartBaseChange_w ψ)

/-- The fibre product `T'' = T' ×_T T'`. -/
abbrev chartBaseChangePair : BigFppfOver B S hS :=
  pullback (chartBaseChangeToBase ψ) (chartBaseChangeToBase ψ)

/-- The morphism `T'' ⟶ X`. -/
abbrev chartBaseChangePairToSpace :
    representedAlgebraicSpace B S hS (chartBaseChangePair ψ) ⟶ X :=
  representedSpaceMap B S hS (pullback.fst _ _ ≫ chartBaseChangeToBase ψ) ≫ ψ

/-- The first projection `T'' ⟶ T'` followed by `T' ⟶ X` is `T'' ⟶ X`. -/
theorem representedSpaceMap_pullback_fst_comp :
    representedSpaceMap B S hS (pullback.fst (chartBaseChangeToBase ψ) (chartBaseChangeToBase ψ)) ≫
        chartBaseChangeToSpace ψ = chartBaseChangePairToSpace ψ :=
  by rw [← Category.assoc, representedSpaceMap_comp]

/-- The second projection `T'' ⟶ T'` followed by `T' ⟶ X` is `T'' ⟶ X`. -/
theorem representedSpaceMap_pullback_snd_comp :
    representedSpaceMap B S hS (pullback.snd (chartBaseChangeToBase ψ) (chartBaseChangeToBase ψ)) ≫
        chartBaseChangeToSpace ψ = chartBaseChangePairToSpace ψ :=
  by rw [← Category.assoc, representedSpaceMap_comp, ← pullback.condition]

/-- The first projection `𝐏(ℰ_{T''}) ⟶ 𝐏(ℰ_{T'})`, the base change along the first projection
`T'' ⟶ T'`. -/
abbrev bundleCoverPairFst :
    readingBundleSite E hfree (chartBaseChangePairToSpace ψ) ⟶
      readingBundleSite E hfree (chartBaseChangeToSpace ψ) :=
  readingBundleSiteMap E hfree (pullback.fst _ _) (representedSpaceMap_pullback_fst_comp ψ)

/-- The second projection `𝐏(ℰ_{T''}) ⟶ 𝐏(ℰ_{T'})`, the base change along the second projection
`T'' ⟶ T'`. -/
abbrev bundleCoverPairSnd :
    readingBundleSite E hfree (chartBaseChangePairToSpace ψ) ⟶
      readingBundleSite E hfree (chartBaseChangeToSpace ψ) :=
  readingBundleSiteMap E hfree (pullback.snd _ _) (representedSpaceMap_pullback_snd_comp ψ)

/-- **The kernel pair of `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)` is `𝐏(ℰ_{T''})`.** -/
theorem isPullback_bundleCoverPair :
    IsPullback (bundleCoverPairFst ψ E hfree) (bundleCoverPairSnd ψ E hfree)
      (bundleCover ψ E hfree) (bundleCover ψ E hfree) := by
  have hfst := isPullback_readingBundleSiteMap E hfree (pullback.fst _ _)
    (representedSpaceMap_pullback_fst_comp ψ)
  have hsnd := isPullback_readingBundleSiteMap E hfree (pullback.snd _ _)
    (representedSpaceMap_pullback_snd_comp ψ)
  have hcov := isPullback_readingBundleSiteMap E hfree (chartBaseChangeToBase ψ)
    (ψ := ψ) (ψ' := chartBaseChangeToSpace ψ) rfl
  have hcomp := hfst.paste_vert
    (IsPullback.of_hasPullback (chartBaseChangeToBase ψ) (chartBaseChangeToBase ψ))
  rw [← hsnd.w, ← hcov.w] at hcomp
  refine IsPullback.of_bot hcomp ?_ hcov
  have W₂ : representedSpaceMap B S hS (pullback.snd _ _ ≫ chartBaseChangeToBase ψ) ≫ ψ =
      chartBaseChangePairToSpace ψ := by
    rw [← pullback.condition]
  rw [readingBundleSiteMap_comp E hfree _ _ rfl _ rfl,
    readingBundleSiteMap_comp E hfree _ _ rfl _ W₂]
  exact readingBundleSiteMap_congr E hfree pullback.condition _ _

end Cover

/-! ### The cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)` is étale and surjective -/

section CoverProperties

variable (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The projection `T' = T ×_X U ⟶ T` is étale. -/
theorem etale_chartBaseChangeToBase :
    Etale ((BigFppfOver.toScheme B S hS).map (chartBaseChangeToBase ψ)) :=
  MorphismProperty.relative.property_snd (bundleBaseChart X).property ψ.hom

/-- The projection `T' = T ×_X U ⟶ T` is surjective. -/
theorem surjective_chartBaseChangeToBase :
    Surjective ((BigFppfOver.toScheme B S hS).map (chartBaseChangeToBase ψ)) :=
  MorphismProperty.relative.property_snd (projectiveBundlePresentation X).surjective ψ.hom

/-- The cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)` has any base-change stable property of `T' ⟶ T`. -/
private theorem presheaf_bundleCover_of_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (h : P ((BigFppfOver.toScheme B S hS).map (chartBaseChangeToBase ψ))) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (bundleCover ψ E hfree)) :=
  (presheaf_yoneda_map_iff B S hS inferInstance _).2
    (MorphismProperty.of_isPullback
      (isPullback_readingBundleMap E (chartBaseChangeToBase ψ) (ψ := ψ) rfl).flip h)

/-- The cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)` is étale. -/
theorem presheaf_etale_bundleCover :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (bundleCover ψ E hfree)) :=
  presheaf_bundleCover_of_property ψ E hfree _ (etale_chartBaseChangeToBase ψ)

/-- The cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)` is surjective. -/
theorem presheaf_surjective_bundleCover :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (bundleCover ψ E hfree)) :=
  presheaf_bundleCover_of_property ψ E hfree _ (surjective_chartBaseChangeToBase ψ)

end CoverProperties

/-! ### The comparison morphism `𝐏(ℰ_T) ⟶ 𝐏(ℰ)` over `T ⟶ X` -/

section Comparison

variable (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The two morphisms `T'' ⟶ U` agree after `U ⟶ X`. -/
theorem chartBaseChangePair_w :
    yoneda.map (pullback.fst (chartBaseChangeToBase ψ) (chartBaseChangeToBase ψ) ≫
        chartBaseChangeToChart ψ) ≫ (bundleBaseChart X).obj.hom =
      yoneda.map (pullback.snd (chartBaseChangeToBase ψ) (chartBaseChangeToBase ψ) ≫
        chartBaseChangeToChart ψ) ≫ (bundleBaseChart X).obj.hom := by
  have h := (isPullback_chartBaseChange ψ).w
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  show _ ≫ yoneda.map (chartBaseChangeToChart ψ) ≫ (chartToSpace B S hS X (bundleBaseChart
      X)).hom =
    _ ≫ yoneda.map (chartBaseChangeToChart ψ) ≫ (chartToSpace B S hS X (bundleBaseChart X)).hom
  rw [h, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    pullback.condition]

/-- The morphism `T'' ⟶ R` to the relation of the presenting chart. -/
def chartBaseChangePairToRelation :
    chartBaseChangePair ψ ⟶ (SmallEtale.toOver B S hS X.1).obj
      (presentationRelationChart (projectiveBundlePresentation X)) :=
  Yoneda.fullyFaithful.preimage
    ((isPullback_projectiveBundlePresentation X).lift _ _ (chartBaseChangePair_w ψ))

/-- `T'' ⟶ R` followed by the first projection `R ⟶ U` is `T'' ⟶ T' ⟶ U` along the first
projection. -/
theorem chartBaseChangePairToRelation_fst :
    chartBaseChangePairToRelation ψ ≫ (SmallEtale.toOver B S hS
        X.1).map (presentationRelationTargetHom (projectiveBundlePresentation X)) =
      pullback.fst _ _ ≫ chartBaseChangeToChart ψ :=
  yoneda.map_injective (by
    rw [Functor.map_comp, chartBaseChangePairToRelation, Functor.FullyFaithful.map_preimage,
      IsPullback.lift_fst])

/-- `T'' ⟶ R` followed by the second projection `R ⟶ U` is `T'' ⟶ T' ⟶ U` along the second
projection. -/
theorem chartBaseChangePairToRelation_snd :
    chartBaseChangePairToRelation ψ ≫ (SmallEtale.toOver B S hS
        X.1).map (presentationRelationSourceHom (projectiveBundlePresentation X)) =
      pullback.snd _ _ ≫ chartBaseChangeToChart ψ :=
  yoneda.map_injective (by
    rw [Functor.map_comp, chartBaseChangePairToRelation, Functor.FullyFaithful.map_preimage,
      IsPullback.lift_snd])

/-- `T'' ⟶ R` followed by `R ⟶ X` is `T'' ⟶ X`. -/
theorem chartBaseChangePairToRelation_w :
    representedSpaceMap B S hS (chartBaseChangePairToRelation ψ) ≫
        chartToSpace B S hS X (presentationRelationChart (projectiveBundlePresentation X)) =
      chartBaseChangePairToSpace ψ := by
  refine ObjectProperty.hom_ext _ ?_
  show yoneda.map (chartBaseChangePairToRelation ψ) ≫
      (presentationRelationChart (projectiveBundlePresentation X)).obj.hom =
    yoneda.map (pullback.fst _ _ ≫ chartBaseChangeToBase ψ) ≫ ψ.hom
  rw [← yoneda_map_toOver_map_comp_hom (presentationRelationTargetHom (projectiveBundlePresentation
      X)), ← Category.assoc, ← Functor.map_comp,
    chartBaseChangePairToRelation_fst, Functor.map_comp, Category.assoc, Functor.map_comp,
    Category.assoc]
  exact congrArg (yoneda.map (pullback.fst _ _) ≫ ·) (isPullback_chartBaseChange ψ).w

/-- The morphism `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U) ⟶ 𝐏(ℰ)` which descends to the comparison. -/
abbrev bundleCoverToSpace :
    yoneda.obj (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶
      (projectiveBundle E hfree).1 :=
  yoneda.map (bundleCoverToChart ψ E hfree) ≫ projectiveBundleChart E hfree

/-- For `q : T'' ⟶ T'` over `T`, the composite `T'' ⟶ T' ⟶ U ⟶ X` is `T'' ⟶ X`. -/
theorem chartBaseChangePair_comp_toChart_w (q : chartBaseChangePair ψ ⟶ chartBaseChange ψ)
    (hq : q ≫ chartBaseChangeToBase ψ = pullback.fst _ _ ≫ chartBaseChangeToBase ψ) :
    representedSpaceMap B S hS (q ≫ chartBaseChangeToChart ψ) ≫
        chartToSpace B S hS X (bundleBaseChart X) = chartBaseChangePairToSpace ψ := by
  refine ObjectProperty.hom_ext _ ?_
  show yoneda.map (q ≫ chartBaseChangeToChart ψ) ≫ (bundleBaseChart X).obj.hom =
    yoneda.map (pullback.fst _ _ ≫ chartBaseChangeToBase ψ) ≫ ψ.hom
  rw [Functor.map_comp, Category.assoc]
  show yoneda.map q ≫ yoneda.map (chartBaseChangeToChart ψ) ≫
      (chartToSpace B S hS X (bundleBaseChart X)).hom = _
  rw [(isPullback_chartBaseChange ψ).w, ← Category.assoc, ← Functor.map_comp, hq]

/-- For each `i`, the composite `𝐏(ℰ_{T''}) ⟶ 𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U)` along the `i`-th projection
`T'' ⟶ T'` equals `𝐏(ℰ_{T''}) ⟶ 𝐏(ℰ_R) ⟶ 𝐏(ℰ_U)` along the `i`-th projection `R ⟶ U`. -/
theorem bundleCoverPair_comp_bundleCoverToChart (i : Fin 2) :
    readingBundleSiteMap E hfree (if i = 0 then pullback.fst _ _ else pullback.snd _ _)
          (by
            split_ifs
            · exact representedSpaceMap_pullback_fst_comp ψ
            · exact representedSpaceMap_pullback_snd_comp ψ) ≫
        bundleCoverToChart ψ E hfree =
      readingBundleSiteMap E hfree (chartBaseChangePairToRelation ψ)
          (chartBaseChangePairToRelation_w ψ) ≫
        (projectiveBundleChartFamily E hfree).siteMap
          (if i = 0 then presentationRelationTargetHom (projectiveBundlePresentation X) else
              presentationRelationSourceHom (projectiveBundlePresentation X)) := by
  have hq : (if i = 0 then pullback.fst (chartBaseChangeToBase ψ) (chartBaseChangeToBase ψ)
      else pullback.snd _ _) ≫ chartBaseChangeToBase ψ =
        pullback.fst _ _ ≫ chartBaseChangeToBase ψ := by
    split_ifs
    · rfl
    · exact pullback.condition.symm
  have hr : chartBaseChangePairToRelation ψ ≫ (SmallEtale.toOver B S hS X.1).map
      (if i = 0 then presentationRelationTargetHom (projectiveBundlePresentation X) else
          presentationRelationSourceHom (projectiveBundlePresentation X)) =
      (if i = 0 then pullback.fst _ _ else pullback.snd _ _) ≫ chartBaseChangeToChart ψ := by
    split_ifs
    · exact chartBaseChangePairToRelation_fst ψ
    · exact chartBaseChangePairToRelation_snd ψ
  refine (readingBundleSiteMap_comp E hfree _ (chartBaseChangeToChart ψ) (chartBaseChange_w ψ) _
    (chartBaseChangePair_comp_toChart_w ψ _ hq)).trans ?_
  refine (readingBundleSiteMap_congr E hfree hr.symm _
    (hr ▸ chartBaseChangePair_comp_toChart_w ψ _ hq)).trans ?_
  exact (readingBundleSiteMap_comp E hfree (chartBaseChangePairToRelation ψ) _
    (representedSpaceMap_toOver_map_comp_chartToSpace _) (chartBaseChangePairToRelation_w ψ)
    _).symm

/-- `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ)` identifies the two projections of the kernel pair. -/
theorem bundleCoverPair_comp_bundleCoverToSpace :
    yoneda.map (bundleCoverPairFst ψ E hfree) ≫ bundleCoverToSpace ψ E hfree =
      yoneda.map (bundleCoverPairSnd ψ E hfree) ≫ bundleCoverToSpace ψ E hfree := by
  have h₀ := bundleCoverPair_comp_bundleCoverToChart ψ E hfree 0
  have h₁ := bundleCoverPair_comp_bundleCoverToChart ψ E hfree 1
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one] at h₀ h₁
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  show yoneda.map (readingBundleSiteMap E hfree (pullback.fst _ _) _ ≫ _) ≫ _ =
    yoneda.map (readingBundleSiteMap E hfree (pullback.snd _ _) _ ≫ _) ≫ _
  rw [h₀, h₁]
  exact ((congrArg (· ≫ projectiveBundleChart E hfree) (yoneda.map_comp _ _)).trans
    (Category.assoc _ _ _)).trans ((congrArg (yoneda.map _ ≫ ·)
      (siteMap_bundleRelFst_comp_projectiveBundleSpaceChart E hfree)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ projectiveBundleChart E hfree) (yoneda.map_comp _ _)).symm))

/-- The descent of morphisms along the cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)`: a morphism out of
`𝐏(ℰ_{T'})` to a sheaf which identifies the kernel pair factors uniquely through `𝐏(ℰ_T)`. -/
theorem existsUnique_desc_bundleCover {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (k : yoneda.obj (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶ G)
    (hk : yoneda.map (bundleCoverPairFst ψ E hfree) ≫ k =
      yoneda.map (bundleCoverPairSnd ψ E hfree) ≫ k) :
    ∃! d : yoneda.obj (readingBundleSite E hfree ψ) ⟶ G,
      yoneda.map (bundleCover ψ E hfree) ≫ d = k :=
  existsUnique_desc_of_surjective_etale_atlas B S hS (isSheaf_yoneda_obj B S hS _)
    (yoneda.map (bundleCover ψ E hfree)) ((isPullback_bundleCoverPair ψ E hfree).map yoneda)
    (presheaf_surjective_bundleCover ψ E hfree) (presheaf_etale_bundleCover ψ E hfree) hG k hk

/-- **The comparison morphism `𝐏(ℰ_T) ⟶ 𝐏(ℰ)`**, descended from `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U) ⟶ 𝐏(ℰ)`. -/
def readingBundleToSpace :
    yoneda.obj (readingBundleSite E hfree ψ) ⟶ (projectiveBundle E hfree).1 :=
  (existsUnique_desc_bundleCover ψ E hfree (projectiveBundle E hfree).property.isSheaf
    (bundleCoverToSpace ψ E hfree)
    (bundleCoverPair_comp_bundleCoverToSpace ψ E hfree)).exists.choose

/-- The comparison restricted along the cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)` is
`𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_U) ⟶ 𝐏(ℰ)`. -/
theorem bundleCover_comp_readingBundleToSpace :
    yoneda.map (bundleCover ψ E hfree) ≫ readingBundleToSpace ψ E hfree =
      bundleCoverToSpace ψ E hfree :=
  (existsUnique_desc_bundleCover ψ E hfree (projectiveBundle E hfree).property.isSheaf
    (bundleCoverToSpace ψ E hfree)
    (bundleCoverPair_comp_bundleCoverToSpace ψ E hfree)).exists.choose_spec

/-- Two morphisms out of `𝐏(ℰ_T)` to a sheaf agreeing on the cover are equal. -/
theorem readingBundleSite_hom_ext {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {d₁ d₂ : yoneda.obj (readingBundleSite E hfree ψ) ⟶ G}
    (h : yoneda.map (bundleCover ψ E hfree) ≫ d₁ = yoneda.map (bundleCover ψ E hfree) ≫ d₂) :
    d₁ = d₂ := by
  have hk : yoneda.map (bundleCoverPairFst ψ E hfree) ≫ yoneda.map (bundleCover ψ E hfree) ≫ d₁ =
      yoneda.map (bundleCoverPairSnd ψ E hfree) ≫ yoneda.map (bundleCover ψ E hfree) ≫ d₁ := by
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      (isPullback_bundleCoverPair ψ E hfree).w]
  exact (existsUnique_desc_bundleCover ψ E hfree hG _ hk).unique rfl h.symm

/-- **The comparison lies over `ψ`.** -/
theorem readingBundleToSpace_comp_proj :
    readingBundleToSpace ψ E hfree ≫ (projectiveBundleProj E hfree).hom =
      yoneda.map (readingBundleSiteToBase E hfree ψ) ≫ ψ.hom := by
  refine readingBundleSite_hom_ext ψ E hfree X.property.isSheaf ?_
  have h₁ := (isPullback_projectiveBundleProj E hfree).w
  have h₂ := (isPullback_readingBundleSiteMap E hfree (chartBaseChangeToChart ψ)
    (chartBaseChange_w ψ)).w
  have h₃ := (isPullback_readingBundleSiteMap E hfree (chartBaseChangeToBase ψ)
    (ψ := ψ) (ψ' := chartBaseChangeToSpace ψ) rfl).w
  have h₄ := (isPullback_chartBaseChange ψ).w
  rw [← Category.assoc, bundleCover_comp_readingBundleToSpace, Category.assoc, h₁,
    ← Category.assoc, ← Functor.map_comp]
  show yoneda.map (readingBundleSiteMap E hfree (chartBaseChangeToChart ψ) _ ≫
      readingBundleSiteToBase E hfree (chartToSpace B S hS X (bundleBaseChart X))) ≫
      (chartToSpace B S hS X (bundleBaseChart X)).hom = _
  rw [h₂, Functor.map_comp]
  refine (Category.assoc _ _ _).trans ((congrArg (yoneda.map _ ≫ ·) h₄).trans
    ((Category.assoc _ _ _).symm.trans ?_))
  rw [← Functor.map_comp, ← h₃, Functor.map_comp, Category.assoc]

/-! ### The comparison square is cartesian -/

/-- `𝐏(ℰ_{T'}) = 𝐏(ℰ) ×_X T'`: the bundle over `T'` is the base change of the chart bundle
`𝐏(ℰ_U) = 𝐏(ℰ) ×_X U`. -/
theorem isPullback_bundleCoverToSpace :
    IsPullback (bundleCoverToSpace ψ E hfree)
      (yoneda.map (readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ)))
      (projectiveBundleProj E hfree).hom (yoneda.map (chartBaseChangeToBase ψ) ≫ ψ.hom) := by
  have h := ((isPullback_readingBundleSiteMap E hfree (chartBaseChangeToChart ψ)
    (chartBaseChange_w ψ)).map yoneda).paste_horiz
      (isPullback_projectiveBundleProj E hfree)
  rw [← (isPullback_chartBaseChange ψ).w]
  exact h

/-- Presheaves on the site have pullbacks (instance search for it times out). -/
instance (priority := high) hasPullback_presheaf_bigFppfOver
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : HasPullback f g :=
  have : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := functorCategoryHasLimitsOfShape
  HasLimitsOfShape.has_limit _

/-- The fibre product `T ×_X 𝐏(ℰ)` as a presheaf. -/
abbrev bundleFibre : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (projectiveBundleProj E hfree).hom ψ.hom

/-- The fibre product `T ×_X 𝐏(ℰ)` is a sheaf. -/
theorem isSheaf_bundleFibre :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (bundleFibre ψ E hfree) := by
  refine ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf (BigFppfOver.topology B S hS))
    (limit.isLimit _) ?_
  rintro (_ | _ | _)
  · exact X.property.isSheaf
  · exact (projectiveBundle E hfree).property.isSheaf
  · exact isSheaf_yoneda_obj B S hS T

/-- The comparison `𝐏(ℰ_T) ⟶ T ×_X 𝐏(ℰ)`. -/
abbrev bundleFibreLift : yoneda.obj (readingBundleSite E hfree ψ) ⟶ bundleFibre ψ E hfree :=
  pullback.lift _ _ (readingBundleToSpace_comp_proj ψ E hfree)

/-- The atlas `𝐏(ℰ_{T'}) ⟶ T ×_X 𝐏(ℰ)`. -/
abbrev bundleFibreAtlas :
    yoneda.obj (readingBundleSite E hfree (chartBaseChangeToSpace ψ)) ⟶ bundleFibre ψ E hfree :=
  yoneda.map (bundleCover ψ E hfree) ≫ bundleFibreLift ψ E hfree

/-- The atlas `𝐏(ℰ_{T'}) ⟶ T ×_X 𝐏(ℰ)` is the base change of `T' ⟶ T` along
`T ×_X 𝐏(ℰ) ⟶ T`. -/
theorem isPullback_bundleFibreAtlas :
    IsPullback (bundleFibreAtlas ψ E hfree)
      (yoneda.map (readingBundleSiteToBase E hfree (chartBaseChangeToSpace ψ)))
      (pullback.snd _ _) (yoneda.map (chartBaseChangeToBase ψ)) := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback _ _)
  · rw [Category.assoc, pullback.lift_fst, bundleCover_comp_readingBundleToSpace]
    exact isPullback_bundleCoverToSpace ψ E hfree
  · rw [Category.assoc, pullback.lift_snd, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg yoneda.map (isPullback_readingBundleSiteMap E hfree (chartBaseChangeToBase ψ)
      (ψ := ψ) (ψ' := chartBaseChangeToSpace ψ) rfl).w

/-- The atlas `𝐏(ℰ_{T'}) ⟶ T ×_X 𝐏(ℰ)` has any base-change stable property of `T' ⟶ T`. -/
private theorem presheaf_bundleFibreAtlas_of_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (h : P ((BigFppfOver.toScheme B S hS).map (chartBaseChangeToBase ψ))) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (bundleFibreAtlas ψ E hfree) :=
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := P.inverseImage (BigFppfOver.toScheme B S hS)) (F := yoneda)
  MorphismProperty.of_isPullback (isPullback_bundleFibreAtlas ψ E hfree).flip
    ((presheaf_yoneda_map_iff B S hS inferInstance _).2 h)

/-- The atlas `𝐏(ℰ_{T'}) ⟶ T ×_X 𝐏(ℰ)` is étale. -/
theorem presheaf_etale_bundleFibreAtlas :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (bundleFibreAtlas ψ E hfree) :=
  presheaf_bundleFibreAtlas_of_property ψ E hfree _ (etale_chartBaseChangeToBase ψ)

/-- The atlas `𝐏(ℰ_{T'}) ⟶ T ×_X 𝐏(ℰ)` is surjective. -/
theorem presheaf_surjective_bundleFibreAtlas :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (bundleFibreAtlas ψ E hfree) :=
  presheaf_bundleFibreAtlas_of_property ψ E hfree _ (surjective_chartBaseChangeToBase ψ)

/-- The two projections `𝐏(ℰ_{T''}) ⟶ 𝐏(ℰ_{T'})` agree after the cover `𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)`. -/
theorem bundleCoverPair_comp_bundleCover :
    bundleCoverPairFst ψ E hfree ≫ bundleCover ψ E hfree =
      bundleCoverPairSnd ψ E hfree ≫ bundleCover ψ E hfree :=
  (isPullback_bundleCoverPair ψ E hfree).w

/-- The kernel pair of the atlas of `T ×_X 𝐏(ℰ)` is `𝐏(ℰ_{T''})`. -/
theorem isPullback_bundleFibreAtlasPair :
    IsPullback (yoneda.map (bundleCoverPairFst ψ E hfree))
      (yoneda.map (bundleCoverPairSnd ψ E hfree))
      (bundleFibreAtlas ψ E hfree) (bundleFibreAtlas ψ E hfree) := by
  have hfst := (isPullback_readingBundleSiteMap E hfree (pullback.fst _ _)
    (representedSpaceMap_pullback_fst_comp ψ)).map yoneda
  have hsnd := (isPullback_readingBundleSiteMap E hfree (pullback.snd _ _)
    (representedSpaceMap_pullback_snd_comp ψ)).map yoneda
  have hkp := (IsPullback.of_hasPullback (chartBaseChangeToBase ψ)
    (chartBaseChangeToBase ψ)).map yoneda
  have hcomp := hfst.paste_vert hkp
  rw [← hsnd.w, ← (isPullback_bundleFibreAtlas ψ E hfree).w] at hcomp
  refine IsPullback.of_bot hcomp ?_ (isPullback_bundleFibreAtlas ψ E hfree)
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    bundleCoverPair_comp_bundleCover]

/-- The inverse `T ×_X 𝐏(ℰ) ⟶ 𝐏(ℰ_T)`, descended from the cover. -/
def bundleFibreInv : bundleFibre ψ E hfree ⟶ yoneda.obj (readingBundleSite E hfree ψ) :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS (isSheaf_bundleFibre ψ E hfree)
    (bundleFibreAtlas ψ E hfree) (isPullback_bundleFibreAtlasPair ψ E hfree)
    (presheaf_surjective_bundleFibreAtlas ψ E hfree) (presheaf_etale_bundleFibreAtlas ψ E hfree)
    (isSheaf_yoneda_obj B S hS _) (yoneda.map (bundleCover ψ E hfree))
    (by rw [← Functor.map_comp, ← Functor.map_comp,
      bundleCoverPair_comp_bundleCover])).exists.choose

/-- The inverse `T ×_X 𝐏(ℰ) ⟶ 𝐏(ℰ_T)` restricted along the atlas is the cover
`𝐏(ℰ_{T'}) ⟶ 𝐏(ℰ_T)`. -/
theorem bundleFibreAtlas_comp_bundleFibreInv :
    bundleFibreAtlas ψ E hfree ≫ bundleFibreInv ψ E hfree = yoneda.map (bundleCover ψ E hfree) :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS (isSheaf_bundleFibre ψ E hfree)
    (bundleFibreAtlas ψ E hfree) (isPullback_bundleFibreAtlasPair ψ E hfree)
    (presheaf_surjective_bundleFibreAtlas ψ E hfree) (presheaf_etale_bundleFibreAtlas ψ E hfree)
    (isSheaf_yoneda_obj B S hS _) (yoneda.map (bundleCover ψ E hfree))
    (by rw [← Functor.map_comp, ← Functor.map_comp,
      bundleCoverPair_comp_bundleCover])).exists.choose_spec

/-- The comparison `𝐏(ℰ_T) ⟶ T ×_X 𝐏(ℰ)` is an isomorphism. -/
instance isIso_bundleFibreLift : IsIso (bundleFibreLift ψ E hfree) := by
  refine ⟨bundleFibreInv ψ E hfree, ?_, ?_⟩
  · refine readingBundleSite_hom_ext ψ E hfree (isSheaf_yoneda_obj B S hS _) ?_
    rw [← Category.assoc, bundleFibreAtlas_comp_bundleFibreInv, Category.comp_id]
  · have hk : yoneda.map (bundleCoverPairFst ψ E hfree) ≫ bundleFibreAtlas ψ E hfree =
        yoneda.map (bundleCoverPairSnd ψ E hfree) ≫ bundleFibreAtlas ψ E hfree :=
      (isPullback_bundleFibreAtlasPair ψ E hfree).w
    exact (existsUnique_desc_of_surjective_etale_atlas B S hS (isSheaf_bundleFibre ψ E hfree)
      (bundleFibreAtlas ψ E hfree) (isPullback_bundleFibreAtlasPair ψ E hfree)
      (presheaf_surjective_bundleFibreAtlas ψ E hfree) (presheaf_etale_bundleFibreAtlas ψ E hfree)
      (isSheaf_bundleFibre ψ E hfree) _ hk).unique
        (by rw [← Category.assoc, bundleFibreAtlas_comp_bundleFibreInv]) (Category.comp_id _)

/-- **`𝐏(ℰ_T) = T ×_X 𝐏(ℰ)`**: the reading bundle over a scheme `T` over `X` is the base change of
the projective bundle of `ℰ`. -/
theorem isPullback_readingBundleToSpace :
    IsPullback (readingBundleToSpace ψ E hfree) (yoneda.map (readingBundleSiteToBase E hfree ψ))
      (projectiveBundleProj E hfree).hom ψ.hom :=
  IsPullback.of_iso_pullback ⟨readingBundleToSpace_comp_proj ψ E hfree⟩
    (asIso (bundleFibreLift ψ E hfree)) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end Comparison

/-! ### Naturality of the comparison in the scheme -/

section Naturality

variable (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  {T₁ T₂ : BigFppfOver B S hS} (g : T₁ ⟶ T₂) {ψ₁ : representedAlgebraicSpace B S hS T₁ ⟶ X}
  {ψ₂ : representedAlgebraicSpace B S hS T₂ ⟶ X} (w : representedSpaceMap B S hS g ≫ ψ₂ = ψ₁)

/-- The morphism `T₁ ×_X U ⟶ T₂ ×_X U` induced by `g`. -/
def chartBaseChangeMap : chartBaseChange ψ₁ ⟶ chartBaseChange ψ₂ :=
  Yoneda.fullyFaithful.preimage ((isPullback_chartBaseChange ψ₂).lift
    (yoneda.map (chartBaseChangeToChart ψ₁)) (yoneda.map (chartBaseChangeToBase ψ₁ ≫ g)) (by
      rw [(isPullback_chartBaseChange ψ₁).w, Functor.map_comp, Category.assoc]
      exact congrArg (yoneda.map (chartBaseChangeToBase ψ₁) ≫ ·)
        (congrArg (fun k => k.hom) w).symm))

/-- The morphism `T₁ ×_X U ⟶ T₂ ×_X U` commutes with the projections to `U`. -/
theorem chartBaseChangeMap_toChart :
    chartBaseChangeMap g w ≫ chartBaseChangeToChart ψ₂ = chartBaseChangeToChart ψ₁ :=
  yoneda.map_injective (by
    rw [Functor.map_comp, chartBaseChangeMap, Functor.FullyFaithful.map_preimage]
    exact IsPullback.lift_fst _ _ _ _)

/-- The morphism `T₁ ×_X U ⟶ T₂ ×_X U` lies over `g : T₁ ⟶ T₂`. -/
theorem chartBaseChangeMap_toBase :
    chartBaseChangeMap g w ≫ chartBaseChangeToBase ψ₂ = chartBaseChangeToBase ψ₁ ≫ g :=
  yoneda.map_injective (by
    rw [Functor.map_comp, chartBaseChangeMap, Functor.FullyFaithful.map_preimage]
    exact IsPullback.lift_snd _ _ _ _)

/-- `T₁ ×_X U ⟶ T₁ ⟶ T₂` followed by `T₂ ⟶ X` is `T₁ ×_X U ⟶ X`. -/
private theorem representedSpaceMap_chartBaseChangeToBase_comp
    (h : representedSpaceMap B S hS g ≫ ψ₂ = ψ₁) :
    representedSpaceMap B S hS (chartBaseChangeToBase ψ₁ ≫ g) ≫ ψ₂ = chartBaseChangeToSpace ψ₁ := by
  rw [← representedSpaceMap_comp, Category.assoc, h]

/-- The morphism `T₁ ×_X U ⟶ T₂ ×_X U` commutes with the morphisms to `X`. -/
theorem chartBaseChangeMap_w :
    representedSpaceMap B S hS (chartBaseChangeMap g w) ≫ chartBaseChangeToSpace ψ₂ =
      chartBaseChangeToSpace ψ₁ := by
  rw [← Category.assoc, representedSpaceMap_comp, chartBaseChangeMap_toBase]
  exact representedSpaceMap_chartBaseChangeToBase_comp g w

include w in
/-- **Naturality of the comparison**: along `g : T₁ ⟶ T₂` over `X`, the comparison of `T₁` is the
base-change morphism `𝐏(ℰ_{ψ₁}) ⟶ 𝐏(ℰ_{ψ₂})` followed by the comparison of `T₂`. -/
theorem readingBundleSiteMap_comp_readingBundleToSpace :
    yoneda.map (readingBundleSiteMap E hfree g w) ≫ readingBundleToSpace ψ₂ E hfree =
      readingBundleToSpace ψ₁ E hfree := by
  refine readingBundleSite_hom_ext ψ₁ E hfree (projectiveBundle E hfree).property.isSheaf ?_
  rw [bundleCover_comp_readingBundleToSpace, ← Category.assoc, ← Functor.map_comp]
  have W₁ := representedSpaceMap_chartBaseChangeToBase_comp g w
  have W₂ : representedSpaceMap B S hS (chartBaseChangeMap g w ≫ chartBaseChangeToBase ψ₂) ≫ ψ₂ =
      chartBaseChangeToSpace ψ₁ := by
    rw [chartBaseChangeMap_toBase]
    exact W₁
  have e₁ : bundleCover ψ₁ E hfree ≫ readingBundleSiteMap E hfree g w =
      readingBundleSiteMap E hfree (chartBaseChangeMap g w) (chartBaseChangeMap_w g w) ≫
        bundleCover ψ₂ E hfree :=
    (readingBundleSiteMap_comp E hfree _ _ _ _ W₁).trans
      ((readingBundleSiteMap_congr E hfree (chartBaseChangeMap_toBase g w).symm W₁ W₂).trans
        (readingBundleSiteMap_comp E hfree _ _ _ _ W₂).symm)
  have W₃ : representedSpaceMap B S hS (chartBaseChangeMap g w ≫ chartBaseChangeToChart ψ₂) ≫
      chartToSpace B S hS X (bundleBaseChart X) = chartBaseChangeToSpace ψ₁ := by
    rw [chartBaseChangeMap_toChart]
    exact chartBaseChange_w ψ₁
  rw [e₁, Functor.map_comp, Category.assoc, bundleCover_comp_readingBundleToSpace,
    ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun k => yoneda.map k ≫ projectiveBundleChart E hfree)
    ((readingBundleSiteMap_comp E hfree (chartBaseChangeMap g w) (chartBaseChangeToChart ψ₂)
      (chartBaseChange_w ψ₂) (chartBaseChangeMap_w g w) W₃).trans
    (readingBundleSiteMap_congr E hfree (chartBaseChangeMap_toChart g w) W₃ (chartBaseChange_w ψ₁)))

end Naturality

/-! ### The kernel pair of the chart of the projective bundle -/

/-- **The kernel pair of the chart `𝐏(ℰ_U) ⟶ 𝐏(ℰ)` is `𝐏(ℰ_R)`**, `R = U ×_X U` the relation of the
presentation. -/
theorem isPullback_projectiveBundleSpaceChart_relation (E : Modules.{u, u} B S hS X.1 X.2)
    [E.IsQuasicoherentOnSite] (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    IsPullback (yoneda.map ((projectiveBundleChartFamily E hfree).siteMap
        (presentationRelationTargetHom (projectiveBundlePresentation X))))
      (yoneda.map ((projectiveBundleChartFamily E hfree).siteMap (presentationRelationSourceHom
          (projectiveBundlePresentation X))))
      (projectiveBundleChart E hfree) (projectiveBundleChart E hfree) := by
  have h₁ := ((projectiveBundleChartFamily E hfree).isPullback_siteMap
      (presentationRelationTargetHom (projectiveBundlePresentation X))).map yoneda
  have h₂ := ((projectiveBundleChartFamily E hfree).isPullback_siteMap
      (presentationRelationSourceHom (projectiveBundlePresentation X))).map yoneda
  have hcomp := h₁.paste_vert (isPullback_projectiveBundlePresentation X)
  rw [← h₂.w, ← (isPullback_projectiveBundleProj E hfree).w] at hcomp
  exact IsPullback.of_bot hcomp (siteMap_bundleRelFst_comp_projectiveBundleSpaceChart E hfree)
    (isPullback_projectiveBundleProj E hfree)

end AlgebraicGeometry.Space.PrivateChern

end
