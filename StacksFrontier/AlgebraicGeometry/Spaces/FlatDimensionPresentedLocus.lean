module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatDimensionFunctorPure
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The flat-dimension locus over a test scheme, read on all schemes

In Situation 0CWU, fix a test scheme `T` over `Y`. A surjective étale chart `U` of the base change
`X_T` presents `F_n` over `T` by the scheme-level situation of Stacks 05MT on `U ⟶ T`. By
`AlgebraicGeometry.Space.FlatDimensionSituation.stageSituation_isFlat_iff_of_isSurjective` the
scheme-level functor does not depend on the chart, so it is a functor of `T` alone,
`AlgebraicGeometry.Space.FlatDimensionSituation.Presented`, defined on *all* schemes over the
scheme underlying `T`. This is what lets the descent and induction arguments of the proof of
Stacks 0CX1, which are made over schemes that need not lie in the site, be carried out with the
scheme-level tools of Stacks 05UG.

## Main definitions

* `AlgebraicGeometry.Space.FlatDimensionSituation.surjectiveChart`: a chosen surjective étale
  chart of `X_T`.
* `AlgebraicGeometry.Space.FlatDimensionSituation.Presented`: the scheme-level functor `F_n`
  over `T`, read on that chart.
* `AlgebraicGeometry.Space.FlatDimensionSituation.IsRepresentedOver`: it is cut out by a
  monomorphism of finite presentation.
* `AlgebraicGeometry.Space.schemesOverOfContained`: a scheme of the site over the scheme of a test
  scheme, as a test scheme.

## Main results

* `AlgebraicGeometry.Space.FlatDimensionSituation.presented_iff`: any surjective chart computes
  `Presented`.
* `AlgebraicGeometry.Space.FlatDimensionSituation.presented_baseChange_iff`: `Presented` is
  compatible with morphisms of test schemes.
* `FlatDimensionSituation.isFlatInDimensionsGEAfterBaseChange_iff_presented`:
  on test schemes of the site, `Presented` is the condition of Stacks 0CWT.
* `AlgebraicGeometry.Space.FlatDimensionSituation.isRepresentedOver_of_etale_local`:
  representability is étale local on the test scheme.

## References

* [Stacks Project, Tag 0CX1](https://stacks.math.columbia.edu/tag/0CX1)
* [Stacks Project, Tag 0CWS](https://stacks.math.columbia.edu/tag/0CWS)
* [Stacks Project, Tag 05UG](https://stacks.math.columbia.edu/tag/05UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Flatness

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every algebraic space has a surjective étale chart. -/
theorem exists_isSurjective_etaleChart (X : AlgebraicSpaces B S hS) :
    ∃ U : SmallEtale B S hS X.1, IsSurjective B S hS U.obj.hom := by
  obtain ⟨W, p, hps, hpe⟩ := X.2.exists_atlas
  exact ⟨⟨CostructuredArrow.mk p, hpe⟩,
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 W p).1 hps⟩

/-- A scheme of the site with a morphism to the scheme underlying a test scheme, as a test
scheme over the same algebraic space. -/
def schemesOverOfContained {Y : AlgebraicSpaces B S hS} (T : SchemesOver Y) {Z : Scheme.{u}}
    (hZ : B.Contains Z) (φ : Z ⟶ (BigFppfOver.toScheme B S hS).obj T.left) : SchemesOver Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
    (BigFppfOver.siteMapOver B S hS T.left hZ φ) ≫ T.hom)

/-- The morphism of test schemes from `AlgebraicGeometry.Space.schemesOverOfContained`. -/
def schemesOverOfContainedMap {Y : AlgebraicSpaces B S hS} (T : SchemesOver Y) {Z : Scheme.{u}}
    (hZ : B.Contains Z) (φ : Z ⟶ (BigFppfOver.toScheme B S hS).obj T.left) :
    schemesOverOfContained T hZ φ ⟶ T :=
  CostructuredArrow.homMk (BigFppfOver.siteMapOver B S hS T.left hZ φ) rfl

/-- The scheme underlying `schemesOverOfContained T hZ φ` is `Z`. -/
@[simp]
theorem toScheme_obj_schemesOverOfContained {Y : AlgebraicSpaces B S hS} (T : SchemesOver Y)
    {Z : Scheme.{u}} (hZ : B.Contains Z) (φ : Z ⟶ (BigFppfOver.toScheme B S hS).obj T.left) :
    (BigFppfOver.toScheme B S hS).obj (schemesOverOfContained T hZ φ).left = Z := rfl

/-- The morphism of schemes underlying `schemesOverOfContainedMap T hZ φ` is `φ`. -/
@[simp]
theorem toScheme_map_schemesOverOfContainedMap {Y : AlgebraicSpaces B S hS} (T : SchemesOver Y)
    {Z : Scheme.{u}} (hZ : B.Contains Z) (φ : Z ⟶ (BigFppfOver.toScheme B S hS).obj T.left) :
    (BigFppfOver.toScheme B S hS).map (schemesOverOfContainedMap T hZ φ).left = φ := rfl

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u} B S hS) (n : ℕ)

/-- A chosen surjective étale chart of the base change `X_T`. -/
def surjectiveChart (T : SchemesOver D.Y) : SmallEtale B S hS (baseChangeSpace D.f T).1 :=
  (exists_isSurjective_etaleChart (baseChangeSpace D.f T)).choose

/-- The chart `surjectiveChart T` is surjective. -/
theorem isSurjective_surjectiveChart (T : SchemesOver D.Y) :
    IsSurjective B S hS (D.surjectiveChart T).obj.hom :=
  (exists_isSurjective_etaleChart (baseChangeSpace D.f T)).choose_spec

/-- **The scheme-level functor `F_n` over a test scheme.** For a scheme `Z` over the scheme
underlying a test scheme `T`, the condition of Stacks 05MT for the scheme-level situation which a
surjective étale chart of `X_T` presents. By `presented_iff` it does not depend on the chart. -/
def Presented (T : SchemesOver D.Y) (Z : Over ((BigFppfOver.toScheme B S hS).obj T.left)) :
    Prop :=
  (D.stageSituation B S hS n T (D.surjectiveChart T)).IsFlatInDimensionsGEAfterBaseChange Z

/-- Any surjective étale chart of `X_T` computes `Presented`. -/
theorem presented_iff (T : SchemesOver D.Y) (U : SmallEtale B S hS (baseChangeSpace D.f T).1)
    (hU : IsSurjective B S hS U.obj.hom) (Z : Over ((BigFppfOver.toScheme B S hS).obj T.left)) :
    D.Presented n T Z ↔ (D.stageSituation B S hS n T U).IsFlatInDimensionsGEAfterBaseChange Z :=
  D.stageSituation_isFlat_iff_of_isSurjective n _ U (D.isSurjective_surjectiveChart T) hU Z

/-- `Presented` is inherited along morphisms of schemes over `T`. -/
theorem presented_of_hom (T : SchemesOver D.Y)
    {Z Z' : Over ((BigFppfOver.toScheme B S hS).obj T.left)} (g : Z' ⟶ Z)
    (h : D.Presented n T Z) : D.Presented n T Z' :=
  (D.stageSituation B S hS n T (D.surjectiveChart T)).isFlatInDimensionsGEAfterBaseChange_of_hom
    g h

/-- `Presented` is an fpqc sheaf: it is the functor of a scheme-level situation, Stacks 05MV. -/
theorem isSheaf_presented (T : SchemesOver D.Y) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over ((BigFppfOver.toScheme B S hS).obj T.left))
      (propertyFunctor (D.Presented n T) fun g h ↦ D.presented_of_hom n T g h) :=
  (D.stageSituation B S hS n T (D.surjectiveChart T)).isSheaf_propertyFunctor

/-- **On test schemes of the site, `Presented` is the condition of Stacks 0CWT.** -/
theorem isFlatInDimensionsGEAfterBaseChange_iff_presented {T' T : SchemesOver D.Y}
    (β : T' ⟶ T) :
    D.IsFlatInDimensionsGEAfterBaseChange T' n ↔
      D.Presented n T (Over.mk ((BigFppfOver.toScheme B S hS).map β.left)) :=
  D.isFlatInDimensionsGEAfterBaseChange_iff_stageSituation B S hS n β _
    (D.isSurjective_surjectiveChart T)

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  preservesLimitsOfShape_walkingCospan_toScheme
  _root_.AlgebraicGeometry.isQuasicoherent_pullback_obj'
  _root_.AlgebraicGeometry.isFiniteType_pullback_obj'

/-- The scheme of the base change to `X_{T'}` of a chart `U` of `X_T` is the fibre product of
the chart morphism of `U` with `T' ⟶ T`. -/
def stageChartIsoPullback {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).X ≅
      ((D.stageSituation B S hS n T U).baseChange
        ((BigFppfOver.toScheme B S hS).map β.left)).X :=
  (isPullback_chartScheme_stageChart B S hS D.f β U).isoPullback

/-- The isomorphism `stageChartIsoPullback` followed by the first projection of the fibre product
is the projection of the base-changed chart to `U`. -/
theorem stageChartIsoPullback_hom_fst {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageChartIsoPullback n β U).hom ≫ pullback.fst (D.stageSituation B S hS n T U).f
        ((BigFppfOver.toScheme B S hS).map β.left) =
      (BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_baseChangeMap B S hS D.f β).snd U.1.hom) :=
  (isPullback_chartScheme_stageChart B S hS D.f β U).isoPullback_hom_fst

/-- The isomorphism `stageChartIsoPullback` followed by the second projection of the fibre
product is the structure morphism of the situation presented by the base-changed chart. -/
theorem stageChartIsoPullback_hom_snd {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageChartIsoPullback n β U).hom ≫ pullback.snd (D.stageSituation B S hS n T U).f
        ((BigFppfOver.toScheme B S hS).map β.left) =
      (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).f :=
  (isPullback_chartScheme_stageChart B S hS D.f β U).isoPullback_hom_snd

/-- The inverse of `stageChartIsoPullback` followed by the structure morphism of the situation
presented by the base-changed chart is the second projection of the fibre product. -/
theorem stageChartIsoPullback_inv_f {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageChartIsoPullback n β U).inv ≫
        (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).f =
      pullback.snd (D.stageSituation B S hS n T U).f ((BigFppfOver.toScheme B S hS).map β.left) :=
  (Iso.inv_comp_eq _).mpr (D.stageChartIsoPullback_hom_snd n β U).symm

/-- The module of the situation presented by the base-changed chart is the pullback of the
module of the base change of the situation presented by `U`. -/
def stageChartModuleIso {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).F ≅
      (Scheme.Modules.pullback (D.stageChartIsoPullback n β U).hom).obj
        ((D.stageSituation B S hS n T U).baseChange
          ((BigFppfOver.toScheme B S hS).map β.left)).F :=
  (D.stageModuleIso B S hS n β U).symm ≪≫
    (Scheme.Modules.pullbackCongr (D.stageChartIsoPullback_hom_fst n β U)).symm.app
      (D.stageSituation B S hS n T U).F ≪≫
    ((Scheme.Modules.pullbackComp (D.stageChartIsoPullback n β U).hom
      (pullback.fst _ _)).app (D.stageSituation B S hS n T U).F).symm

/-- The situation presented by the base-changed chart has the functor of the base change of the
situation presented by `U`. -/
theorem stageSituation_stageChart_isFlat_iff_baseChange {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1)
    (Z : Over ((BigFppfOver.toScheme B S hS).obj T'.left)) :
    (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).IsFlatInDimensionsGEAfterBaseChange
        Z ↔
      ((D.stageSituation B S hS n T U).baseChange
        ((BigFppfOver.toScheme B S hS).map β.left)).IsFlatInDimensionsGEAfterBaseChange Z := by
  set E := D.stageSituation B S hS n T U with hE
  set q : (BigFppfOver.toScheme B S hS).obj T'.left ⟶ E.S :=
    (BigFppfOver.toScheme B S hS).map β.left with hq
  let f' : (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).X ⟶ (E.baseChange q).S :=
    (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).f
  have : LocallyOfFiniteType f' :=
    (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).locallyOfFiniteType
  have := (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).isQuasicoherent
  have := (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).isFiniteType
  exact (E.baseChange q).isFlat_iff_of_surjective_etale (D.stageChartIsoPullback n β U).hom
    (Scheme.Hom.surjective _) (f' := f') (D.stageChartIsoPullback_hom_snd n β U).symm
    (F' := (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).F)
    (D.stageChartModuleIso n β U) Z

/-- **Base change of the presentation.** For a morphism `β : T' ⟶ T` of test schemes, the
situation presented by the base change of a chart `U` of `X_T` to `X_{T'}` is the base change of
the situation presented by `U`, so its functor is the restriction of that of `U`. -/
theorem stageSituation_stageChart_isFlat_iff {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1)
    (Z : Over ((BigFppfOver.toScheme B S hS).obj T'.left)) :
    (D.stageSituation B S hS n T' (stageChart B S hS D.f β U)).IsFlatInDimensionsGEAfterBaseChange
        Z ↔
      (D.stageSituation B S hS n T U).IsFlatInDimensionsGEAfterBaseChange
        ((Over.map ((BigFppfOver.toScheme B S hS).map β.left)).obj Z) :=
  (D.stageSituation_stageChart_isFlat_iff_baseChange n β U Z).trans
    ((D.stageSituation B S hS n T U).baseChange_isFlat_iff _ Z)

/-- **`Presented` is compatible with morphisms of test schemes.** -/
theorem presented_baseChange_iff {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (Z : Over ((BigFppfOver.toScheme B S hS).obj T'.left)) :
    D.Presented n T' Z ↔
      D.Presented n T ((Over.map ((BigFppfOver.toScheme B S hS).map β.left)).obj Z) := by
  rw [D.presented_iff n T' (stageChart B S hS D.f β (D.surjectiveChart T))
    (isSurjective_stageChart B S hS D.f β _ (D.isSurjective_surjectiveChart T)),
    D.stageSituation_stageChart_isFlat_iff n β]
  rfl

/-- **The flat-dimension locus over a test scheme is cut out by a monomorphism of finite
presentation**: there is a monomorphism of finite presentation `Z ⟶ T` through which a scheme
over `T` factors exactly when it lies in `Presented`. -/
def IsRepresentedOver (T : SchemesOver D.Y) : Prop :=
  IsCutOutByMonoFP (D.Presented n T)

/-- **Representability is étale local on the test scheme.** If every point of `T` lies in the
image of an étale morphism of test schemes `T' ⟶ T` over which the locus is represented, then it
is represented over `T`. -/
theorem isRepresentedOver_of_etale_local (T : SchemesOver D.Y)
    (h : ∀ t : (BigFppfOver.toScheme B S hS).obj T.left, ∃ (T' : SchemesOver D.Y) (β : T' ⟶ T),
      Etale ((BigFppfOver.toScheme B S hS).map β.left) ∧
        t ∈ Set.range ((BigFppfOver.toScheme B S hS).map β.left) ∧ D.IsRepresentedOver n T') :
    D.IsRepresentedOver n T := by
  refine IsCutOutByMonoFP.of_etale_local _ (fun g h ↦ D.presented_of_hom n T g h)
    (D.isSheaf_presented n T) fun t ↦ ?_
  obtain ⟨T', β, hβ, ht, hrep⟩ := h t
  exact ⟨_, _, hβ, ht, IsCutOutByMonoFP.of_iff hrep fun Z ↦ D.presented_baseChange_iff n β Z⟩

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
