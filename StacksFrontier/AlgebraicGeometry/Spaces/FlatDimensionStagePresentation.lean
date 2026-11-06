module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseConditionsFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq

/-!
# The chart presentation of the flat-dimension condition over a test scheme

In **Situation 0CWU** — a morphism `f : X ⟶ Y` of algebraic spaces over `S` locally of finite
type and a quasi-coherent `𝒪_X`-module `F` of finite type — fix a test scheme `T` over `Y` and an
étale scheme chart `U` of the base change `X_T`.  Because `T` is a scheme, the algebraic space it
represents has the *identity* chart, so `U` and that identity chart form a commuting square of
étale scheme charts of `f_T : X_T ⟶ T`, and the chart morphism `U ⟶ T` together with the
restriction of `F_T` to `U` is a situation of **Stacks 05MT**.

This file builds that situation and shows that the condition of **Stacks 0CWT** on a test scheme
`T'` over `T` is exactly the condition of Stacks 05MT for it at `T'`, viewed as a scheme over the
scheme underlying `T`.  That is the chart presentation of the proof of **Stacks 0CWW**, clause
(2), read over a test scheme instead of over `Y`: no base change of a chart of `Y` is involved,
and the value of the presentation at `T'` is `T'` itself.

## Main definitions

* `AlgebraicGeometry.Space.identityTargetChartDiagram`: the commuting square of étale scheme charts
  of a morphism with represented target, whose target chart is the identity chart.
* `AlgebraicGeometry.Space.stageChart`: the base change to `X_{T'}` of an étale scheme chart of
  `X_T` along a morphism `T' ⟶ T` of test schemes, by Stacks 03G2, part (4).
* `AlgebraicGeometry.Space.FlatDimensionSituation.stageSituation`: the situation of Stacks 05MT
  attached to a chart of `X_T`.
* `AlgebraicGeometry.Space.FlatDimensionSituation.stageModuleIso`: the identification of the
  restriction of `F_{T'}` to the base-changed chart with the scheme-level inverse image of the
  restriction of `F_T` to the original chart.

## Main results

* `AlgebraicGeometry.Space.exists_isAffine_isSurjective_chart_baseChangeSpace`: **Stacks 03H6**
  for the base change to an affine test scheme — `X_T` is a quasi-compact algebraic space when
  `f` is quasi-compact and `T` is affine, so it has a surjective étale chart whose scheme is
  affine.
* `AlgebraicGeometry.Space.isPullback_chartScheme_stageChart`: the base-changed chart of `X_{T'}`
  is, as a scheme, the fibre product of the chart of `X_T` and the scheme underlying `T'` over
  the scheme underlying `T`.
* **The presentation**, in the namespace
  `AlgebraicGeometry.Space.FlatDimensionSituation`:
  `isFlatInDimensionsGEAfterBaseChange_iff_stageSituation`.  For a morphism `T' ⟶ T` of test
  schemes and a *surjective* chart `U` of `X_T`, the base change `F_{T'}` is flat over `T'` in
  dimensions `≥ n` exactly when the base change of the situation of Stacks 05MT to `T'` is.
* `AlgebraicGeometry.Space.FlatDimensionSituation.quasiCompact_stageSituation_f`,
  `AlgebraicGeometry.Space.FlatDimensionSituation.locallyOfFinitePresentation_stageSituation_f`
  and `AlgebraicGeometry.Space.FlatDimensionSituation.isFinitePresentation_stageSituation_F`: the
  three hypotheses part (2) of Stacks 05MV asks of the presented situation, from quasi-compactness
  and local finite presentation of `f` and finite presentation of `F`.

## Implementation notes

The identity chart of a represented algebraic space is
`AlgebraicGeometry.Space.idEtaleChart`; its structure morphism is an identity, so it is
surjective and the commutation of the square of `identityTargetChartDiagram` is the defining
equation of `CategoryTheory.Functor.preimage` of the composite `U ⟶ X_T ⟶ T`.

The affine chart of `X_T` is obtained from quasi-compactness of `f` in the sense of
**Stacks 03HE**, which is a statement about base changes along morphisms *from quasi-compact
algebraic spaces*, applied at the algebraic space represented by the affine scheme `T`; the chart
is then **Stacks 03H6**,
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`.  The
étale half of what that produces is étaleness of a morphism of algebraic spaces in the sense of
Stacks 03FR, and `AlgebraicGeometry.Space.isEtaleChart_of_isEtale` reads it as the chart
property, by testing the definition at the identity of the source.

The cartesian square of schemes is obtained by pasting the representability square of the
transition morphism `X_{T'} ⟶ X_T` with the cartesian square of the two base changes, exactly as
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeAffineTest.lean` does for a base change by a
test object: all four corners of the pasted square of presheaves are representable, so it
descends to the big fppf category by full faithfulness of the Yoneda embedding and from there to
schemes.

Transporting the condition of Stacks 0CWG across that square, in both directions, is
`AlgebraicGeometry.flatInDimensions_canonical_of_isPullback` and
`AlgebraicGeometry.flatInDimensions_of_isPullback_canonical` of
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningFunctor/FlatDimensionLimitPreserving.lean`,
which compare an arbitrary cartesian square with the chosen fibre product.

The module comparison is `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, the
compatibility of the chart restriction of Stacks 03M0 with the inverse image of Stacks 03LW,
followed by the composition comparison of Stacks 03LU identifying the inverse image of `F_T`
along the transition morphism with `F_{T'}`.  The square of charts it is applied to is not
cartesian as a square of charts, and does not need to be.

Quasi-compactness of the presenting chart morphism is read off affineness of both of its ends:
both are affine schemes, so the morphism is affine and therefore quasi-compact.

## References

* [Stacks Project, Tag 0CWW](https://stacks.math.columbia.edu/tag/0CWW)
* [Stacks Project, Tag 0CWU](https://stacks.math.columbia.edu/tag/0CWU)
* [Stacks Project, Tag 0CWS](https://stacks.math.columbia.edu/tag/0CWS)
* [Stacks Project, Tag 0CWT](https://stacks.math.columbia.edu/tag/0CWT)
* [Stacks Project, Tag 0CWG](https://stacks.math.columbia.edu/tag/0CWG)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_FlatDimensionStagePresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_FlatDimensionStagePresentation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Étale charts out of étale morphisms -/

/-- A morphism from a representable presheaf which is étale in the sense of **Stacks 03FR** is
an étale chart: test the defining condition at the identity of the source. -/
theorem isEtaleChart_of_isEtale {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B S hS} (p : yoneda.obj W ⟶ F) (hp : IsEtale B S hS p) :
    IsEtaleChart B S hS F (CostructuredArrow.mk p) := by
  have h := hp W (𝟙 (yoneda.obj W)) (presheaf_etale_id B S hS W)
  rwa [Category.id_comp] at h

/-- The identity chart of a represented algebraic space is surjective on points. -/
theorem isSurjective_idEtaleChart (T : BigFppfOver B S hS) :
    IsSurjective B S hS (idEtaleChart B S hS T).obj.hom :=
  fun x => ⟨x, congrFun (pointsMap_id B S hS (yoneda.obj T)) x⟩

/-! ### The chart diagram at the identity chart of a represented target -/

/-- **The commuting square of étale scheme charts over a morphism with represented target.**
For a morphism `a : Z ⟶ T` of algebraic spaces whose target is the algebraic space represented
by an object `T` of the big fppf category, and an étale scheme chart `W` of `Z`, the square
whose source chart is `W`, whose target chart is the identity chart of `T` and whose vertical
morphism is the morphism of the site underlying `W ⟶ Z ⟶ T`. -/
def identityTargetChartDiagram {Z : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (a : Z ⟶ (schemeSpaceFunctor B S hS).obj T) (W : SmallEtale B S hS Z.1) :
    ChartDiagram B S hS Z.1 (yoneda.obj T) a.hom where
  U := W
  V := idEtaleChart B S hS T
  g := yoneda.preimage (W.1.hom ≫ a.hom)
  comm := by
    rw [Functor.map_preimage]
    exact (Category.comp_id _).symm

/-- The source chart of `identityTargetChartDiagram a W` is `W`. -/
@[simp]
theorem identityTargetChartDiagram_U {Z : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (a : Z ⟶ (schemeSpaceFunctor B S hS).obj T) (W : SmallEtale B S hS Z.1) :
    (identityTargetChartDiagram B S hS a W).U = W := rfl

/-- The target chart of `identityTargetChartDiagram a W` is the identity chart of `T`. -/
@[simp]
theorem identityTargetChartDiagram_V {Z : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (a : Z ⟶ (schemeSpaceFunctor B S hS).obj T) (W : SmallEtale B S hS Z.1) :
    (identityTargetChartDiagram B S hS a W).V = idEtaleChart B S hS T := rfl

/-- The Yoneda image of the vertical morphism of `identityTargetChartDiagram a W` is the
composite `W ⟶ Z ⟶ T`. -/
theorem yoneda_map_identityTargetChartDiagram_g {Z : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (a : Z ⟶ (schemeSpaceFunctor B S hS).obj T)
    (W : SmallEtale B S hS Z.1) :
    yoneda.map (identityTargetChartDiagram B S hS a W).g = W.1.hom ≫ a.hom :=
  Functor.map_preimage _ _

/-! ### An affine surjective chart of the base change to an affine test scheme -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03H6 for the base change to an affine test scheme.** The base change `X_T` of a
quasi-compact morphism of algebraic spaces to an affine test scheme `T` over its target is a
quasi-compact algebraic space, so it has a surjective étale chart whose scheme is affine.

Quasi-compactness of `f` in the sense of Stacks 03HE is tested at the quasi-compact algebraic
space represented by `T`, and the affine chart is then Stacks 03H6. -/
theorem exists_isAffine_isSurjective_chart_baseChangeSpace (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f.hom) (T : SchemesOver Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    ∃ U : SmallEtale B S hS (baseChangeSpace f T).1,
      IsAffine (chartScheme U) ∧ IsSurjective B S hS U.obj.hom := by
  have := hT
  have hqcT : IsQuasiCompactSpace B S hS (yoneda.obj T.left) :=
    isQuasiCompact_yoneda_of_compact B S hS T.left
      (Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj T.left))
  have hsq := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f T.hom)
  have hqc : IsQuasiCompactSpace B S hS (baseChangeSpace f T).1 :=
    IsQuasiCompactSpace.of_iso B S hS
      (hf (yoneda.obj T.left) (isAlgebraicSpace_yoneda B S hS T.left) hqcT T.hom.hom)
      hsq.flip.isoPullback.symm
  obtain ⟨W, p, hWaff, hpsurj, hpet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (baseChangeSpace f T).1 (baseChangeSpace f T).2).1 hqc
  refine ⟨⟨CostructuredArrow.mk p, isEtaleChart_of_isEtale B S hS p hpet⟩, hWaff, ?_⟩
  exact (surjective_iff_surjective_pointsMap B S hS (baseChangeSpace f T).1
    (baseChangeSpace f T).2 W p).1 hpsurj

/-! ### Base change of a chart of `X_T` to a later test scheme -/

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  preservesLimitsOfShape_walkingCospan_toScheme

/-- The transition morphism `X_{T'} ⟶ X_T` of base changes over a morphism `T' ⟶ T` of test
schemes is relatively representable: it is the base change of the morphism `T' ⟶ T` of
representable presheaves. -/
theorem relativelyRepresentable_baseChangeMap (f : X ⟶ Y) {T' T : SchemesOver Y} (β : T' ⟶ T) :
    yoneda.relativelyRepresentable (baseChangeMap f β).hom :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap f β)).flip
    (Functor.relativelyRepresentable.map yoneda β.left)

/-- The base change to `X_{T'}` of an étale scheme chart of `X_T`, along a morphism `T' ⟶ T`
of test schemes. -/
def stageChart (f : X ⟶ Y) {T' T : SchemesOver Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace f T).1) :
    SmallEtale B S hS (baseChangeSpace f T').1 :=
  (smallBaseChange B S hS (baseChangeMap f β)
    (relativelyRepresentable_baseChangeMap B S hS f β)).obj U

/-- The chart structure morphism of the base-changed chart is the cartesian projection to
`X_{T'}` of the representability square. -/
theorem stageChart_obj_hom (f : X ⟶ Y) {T' T : SchemesOver Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace f T).1) :
    (stageChart B S hS f β U).obj.hom =
      (relativelyRepresentable_baseChangeMap B S hS f β).fst U.1.hom := rfl

/-- The base change of a surjective chart is surjective: it is a base change of it. -/
theorem isSurjective_stageChart (f : X ⟶ Y) {T' T : SchemesOver Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace f T).1)
    (hU : IsSurjective B S hS U.obj.hom) :
    IsSurjective B S hS (stageChart B S hS f β U).obj.hom := by
  have hrep := relativelyRepresentable_baseChangeMap B S hS f β
  have hsq : IsPullback
      (ObjectProperty.homMk (yoneda.map (hrep.snd U.1.hom)) :
        representedAlgebraicSpace B S hS (hrep.pullback U.1.hom) ⟶
          representedAlgebraicSpace B S hS U.1.left)
      (ObjectProperty.homMk (hrep.fst U.1.hom) :
        representedAlgebraicSpace B S hS (hrep.pullback U.1.hom) ⟶ baseChangeSpace f T')
      (ObjectProperty.homMk U.1.hom :
        representedAlgebraicSpace B S hS U.1.left ⟶ baseChangeSpace f T)
      (baseChangeMap f β) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) (hrep.isPullback U.1.hom).flip
  exact isSurjective_of_isPullback B S hS hsq hU

/-- **The base-changed chart of `X_{T'}` is the fibre product, over the earlier test scheme, of
the chart of `X_T` and the later test scheme.**  The square of presheaves is the
representability square of the transition morphism `X_{T'} ⟶ X_T` pasted with the cartesian
square of the two base changes, and all four of its corners are representable. -/
theorem isPullback_yoneda_stageChart (f : X ⟶ Y) {T' T : SchemesOver Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace f T).1) :
    IsPullback
      (yoneda.map ((relativelyRepresentable_baseChangeMap B S hS f β).snd U.1.hom))
      (yoneda.map (identityTargetChartDiagram B S hS (baseChangeInclusion f T')
        (stageChart B S hS f β U)).g)
      (yoneda.map (identityTargetChartDiagram B S hS (baseChangeInclusion f T) U).g)
      (yoneda.map β.left) := by
  have hrep := relativelyRepresentable_baseChangeMap B S hS f β
  have hpaste := (hrep.isPullback U.1.hom).paste_horiz
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap f β)).flip
  refine IsPullback.of_eq hpaste.flip rfl
    (yoneda_map_identityTargetChartDiagram_g B S hS (baseChangeInclusion f T')
      (stageChart B S hS f β U)).symm
    (yoneda_map_identityTargetChartDiagram_g B S hS (baseChangeInclusion f T) U).symm rfl

/-- The same square in the big fppf category, by full faithfulness of the Yoneda embedding. -/
theorem isPullback_site_stageChart (f : X ⟶ Y) {T' T : SchemesOver Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace f T).1) :
    IsPullback ((relativelyRepresentable_baseChangeMap B S hS f β).snd U.1.hom)
      (identityTargetChartDiagram B S hS (baseChangeInclusion f T')
        (stageChart B S hS f β U)).g
      (identityTargetChartDiagram B S hS (baseChangeInclusion f T) U).g β.left :=
  IsPullback.of_map_of_faithful yoneda (isPullback_yoneda_stageChart B S hS f β U)

/-- **The same square as a cartesian square of schemes.** -/
theorem isPullback_chartScheme_stageChart (f : X ⟶ Y) {T' T : SchemesOver Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace f T).1) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_baseChangeMap B S hS f β).snd U.1.hom))
      ((BigFppfOver.toScheme B S hS).map (identityTargetChartDiagram B S hS
        (baseChangeInclusion f T') (stageChart B S hS f β U)).g)
      ((BigFppfOver.toScheme B S hS).map
        (identityTargetChartDiagram B S hS (baseChangeInclusion f T) U).g)
      ((BigFppfOver.toScheme B S hS).map β.left) :=
  (isPullback_site_stageChart B S hS f β U).map (BigFppfOver.toScheme B S hS)

/-! ### The scheme-level situation attached to a chart of `X_T` -/

namespace FlatDimensionSituation

/-- The base change `F_T` of the module of Situation 0CWU to a test scheme is quasi-coherent on
the small étale site. -/
theorem isQuasicoherentOnSite_baseChangeModule (D : FlatDimensionSituation.{u} B S hS)
    (T : SchemesOver D.Y) :
    (D.toFlatnessSituation.baseChangeModule T).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (baseChangeProjection D.f T) D.F D.quasicoherent

/-- **The scheme-level flat-dimension situation of Stacks 05MT read on a chart of `X_T`.**  An
étale scheme chart `U` of the base change `X_T` to a test scheme `T` sits over the scheme
underlying `T`, and the restriction of `F_T` to `U` is a quasi-coherent module of finite type on
it, so the chart morphism `U ⟶ T` and that restriction form a situation of Stacks 05MT. -/
def stageSituation (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    _root_.AlgebraicGeometry.FlatDimensionSituation.{u} :=
  { S := (BigFppfOver.toScheme B S hS).obj T.left
    X := chartScheme U
    f := (BigFppfOver.toScheme B S hS).map
      (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) U).g
    locallyOfFiniteType :=
      locallyOfFiniteType_chartDiagram B S hS (D.isLocallyOfFiniteType_baseChangeInclusion T)
        (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) U)
    F := restrictToChart B S hS (baseChangeSpace D.f T).2
      (D.toFlatnessSituation.baseChangeModule T) U
    isQuasicoherent := isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS
      (baseChangeSpace D.f T) _ (D.isQuasicoherentOnSite_baseChangeModule B S hS T) U
    isFiniteType := isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS
      (baseChangeSpace D.f T) _ (D.isQuasicoherentOnSite_baseChangeModule B S hS T)
      (D.isFiniteTypeOnSite_baseChangeModule T) U
    n := n }

/-- The base scheme of the stage situation is the scheme underlying the test scheme `T`. -/
@[simp]
theorem stageSituation_S (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageSituation B S hS n T U).S = (BigFppfOver.toScheme B S hS).obj T.left := rfl

/-- The dimension bound of the stage situation is `n`. -/
@[simp]
theorem stageSituation_n (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageSituation B S hS n T U).n = n := rfl

/-- The structure morphism of the stage situation is the vertical morphism of the chart diagram
at the identity chart of `T`. -/
theorem stageSituation_f (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageSituation B S hS n T U).f = (BigFppfOver.toScheme B S hS).map
      (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) U).g := rfl

/-- The module of the stage situation is the restriction of the base change `F_T` to the
chart `U`. -/
theorem stageSituation_F (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageSituation B S hS n T U).F = restrictToChart B S hS (baseChangeSpace D.f T).2
      (D.toFlatnessSituation.baseChangeModule T) U := rfl

/-- The base change `F_T` of a module of finite presentation on the small étale site is again of
finite presentation on the small étale site.  This is **Stacks 03DO** for the clause 03DL (7). -/
theorem isFinitePresentationOnSite_baseChangeModule (D : FlatDimensionSituation.{u} B S hS)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F) (T : SchemesOver D.Y) :
    SheafOfModules.IsFinitePresentationOnSite (D.toFlatnessSituation.baseChangeModule T) := by
  rw [FlatnessSituation.baseChangeModule_eq]
  exact isFinitePresentationOnSite_modulePullback B S hS (baseChangeProjection D.f T) D.F hF

/-- The chart morphism presenting a stage is locally of finite presentation when `f` is: local
finite presentation passes to the base change `f_T` by **Stacks 03XR** and then to the scheme
morphism of a commuting square of étale scheme charts. -/
theorem locallyOfFinitePresentation_stageSituation_f (D : FlatDimensionSituation.{u} B S hS)
    (n : ℕ) (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    LocallyOfFinitePresentation (D.stageSituation B S hS n T U).f :=
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  locallyOfFinitePresentation_chartDiagram B S hS
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃_F _G : AlgebraicSpaces B S hS⦄ (g : _F ⟶ _G) =>
        IsLocallyOfFinitePresentation B S hS g.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) hlfp)
    (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) U)

/-- The chart morphism presenting a stage over an affine test scheme by an affine chart is
quasi-compact: its source is an affine, hence compact, scheme and its target is affine. -/
theorem quasiCompact_stageSituation_f (D : FlatDimensionSituation.{u} B S hS) (n : ℕ)
    (T : SchemesOver D.Y) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) (hU : IsAffine (chartScheme U)) :
    QuasiCompact (D.stageSituation B S hS n T U).f := by
  have hS₀ : IsAffine (D.stageSituation B S hS n T U).S := hT
  have hX₀ : IsAffine (D.stageSituation B S hS n T U).X := hU
  have haff : _root_.AlgebraicGeometry.IsAffineHom (D.stageSituation B S hS n T U).f :=
    inferInstance
  infer_instance

/-- The module presenting a stage is of finite presentation when `ℱ` is: finite presentation
passes to the base change `F_T` and then to its restriction to an étale scheme chart. -/
theorem isFinitePresentation_stageSituation_F (D : FlatDimensionSituation.{u} B S hS) (n : ℕ)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F) (T : SchemesOver D.Y)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (D.stageSituation B S hS n T U).F.IsFinitePresentation := by
  have hfp := D.isFinitePresentationOnSite_baseChangeModule B S hS hF T
  have := hfp
  exact isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS
    (baseChangeSpace D.f T) (D.toFlatnessSituation.baseChangeModule T) inferInstance hfp U

/-- The restriction of `F_{T'}` to the base change of a chart `U` of `X_T` is the scheme-level
inverse image of the restriction of `F_T` to `U`.

This is the base change of the chart restriction of a quasi-coherent module,
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, at the representability square of the
transition morphism `X_{T'} ⟶ X_T`, followed by the composition comparison of Stacks 03LU which
identifies the inverse image of `F_T` along that transition morphism with `F_{T'}`. -/
def stageModuleIso (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) {T' T : SchemesOver D.Y}
    (β : T' ⟶ T) (U : SmallEtale B S hS (baseChangeSpace D.f T).1) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_baseChangeMap B S hS D.f β).snd U.1.hom))).obj
        (D.stageSituation B S hS n T U).F ≅
      restrictToChart B S hS (baseChangeSpace D.f T').2
        (D.toFlatnessSituation.baseChangeModule T') (stageChart B S hS D.f β U) :=
  restrictToChartBaseChangeIso B S hS (baseChangeMap D.f β)
      (D.toFlatnessSituation.baseChangeModule T)
      (D.isQuasicoherentOnSite_baseChangeModule B S hS T) U (stageChart B S hS D.f β U)
      ((relativelyRepresentable_baseChangeMap B S hS D.f β).snd U.1.hom)
      ((relativelyRepresentable_baseChangeMap B S hS D.f β).w U.1.hom).symm ≪≫
    restrictToChartIso B S hS (baseChangeSpace D.f T').2
      ((modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f β)).app D.F).symm
      (stageChart B S hS D.f β U)

/-- **The condition of Stacks 0CWT over a test scheme, read on a chart of an earlier stage.**
Let `U` be a surjective étale scheme chart of the base change `X_T` of Situation 0CWU to a test
scheme `T`, and let `E` be the scheme-level situation of Stacks 05MT it presents.  Then for
every test scheme `T'` over `T`, the base change `F_{T'}` is flat over `T'` in dimensions `≥ n`
exactly when the base change of `E` to `T'`, viewed as a scheme over the scheme underlying `T`,
is flat over it in dimensions `≥ n`.

This is the chart clause of **Stacks 0CWS** for the morphism `f_{T'}`, read at the commuting
square of étale scheme charts whose source chart is the base change of `U` to `X_{T'}` and whose
target chart is the identity chart of `T'`.  Both charts of that square are surjective, so the
condition on it is the condition on every square by the equivalence of conditions (1) and (2) of
Stacks 0CWS; the square is cartesian over the chart morphism of `U` by
`AlgebraicGeometry.Space.isPullback_chartScheme_stageChart`, and the two modules agree by
`AlgebraicGeometry.Space.stageModuleIso`. -/
theorem isFlatInDimensionsGEAfterBaseChange_iff_stageSituation
    (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) {T' T : SchemesOver D.Y} (β : T' ⟶ T)
    (U : SmallEtale B S hS (baseChangeSpace D.f T).1)
    (hU : IsSurjective B S hS U.obj.hom) :
    D.IsFlatInDimensionsGEAfterBaseChange T' n ↔
      (D.stageSituation B S hS n T U).IsFlatInDimensionsGEAfterBaseChange
        (Over.mk ((BigFppfOver.toScheme B S hS).map β.left)) := by
  have hfT' : IsLocallyOfFiniteType B S hS (baseChangeInclusion D.f T').hom :=
    D.isLocallyOfFiniteType_baseChangeInclusion T'
  have hqcT' : (D.toFlatnessSituation.baseChangeModule T').IsQuasicoherentOnSite :=
    D.isQuasicoherentOnSite_baseChangeModule B S hS T'
  have hqcC : IsQuasicoherentOnCharts B S hS (baseChangeSpace D.f T').2
      (D.toFlatnessSituation.baseChangeModule T') :=
    isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS (baseChangeSpace D.f T') _ hqcT'
  have hftC : IsFiniteTypeOnCharts B S hS (baseChangeSpace D.f T').2
      (D.toFlatnessSituation.baseChangeModule T') :=
    isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS (baseChangeSpace D.f T') _ hqcT'
      (D.isFiniteTypeOnSite_baseChangeModule T')
  have hlftT := (D.stageSituation B S hS n T U).locallyOfFiniteType
  have hlftT' : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T')
        (stageChart B S hS D.f β U)).g) :=
    locallyOfFiniteType_chartDiagram B S hS hfT'
      (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T') (stageChart B S hS D.f β U))
  have hqcW : (restrictToChart B S hS (baseChangeSpace D.f T').2
      (D.toFlatnessSituation.baseChangeModule T')
      (stageChart B S hS D.f β U)).IsQuasicoherent := hqcC (stageChart B S hS D.f β U)
  have hftW : (restrictToChart B S hS (baseChangeSpace D.f T').2
      (D.toFlatnessSituation.baseChangeModule T')
      (stageChart B S hS D.f β U)).IsFiniteType := hftC (stageChart B S hS D.f β U)
  have hqcE : (D.stageSituation B S hS n T U).F.IsQuasicoherent :=
    (D.stageSituation B S hS n T U).isQuasicoherent
  have hftE : (D.stageSituation B S hS n T U).F.IsFiniteType :=
    (D.stageSituation B S hS n T U).isFiniteType
  have hqcP : ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_baseChangeMap B S hS D.f β).snd U.1.hom))).obj
      (D.stageSituation B S hS n T U).F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _
      ((BigFppfOver.toScheme B S hS).map ((relativelyRepresentable_baseChangeMap B S hS D.f
        β).snd U.1.hom)).toLRSHom.toShHom (D.stageSituation B S hS n T U).F hqcE
  have hftP : ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
      ((relativelyRepresentable_baseChangeMap B S hS D.f β).snd U.1.hom))).obj
      (D.stageSituation B S hS n T U).F).IsFiniteType :=
    @SheafOfModules.pullback_isFiniteType _ _
      ((BigFppfOver.toScheme B S hS).map ((relativelyRepresentable_baseChangeMap B S hS D.f
        β).snd U.1.hom)).toLRSHom.toShHom (D.stageSituation B S hS n T U).F hftE
  have hsq := isPullback_chartScheme_stageChart B S hS D.f β U
  have hchart : IsFlatOverInDimensionsGEOnChartDiagram B S hS (baseChangeSpace D.f T').2
        (D.toFlatnessSituation.baseChangeModule T')
        (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T')
          (stageChart B S hS D.f β U)) n ↔
      (D.stageSituation B S hS n T U).IsFlatInDimensionsGEAfterBaseChange
        (Over.mk ((BigFppfOver.toScheme B S hS).map β.left)) :=
    ⟨fun h => @flatInDimensions_canonical_of_isPullback _ _ _ _ _ _ _ _ hsq hlftT hlftT'
        (D.stageSituation B S hS n T U).F hqcE hftE n
        (@IsFlatOverInDimensionsGE.of_moduleIso _ _ _ hlftT' _ _ hqcW hftW hqcP hftP
          (stageModuleIso B S hS D n β U).symm n h),
      fun h => @IsFlatOverInDimensionsGE.of_moduleIso _ _ _ hlftT' _ _ hqcP hftP hqcW hftW
        (stageModuleIso B S hS D n β U) n
        (@flatInDimensions_of_isPullback_canonical _ _ _ _ _ _ _ _ hsq hlftT hlftT'
          (D.stageSituation B S hS n T U).F hqcE hftE n h)⟩
  refine Iff.trans ?_ hchart
  refine ⟨fun h => h _, fun h => ?_⟩
  refine (isFlatOverInDimensionsGEOnSomeChartDiagram_iff_onEveryChartDiagram B S hS
    (baseChangeInclusion D.f T') (D.toFlatnessSituation.baseChangeModule T') hfT' hqcC hftC n).1
    ⟨identityTargetChartDiagram B S hS (baseChangeInclusion D.f T')
      (stageChart B S hS D.f β U), ?_, ?_, h⟩
  · exact isSurjective_stageChart B S hS D.f β U hU
  · exact isSurjective_idEtaleChart B S hS T'.left

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
