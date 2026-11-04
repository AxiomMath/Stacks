module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeMapEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The scheme-level presentation of `F_n` does not depend on the chart

In Situation 0CWU, let `T` be a test scheme over `Y` and `U` a surjective étale chart of the base
change `X_T`. The chart presents the restriction of `F_n` to the schemes over `T` as the functor
of the scheme-level situation of Stacks 05MT on `U ⟶ T`,
`AlgebraicGeometry.Space.FlatDimensionSituation.stageSituation`. That identification is made in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatDimensionStagePresentation.lean` for test schemes of the
site only. This file shows that the scheme-level functor itself, on *all* schemes over `T`, does
not depend on the surjective chart chosen.

## Main definitions

* `AlgebraicGeometry.Space.chartPairObject`: the fibre product `U ×_F V` of two étale charts of a
  presheaf, an object of the site because the charts are representable morphisms.
* `AlgebraicGeometry.Space.chartPair`: the same as an étale chart of `F`, with its two
  projections `chartPairFst`, `chartPairSnd` to `U` and `V`.
* `AlgebraicGeometry.Space.restrictToChartMapIso`: the restriction of a quasi-coherent module to a
  chart pulls back along a morphism of charts to its restriction to the smaller chart.

## Main results

* `AlgebraicGeometry.Space.exists_chartPair_point`: two chart points with the same image in `|F|`
  are the two images of a point of `U ×_F V`, which is Stacks 03H4.
* `AlgebraicGeometry.Space.FlatDimensionSituation.stageSituation_isFlat_iff_of_chartMap`: a
  morphism of charts whose scheme map is surjective identifies the two scheme-level functors.
* `AlgebraicGeometry.Space.FlatDimensionSituation.stageSituation_isFlat_iff_of_isSurjective`:
  two surjective charts give the same scheme-level functor.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 05UD](https://stacks.math.columbia.edu/tag/05UD)
* [Stacks Project, Tag 0CWS](https://stacks.math.columbia.edu/tag/0CWS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The fibre product of two étale charts -/

section ChartPair

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The fibre product `U ×_F V` of two étale charts of `F`, an object of the site: the first
chart is a representable morphism. -/
abbrev chartPairObject (U V : SmallEtale B S hS F) : BigFppfOver B S hS :=
  U.property.rep.pullback V.obj.hom

/-- The projection `U ×_F V ⟶ U`. -/
abbrev chartPairFstHom (U V : SmallEtale B S hS F) : chartPairObject U V ⟶ U.obj.left :=
  U.property.rep.fst' V.obj.hom

/-- The projection `U ×_F V ⟶ V`. -/
abbrev chartPairSndHom (U V : SmallEtale B S hS F) : chartPairObject U V ⟶ V.obj.left :=
  U.property.rep.snd V.obj.hom

/-- The fibre product of two étale charts is cartesian over `F`. -/
theorem isPullback_chartPair (U V : SmallEtale B S hS F) :
    IsPullback (yoneda.map (chartPairFstHom U V)) (yoneda.map (chartPairSndHom U V))
      U.obj.hom V.obj.hom :=
  U.property.rep.isPullback' V.obj.hom

/-- The fibre product `U ×_F V` as an étale chart of `F`, through `V`. -/
def chartPair (U V : SmallEtale B S hS F) : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk (yoneda.map (chartPairSndHom U V) ≫ V.obj.hom), by
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
      inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
    have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    have hsnd : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (chartPairSndHom U V)) :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (isPullback_chartPair U V) U.property
    exact hcomp.comp_mem _ _ hsnd V.property⟩

/-- The projection `U ×_F V ⟶ V` as a morphism of étale charts. -/
def chartPairSnd (U V : SmallEtale B S hS F) : chartPair U V ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartPairSndHom U V) rfl)

/-- The projection `U ×_F V ⟶ U` as a morphism of étale charts. -/
def chartPairFst (U V : SmallEtale B S hS F) : chartPair U V ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartPairFstHom U V)
    (isPullback_chartPair U V).w)

/-- The underlying morphism of `chartPairSnd U V` is the projection `chartPairSndHom U V`. -/
@[simp]
theorem chartPairSnd_hom_left (U V : SmallEtale B S hS F) :
    (chartPairSnd U V).hom.left = chartPairSndHom U V := rfl

/-- The underlying morphism of `chartPairFst U V` is the projection `chartPairFstHom U V`. -/
@[simp]
theorem chartPairFst_hom_left (U V : SmallEtale B S hS F) :
    (chartPairFst U V).hom.left = chartPairFstHom U V := rfl

/-- If a morphism of the site sends a point `w` to the image of `p` under the inverse comparison
bijection, then it sends the scheme point of `w` to `p`. -/
private theorem map_pointsToScheme_eq_of_pointsMap_eq {Z V : BigFppfOver B S hS} (g : Z ⟶ V)
    (w : points B S hS (yoneda.obj Z)) (p : (BigFppfOver.toScheme B S hS).obj V)
    (hw : pointsMap B S hS (yoneda.obj Z) (yoneda.map g) w = (pointsEquivScheme B S hS V).symm p) :
    (BigFppfOver.toScheme B S hS).map g (pointsToScheme B S hS Z w) = p := by
  rw [← pointsToScheme_pointsMap_yoneda, hw]
  exact (pointsEquivScheme B S hS _).apply_symm_apply p

/-- **Stacks 03H4 for two étale charts.** A point of the scheme of `U` and a point of the scheme
of `V` with the same image in `|F|` are the two projections of a point of the scheme of
`U ×_F V`. -/
theorem exists_chartPair_point (U V : SmallEtale B S hS F) (x : chartScheme U)
    (y : chartScheme V) (h : chartSchemeToPoints B S hS F U x = chartSchemeToPoints B S hS F V y) :
    ∃ r : chartScheme (chartPair U V),
      chartSchemeMap (chartPairFst U V) r = x ∧ chartSchemeMap (chartPairSnd U V) r = y := by
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm,
    chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm] at h
  obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback_presheaf B S hS (isPullback_chartPair U V)
    _ _ h
  exact ⟨pointsToScheme B S hS (chartPairObject U V) w,
    map_pointsToScheme_eq_of_pointsMap_eq _ _ _ hw₁,
    map_pointsToScheme_eq_of_pointsMap_eq _ _ _ hw₂⟩

/-- The scheme map of the projection `U ×_F V ⟶ U` is surjective when `V` covers `|F|`. -/
theorem surjective_chartSchemeMap_chartPairFst (U V : SmallEtale B S hS F)
    (hV : Function.Surjective (chartSchemeToPoints B S hS F V)) :
    Function.Surjective (chartSchemeMap (chartPairFst U V)) := by
  intro x
  obtain ⟨y, hy⟩ := hV (chartSchemeToPoints B S hS F U x)
  obtain ⟨r, hr, -⟩ := exists_chartPair_point U V x y hy.symm
  exact ⟨r, hr⟩

/-- The scheme map of the projection `U ×_F V ⟶ V` is surjective when `U` covers `|F|`. -/
theorem surjective_chartSchemeMap_chartPairSnd (U V : SmallEtale B S hS F)
    (hU : Function.Surjective (chartSchemeToPoints B S hS F U)) :
    Function.Surjective (chartSchemeMap (chartPairSnd U V)) := by
  intro y
  obtain ⟨x, hx⟩ := hU (chartSchemeToPoints B S hS F V y)
  obtain ⟨r, -, hr⟩ := exists_chartPair_point U V x y hx
  exact ⟨r, hr⟩

end ChartPair

/-- A chart which is surjective on points of the space it charts is surjective as a map from its
scheme. -/
theorem surjective_chartSchemeToPoints_of_isSurjective {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS F) (hU : IsSurjective B S hS U.obj.hom) :
    Function.Surjective (chartSchemeToPoints B S hS F U) := by
  intro p
  obtain ⟨q, rfl⟩ := hU p
  refine ⟨pointsToScheme B S hS _ q, ?_⟩
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
  exact congrArg _ ((pointsEquivScheme B S hS _).symm_apply_apply q)

/-! ### Restriction of a module along a morphism of charts -/

/-- The restriction of a quasi-coherent module to an étale chart pulls back along a morphism of
charts to its restriction to the smaller chart. This is
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso` along the identity of the space, followed
by the unit law of Stacks 03LU. -/
def restrictToChartMapIso (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite) {U W : SmallEtale B S hS X.1} (k : W ⟶ U) :
    (Scheme.Modules.pullback (chartSchemeMap k)).obj (restrictToChart B S hS X.2 G U) ≅
      restrictToChart B S hS X.2 G W :=
  restrictToChartBaseChangeIso B S hS (𝟙 X) G hG U W k.hom.left
      (by simp) ≪≫
    restrictToChartIso B S hS X.2 ((modulePullbackIdIso B S hS X).app G) W

/-! ### Independence of the chart -/

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u} B S hS) (n : ℕ)

/-- The chart morphism of the stage presented by a smaller chart factors through the larger
chart. -/
theorem stageSituation_f_eq_of_chartMap {T : SchemesOver D.Y}
    {U W : SmallEtale B S hS (baseChangeSpace D.f T).1} (k : W ⟶ U) :
    (D.stageSituation B S hS n T W).f = chartSchemeMap k ≫ (D.stageSituation B S hS n T U).f := by
  rw [stageSituation_f, stageSituation_f]
  have hg : (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) W).g =
      (SmallEtale.toOver B S hS _).map k ≫
        (identityTargetChartDiagram B S hS (baseChangeInclusion D.f T) U).g := by
    apply yoneda.map_injective
    refine (yoneda_map_identityTargetChartDiagram_g B S hS _ W).trans ?_
    refine Eq.trans ?_ (yoneda.map_comp _ _).symm
    refine Eq.trans ?_ (congrArg (yoneda.map ((SmallEtale.toOver B S hS _).map k) ≫ ·)
      (yoneda_map_identityTargetChartDiagram_g B S hS _ U).symm)
    exact Eq.trans (congrArg (· ≫ (baseChangeInclusion D.f T).hom)
      (((SmallEtale.inclusion B S hS _).map k).w).symm) (Category.assoc _ _ _)
  rw [hg]
  exact Functor.map_comp _ _ _

/-- **The scheme-level presentation along a morphism of charts.** Let `k : W ⟶ U` be a morphism
of étale charts of `X_T` whose scheme map is surjective. Then the scheme-level situations
presented by `W` and by `U` have the same functor, on all schemes over `T`. -/
theorem stageSituation_isFlat_iff_of_chartMap {T : SchemesOver D.Y}
    {U W : SmallEtale B S hS (baseChangeSpace D.f T).1} (k : W ⟶ U)
    (hk : Function.Surjective (chartSchemeMap k)) (T' : Over (D.stageSituation B S hS n T U).S) :
    (D.stageSituation B S hS n T W).IsFlatInDimensionsGEAfterBaseChange T' ↔
      (D.stageSituation B S hS n T U).IsFlatInDimensionsGEAfterBaseChange T' := by
  let h : (D.stageSituation B S hS n T W).X ⟶ (D.stageSituation B S hS n T U).X :=
    chartSchemeMap k
  have : Etale h := etale_chartSchemeMap k
  let f' : (D.stageSituation B S hS n T W).X ⟶ (D.stageSituation B S hS n T U).S :=
    (D.stageSituation B S hS n T W).f
  have : LocallyOfFiniteType f' := (D.stageSituation B S hS n T W).locallyOfFiniteType
  have := (D.stageSituation B S hS n T W).isQuasicoherent
  have := (D.stageSituation B S hS n T W).isFiniteType
  exact (D.stageSituation B S hS n T U).isFlat_iff_of_surjective_etale h hk (f' := f')
    (F' := (D.stageSituation B S hS n T W).F)
    (D.stageSituation_f_eq_of_chartMap n k)
    (restrictToChartMapIso (baseChangeSpace D.f T) (D.toFlatnessSituation.baseChangeModule T)
      (D.isQuasicoherentOnSite_baseChangeModule B S hS T) k).symm T'

/-- **Independence of the chart.** Two surjective étale charts `U` and `V` of `X_T` present the
same scheme-level functor on all schemes over `T`: both are compared with the chart
`U ×_{X_T} V`, whose two projections are surjective. -/
theorem stageSituation_isFlat_iff_of_isSurjective {T : SchemesOver D.Y}
    (U V : SmallEtale B S hS (baseChangeSpace D.f T).1) (hU : IsSurjective B S hS U.obj.hom)
    (hV : IsSurjective B S hS V.obj.hom) (T' : Over ((BigFppfOver.toScheme B S hS).obj T.left)) :
    (D.stageSituation B S hS n T U).IsFlatInDimensionsGEAfterBaseChange T' ↔
      (D.stageSituation B S hS n T V).IsFlatInDimensionsGEAfterBaseChange T' :=
  (D.stageSituation_isFlat_iff_of_chartMap n (chartPairFst U V)
      (surjective_chartSchemeMap_chartPairFst U V
        (surjective_chartSchemeToPoints_of_isSurjective V hV)) T').symm.trans
    (D.stageSituation_isFlat_iff_of_chartMap n (chartPairSnd U V)
      (surjective_chartSchemeMap_chartPairSnd U V
        (surjective_chartSchemeToPoints_of_isSurjective U hU)) T')

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
