module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StageChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedFinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusOfCutoffBoundedApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChowDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# Étale charts of a stage, base changed to a limit bounded by the cutoff

`StacksFrontier/AlgebraicGeometry/Spaces/Limits/StageChartSystem.lean` base changes an étale chart
`T` of a stage `X_j` of a cofiltered system `X = lim Xᵢ` to the later stages and to the limit, and
shows that the regular functions on `T_∞ = T ×_{X_j} X` are the colimit of those on the
`T_s = T ×_{X_j} X_s`, for an index category below the cofinality of the site's cutoff. This file
does the same for a system bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no condition on the cofinality.

The cofinality bound enters the bounded development in exactly three places, and each is replaced
here:

* the limit is an algebraic space (`AlgebraicGeometry.Space.isAlgebraicSpace_limit`), replaced by
  `AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_isCutoffBoundedSystem`;
* the projections of the limit are affine (Stacks 07SF, part (1)), replaced by
  `AlgebraicGeometry.Space.isAffineHom_limitπ_of_isCutoffBoundedSystem`;
* the regular functions on `T_∞` are the colimit of those on the `T_s`, which the bounded form
  takes from Stacks 0CP4 for the affine line. Here the `T_s` are represented by the objects of the
  diagram `AlgebraicGeometry.Space.laterStageChartDiagram` of the site, `T_∞` by its limit, and the
  underlying scheme functor preserves that limit
  (`AlgebraicGeometry.Space.isLimit_toScheme_mapCone_of_baseChangeSizeBounded`, from
  `AlgebraicGeometry.Space.preservesLimit_toScheme_of_overLift_of_baseChangeSizeBounded`). The
  statement is then the one for a cofiltered limit of quasi-compact and quasi-separated schemes
  with affine transition morphisms (`AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` and
  `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit`).

Every other declaration of the bounded file that mentions the limit is repeated here, in the
namespace `AlgebraicGeometry.Space.IsCutoffBoundedSystem`, with the same proof; the
declarations about the stages alone are used as they are.

## Main results

* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.limitAlgebraicSpace`: the limit of a system
  bounded by the cutoff, as an algebraic space.
* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_gpb_limToStage_eq`: every regular
  function on `T_∞` comes from a stage.
* `AlgebraicGeometry.Space.IsCutoffBoundedSystem.exists_gpb_stageToStage_eq`: two regular
  functions on a stage which agree on `T_∞` agree on a later stage.

## References

* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Scheme limits of represented systems bounded by the cutoff -/

section SchemeLimit

variable {J : Type u} [Category.{u} J] (E : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (W : J ⥤ BigFppfOver B S hS) (e : W ⋙ yoneda ≅ E)

include e in
/-- If a diagram of the site represents a system with affine transition morphisms, its
underlying schemes have affine transition morphisms. -/
theorem isAffineHom_toScheme_map_of_iso
    (hAffine : ∀ {i j : J} (f : i ⟶ j), IsAffineHom B S hS (E.map f)) {a b : J} (f : a ⟶ b) :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (W.map f)) := by
  apply isAffineHom_toScheme_map_of_isAffineHom B S hS
  have h : yoneda.map (W.map f) = e.hom.app a ≫ E.map f ≫ e.inv.app b := by
    have hn := e.hom.naturality f
    simp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp
  rw [h]
  exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _)
    (isAffineHom_comp B S hS _ _ (hAffine f) (isAffineHom_of_isIso _))

include e in
/-- **A limit in the site of a represented system bounded by the cutoff is a limit of
schemes.** Let `W` be a cofiltered diagram of the site representing a system `E` of presheaves
with affine transition morphisms, with fewer objects than the cutoff, its hom types bounded by
one cardinal below the cutoff and uniformly bounded base changes. Then the underlying scheme
functor sends every limit cone of `W` to a limit cone.

This is `AlgebraicGeometry.Space.preservesLimit_toScheme_of_overLift_of_baseChangeSizeBounded`
at any object `i₀`, carried from the slice over `i₀` to the whole index category, along which
the forgetful functor is initial. -/
theorem nonempty_isLimit_toScheme_mapCone_of_baseChangeSizeBounded [IsCofiltered J]
    {ν : Cardinal.{u}}
    (hSize : #J < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : J, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS E)
    (hAffine : ∀ {i j : J} (f : i ⟶ j), IsAffineHom B S hS (E.map f)) {c : Cone W}
    (hc : IsLimit c) : Nonempty (IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := J)
  have := preservesLimit_toScheme_of_overLift_of_baseChangeSizeBounded E hSize hν hHomSize hB
    hAffine i₀ (Over.forget i₀ ⋙ W)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (Over.forget i₀) e)
  have h1 : IsLimit (c.whisker (Over.forget i₀)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc
  exact ⟨(Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) _)
    (isLimitOfPreserves (BigFppfOver.toScheme B S hS) h1)⟩

end SchemeLimit

/-! ### The base changes of a chart as a diagram of the site -/

section ChartDiagram

variable (B S hS)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
  {j : I} (T : SmallEtale B S hS (D.obj j))

/-- The base changes `T ×_{X_j} X_s` of an étale chart `T` of a stage to the later stages, as a
diagram of the site. -/
def laterStageChartDiagram : Over j ⥤ BigFppfOver B S hS where
  obj s := (laterStageChart B S hS D hD hAffine T s).obj.left
  map d := stageToStage B S hS D hD hAffine T d
  map_id s := by
    apply yoneda.map_injective
    rw [← cancel_mono (stageChartIso B S hS D hD hAffine T s).hom,
      ← stageChartIso_comp B S hS D hD hAffine T (𝟙 s)]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp d d' := stageToStage_comp B S hS D hD hAffine T d' d

/-- The diagram of the site represents the presheaf base changes. -/
def laterStageChartDiagramIso :
    laterStageChartDiagram B S hS D hD hAffine T ⋙ yoneda ≅ stageChartDiagram B S hS D T :=
  NatIso.ofComponents (fun s => stageChartIso B S hS D hD hAffine T s)
    (fun d => (stageChartIso_comp B S hS D hD hAffine T d).symm)

include hD hAffine in
/-- **Uniformly bounded base changes pass to the base changes of a chart.** -/
theorem baseChangeSizeBounded_chartDiagram (hB : BaseChangeSizeBounded B S hS D) :
    BaseChangeSizeBounded B S hS (stageChartDiagram B S hS D T) := by
  let η : stageChartDiagram B S hS D T ⟶ Over.forget j ⋙ D :=
    { app := fun s => pullback.fst _ _
      naturality := fun _ _ d => stageChartDiagram_map_fst B S hS D T d }
  refine baseChangeSizeBounded_of_jointlyMono B S hS η ?_ hD hAffine hB
  intro s s' d Z x y h₁ h₂
  refine pullback.hom_ext h₂ ?_
  rw [← stageChartDiagram_map_snd B S hS D T d, ← Category.assoc, h₁, Category.assoc]

end ChartDiagram

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.IsCutoffBoundedSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The limit of a system bounded by the cutoff -/

variable (B S hS)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hc : IsCutoffBoundedSystem B S hS D)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- The limit of a system bounded by the cutoff, as an object of the category of algebraic
spaces over `S`. -/
def limitAlgebraicSpace : AlgebraicSpaces B S hS :=
  ⟨limit D, isAlgebraicSpace_limit_of_isCutoffBoundedSystem B S hS D hc hD hAffine⟩

/-- The projection of the limit to a stage, as a morphism of algebraic spaces over `S`. -/
def limitProjection (i : I) :
    limitAlgebraicSpace B S hS D hc hD hAffine ⟶ stageAlgebraicSpace B S hS D hD i :=
  ObjectProperty.homMk (limit.π D i)

/-! ### Base change of a chart of a stage to the limit -/

include hAffine in
/-- The projection of the limit to a stage is relatively representable. -/
theorem rep_limitProjection (i : I) :
    yoneda.relativelyRepresentable (limitProjection B S hS D hc hD hAffine i).hom :=
  relativelyRepresentable_hom_of_isAffineHom B S hS _
    (isAffineHom_limitπ_of_isCutoffBoundedSystem B S hS D hc hAffine i)

variable {j : I} (T : SmallEtale B S hS (D.obj j))

/-- The base change of an étale chart of a stage to the limit. -/
abbrev limChart : SmallEtale B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1 :=
  (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine j)
    (rep_limitProjection B S hS D hc hD hAffine j)).obj T

/-- The square defining `limToStage` commutes: the base change to the limit maps to `X_j` in
the same way through the stage `X_s` and through `T`. -/
theorem limToStage_cond (s : Over j) :
    ((limChart B S hS D hc hD hAffine T).obj.hom ≫ limit.π D s.left) ≫
        (stageTransition B S hS D hD s.hom).hom =
      yoneda.map (sbcProj _ (rep_limitProjection B S hS D hc hD hAffine j) T) ≫
        T.obj.hom :=
  (Category.assoc _ _ _).trans ((congrArg _ (limit.w D s.hom)).trans
    (sbc_w (limitProjection B S hS D hc hD hAffine j)
      (rep_limitProjection B S hS D hc hD hAffine j) T).symm)

/-- The projection of the base change to the limit onto the base change to a stage. -/
def limToStage (s : Over j) :
    (limChart B S hS D hc hD hAffine T).obj.left ⟶
      (laterStageChart B S hS D hD hAffine T s).obj.left :=
  (rep_stageTransition B S hS D hD hAffine s.hom).lift _ _
    (limToStage_cond B S hS D hc hD hAffine T s)

/-- The projection `limToStage` followed by the projection to `T` is the projection of the base
change to the limit to `T`. -/
@[reassoc]
theorem limToStage_proj (s : Over j) :
    limToStage B S hS D hc hD hAffine T s ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T =
      sbcProj _ (rep_limitProjection B S hS D hc hD hAffine j) T :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

/-- The projection `limToStage` lies over the projection of the limit to the stage. -/
@[reassoc]
theorem limToStage_chart (s : Over j) :
    yoneda.map (limToStage B S hS D hc hD hAffine T s) ≫
        (laterStageChart B S hS D hD hAffine T s).obj.hom =
      (limChart B S hS D hc hD hAffine T).obj.hom ≫ limit.π D s.left :=
  Functor.relativelyRepresentable.lift_fst _ _ _ _

/-- The projections `limToStage` are compatible with the transition maps `stageToStage`. -/
theorem limToStage_stageToStage {s s' : Over j} (d : s' ⟶ s) :
    limToStage B S hS D hc hD hAffine T s' ≫ stageToStage B S hS D hD hAffine T d =
      limToStage B S hS D hc hD hAffine T s := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · show yoneda.map (limToStage B S hS D hc hD hAffine T s' ≫
        stageToStage B S hS D hD hAffine T d) ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom =
      yoneda.map (limToStage B S hS D hc hD hAffine T s) ≫
        (laterStageChart B S hS D hD hAffine T s).obj.hom
    exact (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom)
      (Functor.map_comp yoneda _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (stageToStage_chart B S hS D hD hAffine T d)).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.map d.left) (limToStage_chart B S hS D hc hD hAffine T
          s')).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (limit.w D d.left)).trans
      (limToStage_chart B S hS D hc hD hAffine T s).symm))))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (stageToStage_proj B S hS D hD hAffine T d)).trans
      ((limToStage_proj B S hS D hc hD hAffine T s').trans
        (limToStage_proj B S hS D hc hD hAffine T s).symm))

/-- The base change to the limit of the base change to a stage. -/
abbrev stageLimChart (s : Over j) :
    SmallEtale B S hS (limitAlgebraicSpace B S hS D hc hD hAffine).1 :=
  (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s.left)
    (rep_limitProjection B S hS D hc hD hAffine s.left)).obj
    (laterStageChart B S hS D hD hAffine T s)

/-- The two maps from the base change to the limit of the base change to a stage to the stage
`X_j`, through `T` and through the limit, agree. -/
theorem stageToLim_cond (s : Over j) :
    yoneda.map (sbcProj _ (rep_limitProjection B S hS D hc hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s) ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T) ≫ T.obj.hom =
      (stageLimChart B S hS D hc hD hAffine T s).obj.hom ≫
        (limitProjection B S hS D hc hD hAffine j).hom :=
  calc _ = yoneda.map (sbcProj _ (rep_limitProjection B S hS D hc hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s)) ≫
        (yoneda.map (sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T) ≫ T.obj.hom) := by
        rw [Functor.map_comp, Category.assoc]
    _ = yoneda.map (sbcProj _ (rep_limitProjection B S hS D hc hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s)) ≫ ((laterStageChart B S hS D hD hAffine T
            s).obj.hom ≫
          D.map s.hom) :=
        congrArg (_ ≫ ·) (sbc_w (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom) T)
    _ = (yoneda.map (sbcProj _ (rep_limitProjection B S hS D hc hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T
            s)) ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom) ≫
          D.map s.hom := (Category.assoc _ _ _).symm
    _ = ((stageLimChart B S hS D hc hD hAffine T s).obj.hom ≫ limit.π D s.left) ≫
          D.map s.hom :=
        congrArg (· ≫ D.map s.hom) (sbc_w (limitProjection B S hS D hc hD hAffine
            s.left)
          (rep_limitProjection B S hS D hc hD hAffine s.left)
          (laterStageChart B S hS D hD hAffine T s))
    _ = _ := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (limit.w D s.hom))

/-- The comparison of the base change to the limit of the base change to a stage with the base
change to the limit. -/
def stageToLim (s : Over j) :
    stageLimChart B S hS D hc hD hAffine T s ⟶ limChart B S hS D hc hD hAffine T :=
  sbcLift _ (rep_limitProjection B S hS D hc hD hAffine j) _
    (stageToLim_cond B S hS D hc hD hAffine T s)

/-- The comparison `stageToLim` followed by the projection to `T` is the composite of the
projections to the base change to the stage and to `T`. -/
theorem stageToLim_proj (s : Over j) :
    (stageToLim B S hS D hc hD hAffine T s).hom.left ≫
        sbcProj _ (rep_limitProjection B S hS D hc hD hAffine j) T =
      sbcProj _ (rep_limitProjection B S hS D hc hD hAffine s.left)
          (laterStageChart B S hS D hD hAffine T s) ≫
        sbcProj _ (rep_stageTransition B S hS D hD hAffine s.hom) T :=
  sbcLift_proj _ _ _ _

/-- **The comparison followed by the projection to the stage is the projection.** -/
theorem stageToLim_limToStage (s : Over j) :
    (stageToLim B S hS D hc hD hAffine T s).hom.left ≫
        limToStage B S hS D hc hD hAffine T s =
      sbcProj _ (rep_limitProjection B S hS D hc hD hAffine s.left)
        (laterStageChart B S hS D hD hAffine T s) := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · have h1 := limToStage_chart B S hS D hc hD hAffine T s
    have h2 := CostructuredArrow.w (stageToLim B S hS D hc hD hAffine T s).hom
    have h3 := sbc_w (limitProjection B S hS D hc hD hAffine s.left)
      (rep_limitProjection B S hS D hc hD hAffine s.left)
      (laterStageChart B S hS D hD hAffine T s)
    exact (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T s).obj.hom)
      (Functor.map_comp yoneda _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ limit.π D s.left) h2).trans h3.symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (limToStage_proj B S hS D hc hD hAffine T s)).trans
      (stageToLim_proj B S hS D hc hD hAffine T s))

/-! ### Naturality in the chart -/

section Naturality

variable {T} {T' : SmallEtale B S hS (D.obj j)} (h : T ⟶ T')

/-- The projections `limToStage` are natural in the chart `T`. -/
theorem limToStage_naturality (s : Over j) :
    ((smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine j)
        (rep_limitProjection B S hS D hc hD hAffine j)).map h).hom.left ≫
        limToStage B S hS D hc hD hAffine T' s =
      limToStage B S hS D hc hD hAffine T s ≫
        ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom.left := by
  refine Functor.relativelyRepresentable.hom_ext _ ?_ ?_
  · have h1 := limToStage_chart B S hS D hc hD hAffine T' s
    have h2 := limToStage_chart B S hS D hc hD hAffine T s
    have h3 := CostructuredArrow.w ((smallBaseChange B S hS
      (limitProjection B S hS D hc hD hAffine j)
      (rep_limitProjection B S hS D hc hD hAffine j)).map h).hom
    have h4 := CostructuredArrow.w ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom)).map h).hom
    exact (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T' s).obj.hom)
      (Functor.map_comp yoneda _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ limit.π D s.left) h3).trans (h2.symm.trans
      ((congrArg (_ ≫ ·) h4).symm.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (laterStageChart B S hS D hD hAffine T' s).obj.hom)
        (Functor.map_comp yoneda _ _).symm))))))))
  · have h1 := limToStage_proj B S hS D hc hD hAffine T' s
    have h2 := limToStage_proj B S hS D hc hD hAffine T s
    have h3 := smallBaseChange_map_proj (limitProjection B S hS D hc hD hAffine j)
      (rep_limitProjection B S hS D hc hD hAffine j) h
    have h4 := smallBaseChange_map_proj (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom) h
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans (h3.trans
      ((congrArg (· ≫ h.hom.left) h2).symm.trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h4).symm.trans (Category.assoc _ _ _).symm)))))

/-- The comparisons `stageToLim` are natural in the chart `T`. -/
theorem stageToLim_naturality (s : Over j) :
    (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine s.left)
        (rep_limitProjection B S hS D hc hD hAffine s.left)).map
        ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
          (rep_stageTransition B S hS D hD hAffine s.hom)).map h) ≫
        stageToLim B S hS D hc hD hAffine T' s =
      stageToLim B S hS D hc hD hAffine T s ≫
        (smallBaseChange B S hS (limitProjection B S hS D hc hD hAffine j)
          (rep_limitProjection B S hS D hc hD hAffine j)).map h := by
  apply sbc_hom_ext
  have h1 := stageToLim_proj B S hS D hc hD hAffine T' s
  have h2 := stageToLim_proj B S hS D hc hD hAffine T s
  have h3 := smallBaseChange_map_proj (limitProjection B S hS D hc hD hAffine j)
    (rep_limitProjection B S hS D hc hD hAffine j) h
  have h4 := smallBaseChange_map_proj (stageTransition B S hS D hD s.hom)
    (rep_stageTransition B S hS D hD hAffine s.hom) h
  have h5 := smallBaseChange_map_proj (limitProjection B S hS D hc hD hAffine s.left)
    (rep_limitProjection B S hS D hc hD hAffine s.left)
    ((smallBaseChange B S hS (stageTransition B S hS D hD s.hom)
      (rep_stageTransition B S hS D hD hAffine s.hom)).map h)
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h5).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h4).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h.hom.left) h2).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).symm.trans
      (Category.assoc _ _ _).symm)))))))))

end Naturality

/-! ### The system of base changes as a diagram of presheaves -/

/-- The base change to the limit represents the presheaf base change. -/
def limChartIso :
    yoneda.obj (limChart B S hS D hc hD hAffine T).obj.left ≅ (stageChartCone B S hS D
        T).pt :=
  ((rep_limitProjection B S hS D hc hD hAffine j).isPullback T.obj.hom).isoPullback

/-- Under `limChartIso` and `stageChartIso`, the projection of the presheaf limit cone to a stage
is the image of `limToStage`. -/
theorem limChartIso_comp (s : Over j) :
    (limChartIso B S hS D hc hD hAffine T).hom ≫ (stageChartCone B S hS D T).π.app s =
      yoneda.map (limToStage B S hS D hc hD hAffine T s) ≫
        (stageChartIso B S hS D hD hAffine T s).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, stageChartCone_π_fst, Category.assoc]
    refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
    exact (congrArg (· ≫ limit.π D s.left) (IsPullback.isoPullback_hom_fst _)).trans
      ((limToStage_chart B S hS D hc hD hAffine T s).symm.trans
        (congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_fst _).symm))
  · rw [Category.assoc, stageChartCone_π_snd, Category.assoc]
    exact (IsPullback.isoPullback_hom_snd _).trans ((congrArg yoneda.map
      (limToStage_proj B S hS D hc hD hAffine T s).symm).trans
      ((Functor.map_comp yoneda _ _).trans
        (congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_snd _).symm)))

/-! ### The limit of the base changes, in the site and in schemes -/

/-- The base change of `T` to the limit, as a cone over the base changes to the stages. -/
def limChartCone : Cone (laterStageChartDiagram B S hS D hD hAffine T) where
  pt := (limChart B S hS D hc hD hAffine T).obj.left
  π :=
    { app := fun s => limToStage B S hS D hc hD hAffine T s
      naturality := fun _ _ d =>
        (Category.id_comp _).trans (limToStage_stageToStage B S hS D hc hD hAffine T d).symm }

/-- **The base change to the limit is the limit, in the site, of the base changes to the
stages.** -/
def limChartConeIsLimit : IsLimit (limChartCone B S hS D hc hD hAffine T) := by
  have h : IsLimit ((Cones.postcompose (laterStageChartDiagramIso B S hS D hD hAffine T).inv).obj
      (stageChartCone B S hS D T)) :=
    (IsLimit.postcomposeInvEquiv _ _).symm (stageChartConeIsLimit B S hS D T)
  refine isLimitOfReflects yoneda (h.ofIsoLimit (Cones.ext
    (limChartIso B S hS D hc hD hAffine T).symm (fun s => ?_)))
  change (stageChartCone B S hS D T).π.app s ≫ (stageChartIso B S hS D hD hAffine T s).inv =
    (limChartIso B S hS D hc hD hAffine T).inv ≫ yoneda.map (limToStage B S hS D hc hD hAffine T s)
  rw [Iso.comp_inv_eq, Category.assoc, ← limChartIso_comp B S hS D hc hD hAffine T s,
    Iso.inv_hom_id_assoc]

include hc in
/-- **The base change to the limit is the limit of the base changes to the stages, as
schemes.** -/
theorem isLimit_toScheme_limChartCone :
    Nonempty (IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      (limChartCone B S hS D hc hD hAffine T))) := by
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := id hc
  have hJ : #(Over j) < B.cutoff :=
    mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHomSize j
  have hJH : ∀ a b : Over j, #(a ⟶ b) ≤ ν := fun a b =>
    (Cardinal.mk_le_of_injective (f := fun φ : a ⟶ b => φ.left)
      fun _ _ h => Over.OverMorphism.ext h).trans (hHomSize _ _)
  exact nonempty_isLimit_toScheme_mapCone_of_baseChangeSizeBounded (stageChartDiagram B S hS D T)
    (laterStageChartDiagram B S hS D hD hAffine T) (laterStageChartDiagramIso B S hS D hD hAffine T)
    hJ hν hJH (baseChangeSizeBounded_chartDiagram B S hS D hD hAffine T hB)
    (stageChartDiagram_affine B S hS D hAffine T) (limChartConeIsLimit B S hS D hc hD hAffine T)

/-! ### Descent of regular functions -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
  (hTqc : IsQuasiCompactSpace B S hS (yoneda.obj T.obj.left))
  (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T.obj.left))

include hD hAffine hZ hQc hQs hTqc hTqs in
/-- The base changes of a quasi-compact and quasi-separated chart to the later stages are
quasi-compact and quasi-separated schemes, with affine transition morphisms. -/
theorem laterStageChartDiagram_qcqs (s : Over j) :
    CompactSpace ((laterStageChartDiagram B S hS D hD hAffine T ⋙
        BigFppfOver.toScheme B S hS).obj s) ∧
      QuasiSeparatedSpace ((laterStageChartDiagram B S hS D hD hAffine T ⋙
        BigFppfOver.toScheme B S hS).obj s) :=
  ⟨compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_of_iso B S hS (stageChartIso B S hS D hD hAffine T s).symm
        (stageChartDiagram_qc B S hS D hD T hZ hQc hQs hTqc s)),
    quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda B S hS hZ _
      (isAbsolutelyQuasiSeparated_of_iso B S hS hZ (isAlgebraicSpace_yoneda B S hS _)
        (stageChartIso B S hS D hD hAffine T s)
        (stageChartDiagram_qs B S hS D hD hAffine T hZ hTqs s))⟩

/-- The hypotheses of the limit theorems for schemes, for the base changes of a chart. -/
private theorem laterStageChartDiagram_hypotheses (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hTqc : IsQuasiCompactSpace B S hS (yoneda.obj T.obj.left))
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T.obj.left)) :
    (∀ s, CompactSpace ((laterStageChartDiagram B S hS D hD hAffine T ⋙
      BigFppfOver.toScheme B S hS).obj s)) ∧
    (∀ s, QuasiSeparatedSpace ((laterStageChartDiagram B S hS D hD hAffine T ⋙
      BigFppfOver.toScheme B S hS).obj s)) ∧
    ∀ {a b : Over j} (f : a ⟶ b), _root_.AlgebraicGeometry.IsAffineHom
      ((laterStageChartDiagram B S hS D hD hAffine T ⋙ BigFppfOver.toScheme B S hS).map f) :=
  ⟨fun s => (laterStageChartDiagram_qcqs B S hS D hD hAffine T hZ hQc hQs hTqc hTqs s).1,
    fun s => (laterStageChartDiagram_qcqs B S hS D hD hAffine T hZ hQc hQs hTqc hTqs s).2,
    fun f => isAffineHom_toScheme_map_of_iso (stageChartDiagram B S hS D T) _
      (laterStageChartDiagramIso B S hS D hD hAffine T)
      (stageChartDiagram_affine B S hS D hAffine T) f⟩

include hc hD hAffine hZ hQc hQs hTqc hTqs in
/-- **Every regular function on the base change to the limit comes from a stage**, for a system
bounded by the cutoff. -/
theorem exists_gpb_limToStage_eq
    (y : Γ((BigFppfOver.toScheme B S hS).obj (limChart B S hS D hc hD hAffine
        T).obj.left, ⊤)) :
    ∃ (s : Over j) (x : Γ((BigFppfOver.toScheme B S hS).obj
        (laterStageChart B S hS D hD hAffine T s).obj.left, ⊤)),
      gpb (limToStage B S hS D hc hD hAffine T s) x = y := by
  obtain ⟨hlim⟩ := isLimit_toScheme_limChartCone B S hS D hc hD hAffine T
  obtain ⟨_, _, _⟩ := laterStageChartDiagram_hypotheses B S hS D T hD hAffine hZ hQc hQs hTqc hTqs
  obtain ⟨s, x, hx⟩ := exists_appTop_π_eq_of_isLimit _ _ hlim y
  exact ⟨s, x, hx.symm⟩

include hc hD hAffine hZ hQc hQs hTqc hTqs in
/-- **Two regular functions on a stage which agree on the base change to the limit agree on a
later stage**, for a system bounded by the cutoff. -/
theorem exists_gpb_stageToStage_eq {s : Over j}
    (x₁ x₂ : Γ((BigFppfOver.toScheme B S hS).obj (laterStageChart B S hS D hD hAffine T
        s).obj.left, ⊤))
    (h : gpb (limToStage B S hS D hc hD hAffine T s) x₁ =
      gpb (limToStage B S hS D hc hD hAffine T s) x₂) :
    ∃ (s' : Over j) (d : s' ⟶ s), gpb (stageToStage B S hS D hD hAffine T d) x₁ =
      gpb (stageToStage B S hS D hD hAffine T d) x₂ := by
  obtain ⟨hlim⟩ := isLimit_toScheme_limChartCone B S hS D hc hD hAffine T
  obtain ⟨_, _, _⟩ := laterStageChartDiagram_hypotheses B S hS D T hD hAffine hZ hQc hQs hTqc hTqs
  exact exists_app_map_eq_map_of_isLimit _ _ hlim (U := ⊤) isCompact_univ x₁ x₂ h

end Descent

end AlgebraicGeometry.Space.IsCutoffBoundedSystem

end
