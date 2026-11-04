module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings

/-!
# Descending the closed-immersion property along a limit of algebraic spaces

Work in the situation of Stacks 084W, formalized as
`AlgebraicGeometry.Space.MorphismDescentSituation`: a directed inverse system of algebraic spaces
`B = lim B_i` with affine transition morphisms, a morphism `f₀ : X₀ ⟶ Y₀` of quasi-compact
quasi-separated algebraic spaces over `B₀`, and its base changes `f_i : X_i ⟶ Y_i` and
`f : X ⟶ Y` to `B_i` and to `B`. If `f` is a closed immersion and `f₀` is locally of finite type,
then `f_i` is a closed immersion for some `i ≥ 0`
(`MorphismDescentSituation.exists_isClosedImmersion_mapAt_of_siteContainsBaseChangeLimits`).
This is under the standing convention of Section 70.2 (tag 07SD) that every ring considered has
its spectrum in the big fppf site, which for the system of bases is
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`.

The file also constructs an affine étale surjective chart `V₀ ⟶ Y₀` of the target at the
distinguished stage, the induced charts `V_i ⟶ Y_i` and `V ⟶ Y` at the later stages and at the
limit, and the fibre products `V_i ×_{Y_i} X_i` and `V ×_Y X`.

## Main definitions

Names are relative to the namespace `AlgebraicGeometry.Space.MorphismDescentSituation`.

* `TargetChart`: an affine étale surjective chart of the target `Y₀` at the distinguished stage.
* `TargetChart.stageChart` and `TargetChart.limitChart`: the induced charts `V_i ⟶ Y_i` and
  `V ⟶ Y`.
* `TargetChart.chartSourceDescentSituation`: the system `V_i ×_{Y_i} X_i`, as a situation of
  Stacks 084R.

## Main results

* `nonempty_targetChart_of_siteContainsBaseChangeLimits`: the target at the distinguished stage,
  being quasi-compact, admits such a chart.
* `TargetChart.isPullback_stageChart` and `TargetChart.isPullback_limitChart`: each induced chart
  is a base change of the chart at the distinguished stage, whence `TargetChart.stageChart_etale`
  and `TargetChart.stageChart_surjective`.
* `TargetChart.isAffine_pullback_limitChart`: `V ×_Y X` is represented by an object of the site
  with affine underlying scheme.
* `TargetChart.isAffineSpace_chartSourceDescentSituation_limitCone_pt`: the limit of that
  situation is an affine algebraic space.
* `TargetChart.isClosedImmersion_mapAt_of_isClosedImmersion_pullback_stageChart`: descent of the
  closed-immersion property through the chart.
* `relativelyRepresentable_mapAt_of_mono`: a monomorphic base change of `f₀` is representable by
  schemes.
* `exists_isPullback_mapAt_targetAtProj` and `exists_isPullback_mapLimit_targetLimitProj`: `f_j`
  and `f` are base changes of `f_i` along the projections `Y_j ⟶ Y_i` and `Y ⟶ Y_i` of the
  targets.
* `isFinite_mapAt_of_le`: finiteness of the base change passes from a stage to every later stage.
* `exists_isClosedImmersion_mapAt_of_siteContainsBaseChangeLimits`: if `f` is a closed
  immersion and `f₀` is locally of finite type, then some `f_i` is a closed immersion.
* `exists_isClosedImmersion_mapAt`: the same for a system small for the site.

## References

* [Stacks Project, Tag 0850](https://stacks.math.columbia.edu/tag/0850)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SM](https://stacks.math.columbia.edu/tag/07SM)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

namespace MorphismDescentSituation

/-- Finiteness of the base change of `f₀` passes from a stage to every later stage, the base change
at the later stage being a base change of the one at the earlier stage. -/
theorem isFinite_mapAt_of_le (D : MorphismDescentSituation B S hS hZ I) {i j : I}
    (hi : D.initial ≤ i) (hij : i ≤ j) (hf : IsFinite B S hS (D.mapAt i hi)) :
    IsFinite B S hS (D.mapAt j (hi.trans hij)) := by
  obtain ⟨α, β, hpb⟩ := D.exists_isPullback_mapAt_of_le hi hij
  have hfin := ((isFinite_iff_representable B S hS _ (D.sourceAt_isAlgebraicSpace i hi)
    (D.targetAt_isAlgebraicSpace i hi)).1 hf).2
  have hfin' := MorphismProperty.of_isPullback (P := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (BigFppfOver.toScheme B S hS))) hpb hfin
  exact (isFinite_iff_representable B S hS _
    (D.sourceAt_isAlgebraicSpace j (hi.trans hij))
    (D.targetAt_isAlgebraicSpace j (hi.trans hij))).2 ⟨hfin'.rep, hfin'⟩

/-! ### Comparing the stages and the limit as base changes of one another

The target `Y_j` of the base change of `f₀` to a stage is the fibre product of `B_j` with `Y₀`
over `B₀`, so the transition morphism `B_j ⟶ B_i` of the system of bases induces a projection
`Y_j ⟶ Y_i` for `i ≤ j`, and the limit projection `B ⟶ B_i` induces `Y ⟶ Y_i`. Against those
named projections `f_j` is a base change of `f_i`, and `f` is a base change of `f_i`. -/

/-- The transition morphism `B_j ⟶ B_i` of the system of bases, followed by the transition morphism
`B_i ⟶ B₀` to the distinguished stage, is the transition morphism `B_j ⟶ B₀`. -/
theorem base_map_comp_baseAtToInitial (D : MorphismDescentSituation B S hS hZ I) {i j : I}
    (hi : D.initial ≤ i) (hij : i ≤ j) :
    D.base.map (homOfLE hij).op ≫ D.baseAtToInitial i hi =
      D.baseAtToInitial j (hi.trans hij) :=
  (D.base.map_comp (homOfLE hij).op (homOfLE hi).op).symm.trans
    (congrArg D.base.map (Subsingleton.elim _ _))

/-- The limit projection `B ⟶ B_i`, followed by the transition morphism `B_i ⟶ B₀`, is the limit
projection `B ⟶ B₀`. -/
theorem limitπ_comp_baseAtToInitial (D : MorphismDescentSituation B S hS hZ I) (i : I)
    (hi : D.initial ≤ i) :
    limit.π D.base (op i) ≫ D.baseAtToInitial i hi = limit.π D.base (op D.initial) :=
  limit.w D.base (homOfLE hi).op

/-- The projection `Y_j ⟶ Y_i` between the targets of the base changes of `f₀` to two stages
`i ≤ j`, induced by the transition morphism `B_j ⟶ B_i`. -/
noncomputable def targetAtProj (D : MorphismDescentSituation B S hS hZ I) {i j : I}
    (hi : D.initial ≤ i) (hij : i ≤ j) :
    D.targetAt j (hi.trans hij) ⟶ D.targetAt i hi :=
  pullback.lift
    (pullback.fst (D.baseAtToInitial j (hi.trans hij)) D.targetToBase ≫
      D.base.map (homOfLE hij).op)
    (pullback.snd (D.baseAtToInitial j (hi.trans hij)) D.targetToBase)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ pullback.fst (D.baseAtToInitial j (hi.trans hij)) D.targetToBase ≫ m)
        (D.base_map_comp_baseAtToInitial hi hij)).trans pullback.condition))

/-- The projection `Y_j ⟶ Y_i` followed by the projection `Y_i ⟶ B_i` is the projection `Y_j ⟶ B_j`
followed by the transition morphism `B_j ⟶ B_i`. -/
@[simp] theorem targetAtProj_fst (D : MorphismDescentSituation B S hS hZ I) {i j : I}
    (hi : D.initial ≤ i) (hij : i ≤ j) :
    D.targetAtProj hi hij ≫ pullback.fst (D.baseAtToInitial i hi) D.targetToBase =
      pullback.fst (D.baseAtToInitial j (hi.trans hij)) D.targetToBase ≫
        D.base.map (homOfLE hij).op :=
  pullback.lift_fst _ _ _

/-- The projection `Y_j ⟶ Y_i` followed by the projection `Y_i ⟶ Y₀` is the projection `Y_j ⟶
Y₀`. -/
@[simp] theorem targetAtProj_snd (D : MorphismDescentSituation B S hS hZ I) {i j : I}
    (hi : D.initial ≤ i) (hij : i ≤ j) :
    D.targetAtProj hi hij ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (D.baseAtToInitial j (hi.trans hij)) D.targetToBase :=
  pullback.lift_snd _ _ _

/-- The projection `Y ⟶ Y_i` from the target of the base change of `f₀` to the limit to the target
of its base change to a stage, induced by the limit projection `B ⟶ B_i`. -/
noncomputable def targetLimitProj (D : MorphismDescentSituation B S hS hZ I) (i : I)
    (hi : D.initial ≤ i) : D.targetLimit ⟶ D.targetAt i hi :=
  pullback.lift
    (pullback.fst (limit.π D.base (op D.initial)) D.targetToBase ≫ limit.π D.base (op i))
    (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ pullback.fst (limit.π D.base (op D.initial)) D.targetToBase ≫ m)
        (D.limitπ_comp_baseAtToInitial i hi)).trans pullback.condition))

/-- The projection `Y ⟶ Y_i` followed by the projection `Y_i ⟶ B_i` is the projection `Y ⟶ B`
followed by the limit projection `B ⟶ B_i`. -/
@[simp] theorem targetLimitProj_fst (D : MorphismDescentSituation B S hS hZ I) (i : I)
    (hi : D.initial ≤ i) :
    D.targetLimitProj i hi ≫ pullback.fst (D.baseAtToInitial i hi) D.targetToBase =
      pullback.fst (limit.π D.base (op D.initial)) D.targetToBase ≫ limit.π D.base (op i) :=
  pullback.lift_fst _ _ _

/-- The projection `Y ⟶ Y_i` followed by the projection `Y_i ⟶ Y₀` is the projection `Y ⟶ Y₀`. -/
@[simp] theorem targetLimitProj_snd (D : MorphismDescentSituation B S hS hZ I) (i : I)
    (hi : D.initial ≤ i) :
    D.targetLimitProj i hi ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (limit.π D.base (op D.initial)) D.targetToBase :=
  pullback.lift_snd _ _ _

/-- The base change `f` of `f₀` to the limit is itself a base change of `f₀`, along the projections
of `X` and `Y` to `X₀` and `Y₀`. -/
theorem isPullback_mapLimit (D : MorphismDescentSituation B S hS hZ I) :
    IsPullback (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) D.mapLimit D.map₀
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) := by
  refine IsPullback.of_bot ?_ D.mapLimit_snd.symm D.targetLimit_isPullback.flip
  convert D.sourceLimit_isPullback.flip using 2
  · exact D.mapLimit_fst
  · exact D.map₀_over

/-- For `i ≤ j`, `f_j` is a base change of `f_i` along the projection `Y_j ⟶ Y_i`. -/
theorem exists_isPullback_mapAt_targetAtProj (D : MorphismDescentSituation B S hS hZ I) {i j : I}
    (hi : D.initial ≤ i) (hij : i ≤ j) :
    ∃ α : D.sourceAt j (hi.trans hij) ⟶ D.sourceAt i hi,
      IsPullback α (D.mapAt j (hi.trans hij)) (D.mapAt i hi) (D.targetAtProj hi hij) := by
  have hs : IsPullback (pullback.snd (D.baseAtToInitial j (hi.trans hij)) D.sourceToBase)
      (D.mapAt j (hi.trans hij)) D.map₀ (D.targetAtProj hi hij ≫
        pullback.snd (D.baseAtToInitial i hi) D.targetToBase) := by
    rw [D.targetAtProj_snd hi hij]
    exact D.isPullback_mapAt j (hi.trans hij)
  exact ⟨_, IsPullback.of_right' hs (D.isPullback_mapAt i hi)⟩

/-- `f` is a base change of `f_i` along the projection `Y ⟶ Y_i`. -/
theorem exists_isPullback_mapLimit_targetLimitProj (D : MorphismDescentSituation B S hS hZ I)
    (i : I) (hi : D.initial ≤ i) :
    ∃ α : D.sourceLimit ⟶ D.sourceAt i hi,
      IsPullback α D.mapLimit (D.mapAt i hi) (D.targetLimitProj i hi) := by
  have hs : IsPullback (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase)
      D.mapLimit D.map₀ (D.targetLimitProj i hi ≫
        pullback.snd (D.baseAtToInitial i hi) D.targetToBase) := by
    rw [D.targetLimitProj_snd i hi]
    exact D.isPullback_mapLimit
  exact ⟨_, IsPullback.of_right' hs (D.isPullback_mapAt i hi)⟩

/-! ### Finiteness properties of the stages -/

/-- Local finiteness of type passes from `f₀` to its base change at every stage, the base change
being a base change of `f₀`. -/
theorem isLocallyOfFiniteType_mapAt (D : MorphismDescentSituation B S hS hZ I)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) (i : I) (hi : D.initial ≤ i) :
    IsLocallyOfFiniteType B S hS (D.mapAt i hi) :=
  IsLocallyOfFiniteType.of_isPullback B S hS (D.isPullback_mapAt i hi).flip
    D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace hf₀

/-- Local finiteness of type passes from `f₀` to its base change to the limit, that base change
being a base change of `f₀`. -/
theorem isLocallyOfFiniteType_mapLimit (D : MorphismDescentSituation B S hS hZ I)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    IsLocallyOfFiniteType B S hS D.mapLimit :=
  IsLocallyOfFiniteType.of_isPullback B S hS D.isPullback_mapLimit.flip
    D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace hf₀

/-- The source `X_i` of the base change of `f₀` to a stage is quasi-compact, being the fibre
product of the quasi-compact `B_i` and `X₀` over the quasi-separated `B₀`. -/
theorem isQuasiCompactSpace_sourceAt (D : MorphismDescentSituation B S hS hZ I) (i : I)
    (hi : D.initial ≤ i) : IsQuasiCompactSpace B S hS (D.sourceAt i hi) :=
  isQuasiCompactSpace_pullback B S hS hZ _ D.sourceToBase
    (D.base_isAlgebraicSpace i) (D.base_isAlgebraicSpace D.initial)
    (D.isQuasiCompactSpace_base ⟨i, hi⟩) D.source₀_quasiCompact D.base₀_quasiSeparated

/-- The target `Y_i` of the base change of `f₀` to a stage is quasi-separated, being the fibre
product of the quasi-separated `B_i` and `Y₀`. -/
theorem isAbsolutelyQuasiSeparated_targetAt (D : MorphismDescentSituation B S hS hZ I) (i : I)
    (hi : D.initial ≤ i) : IsAbsolutelyQuasiSeparated B S hS hZ (D.targetAt i hi) :=
  isAbsolutelyQuasiSeparated_pullback B S hS hZ _ D.targetToBase
    (D.base_isAlgebraicSpace i) D.target₀_isAlgebraicSpace
    (D.base_isAlgebraicSpace D.initial)
    (D.isAbsolutelyQuasiSeparated_base ⟨i, hi⟩) D.target₀_quasiSeparated

/-- If `f₀` is locally of finite type, a monomorphic base change of `f₀` to a stage is
representable by schemes. -/
theorem relativelyRepresentable_mapAt_of_mono (D : MorphismDescentSituation B S hS hZ I)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) {i : I} (hi : D.initial ≤ i)
    (hmono : Mono (D.mapAt i hi)) :
    yoneda.relativelyRepresentable (D.mapAt i hi) := by
  obtain ⟨hsep, hlqf⟩ := isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono
    B S hS (D.mapAt i hi) ⟨D.isLocallyOfFiniteType_mapAt hf₀ i hi, hmono⟩
  exact relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS (D.mapAt i hi)
    (D.sourceAt_isAlgebraicSpace i hi) (D.targetAt_isAlgebraicSpace i hi) hlqf hsep

/-- An affine étale surjective chart of the target `Y₀` at the distinguished stage of a morphism
descent system. -/
structure TargetChart (D : MorphismDescentSituation B S hS hZ I) where
  /-- The system of bases satisfies the chapter's convention (tag 07SD), so that the limits of
  the affine charts of its stages are formed inside the site. -/
  siteContainsBaseChangeLimits : SiteContainsBaseChangeLimits B S hS D.base
  /-- The affine object of the site charting the target. -/
  obj : BigAffineFppf B S hS
  /-- The chart `V₀ ⟶ Y₀`. -/
  chart : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj obj) ⟶ D.target₀
  /-- The chart is surjective. -/
  chart_surjective : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf chart
  /-- The chart is étale. -/
  chart_etale : IsEtale B S hS chart

/-- The target at the distinguished stage of a morphism descent system is quasi-compact, so under
the chapter's convention it admits an affine étale surjective chart. -/
theorem nonempty_targetChart_of_siteContainsBaseChangeLimits
    (D : MorphismDescentSituation B S hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base) : Nonempty (TargetChart D) := by
  obtain ⟨U, chart, hU, hsurj, hetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.target₀
      D.target₀_isAlgebraicSpace).mp D.target₀_quasiCompact
  exact ⟨{ siteContainsBaseChangeLimits := hconv
           obj := ⟨U, hU⟩
           chart := chart
           chart_surjective := hsurj
           chart_etale := hetale }⟩

/-- The target at the distinguished stage of a morphism descent system is quasi-compact, so when
the system is small for the site it admits an affine étale surjective chart. -/
theorem nonempty_targetChart (D : MorphismDescentSituation B S hS hZ I)
    (hb : IsSiteSmall B S hS D.base) : Nonempty (TargetChart D) :=
  have := D.isCofiltered_op
  D.nonempty_targetChart_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb)

/-- The projection `Y ⟶ Y₀` from the target of the base change to the limit. -/
noncomputable def targetLimitToInitial (D : MorphismDescentSituation B S hS hZ I) :
    D.targetLimit ⟶ D.target₀ :=
  pullback.snd (limit.π D.base (op D.initial)) D.targetToBase

/-- The base change `f` of `f₀` to the limit, followed by the projection `Y ⟶ Y₀`, is the structure
morphism `X ⟶ Y₀`. -/
theorem mapLimit_comp_targetLimitToInitial (D : MorphismDescentSituation B S hS hZ I) :
    D.mapLimit ≫ D.targetLimitToInitial = sourceLimitToTargetInitial D := D.mapLimit_snd

namespace TargetChart

variable {D : MorphismDescentSituation B S hS hZ I} (T : TargetChart D)

/-- The chart `V₀ ⟶ B₀` of the distinguished stage obtained from the chart of the target. -/
noncomputable def baseChart :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T.obj) ⟶ D.base.obj (op D.initial) :=
  T.chart ≫ D.targetToBase

/-- The system `(V_i)` of affine charts of the stages, obtained by base changing the chart of the
distinguished stage along the transition morphisms. -/
noncomputable def system :
    AffineChartSystem B S hS (op D.initial) D.base T.obj T.baseChart :=
  affineChartSystem B S hS (op D.initial) D.base T.obj T.baseChart
    (fun {_ _} g ↦ D.transition_affine g)

/-- The limit `V` of the system of affine charts of the stages. -/
noncomputable def bridge : AffineChartSystem.LimitBridge T.system := by
  haveI : Nonempty I := ⟨D.initial⟩
  haveI : IsDirectedOrder I := inferInstance
  haveI : IsFiltered I := inferInstance
  haveI : IsCofiltered Iᵒᵖ := inferInstance
  exact AffineChartSystem.limitBridgeOfLimitInSite T.system
    (T.system.limitInSite_of_siteContainsBaseChangeLimits T.siteContainsBaseChangeLimits)

/-- The square exhibiting the chart `V_j` of a stage as the fibre product of that stage with `V₀`
over the distinguished stage, written against `baseAtToInitial`. -/
theorem isPullback_system (j : Over (op D.initial)) :
    IsPullback (T.system.stageMap j) (T.system.baseMap j)
      (D.baseAtToInitial j.left.unop (leOfHom j.hom.unop)) (T.chart ≫ D.targetToBase) := by
  have h := T.system.isPullback j
  rw [show D.base.map j.hom = D.baseAtToInitial j.left.unop (leOfHom j.hom.unop) from
    congrArg D.base.map (Subsingleton.elim _ _)] at h
  exact h

/-- The chart `V_j ⟶ Y_j` of the target at a stage, induced by the universal property of
`Y_j = B_j ×_{B₀} Y₀`. -/
noncomputable def stageChart (j : Over (op D.initial)) :
    (T.system.siteDiagram ⋙ yoneda).obj j ⟶
      D.targetAt j.left.unop (leOfHom j.hom.unop) :=
  (D.targetAt_isPullback j.left.unop (leOfHom j.hom.unop)).lift (T.system.stageMap j)
    (T.system.baseMap j ≫ T.chart)
    (by rw [(T.isPullback_system j).w, Category.assoc])

/-- The chart of the target at a stage is a base change of the chart at the distinguished stage. -/
theorem isPullback_stageChart (j : Over (op D.initial)) :
    IsPullback (T.stageChart j) (T.system.baseMap j)
      (pullback.snd (D.baseAtToInitial j.left.unop (leOfHom j.hom.unop)) D.targetToBase)
      T.chart :=
  IsPullback.of_right' (T.isPullback_system j)
    (D.targetAt_isPullback j.left.unop (leOfHom j.hom.unop))

/-- The chart `V ⟶ Y` of the target at the limit, induced by the universal property of
`Y = B ×_{B₀} Y₀`. -/
noncomputable def limitChart : yoneda.obj T.bridge.cone.pt ⟶ D.targetLimit :=
  D.targetLimit_isPullback.lift T.bridge.toLimit (T.bridge.toBase ≫ T.chart)
    (by rw [T.bridge.isPullback.w, Category.assoc]; rfl)

/-! ### The charts of the stages and of the limit, against the projections of the targets -/

/-- The chart of the target at a stage, followed by the projection of that stage to its base. -/
theorem stageChart_comp_fst (j : Over (op D.initial)) :
    T.stageChart j ≫
        pullback.fst (D.baseAtToInitial j.left.unop (leOfHom j.hom.unop)) D.targetToBase =
      T.system.stageMap j :=
  (D.targetAt_isPullback j.left.unop (leOfHom j.hom.unop)).lift_fst _ _ _

/-- The chart of the target at a stage, followed by the projection of that stage to `Y₀`. -/
theorem stageChart_comp_snd (j : Over (op D.initial)) :
    T.stageChart j ≫
        pullback.snd (D.baseAtToInitial j.left.unop (leOfHom j.hom.unop)) D.targetToBase =
      T.system.baseMap j ≫ T.chart :=
  (D.targetAt_isPullback j.left.unop (leOfHom j.hom.unop)).lift_snd _ _ _

/-- The chart of the target at the limit, followed by the projection of the limit to its base. -/
theorem limitChart_comp_fst :
    T.limitChart ≫ pullback.fst (limit.π D.base (op D.initial)) D.targetToBase =
      T.bridge.toLimit :=
  D.targetLimit_isPullback.lift_fst _ _ _

/-- The chart of the target at the limit, followed by the projection of the limit to `Y₀`. -/
theorem limitChart_comp_snd :
    T.limitChart ≫ pullback.snd (limit.π D.base (op D.initial)) D.targetToBase =
      T.bridge.toBase ≫ T.chart :=
  D.targetLimit_isPullback.lift_snd _ _ _

/-- Naturality of the isomorphism between the system of affine charts and the system of base
changes of the chart at the distinguished stage. -/
private theorem yoneda_map_siteDiagram_map_comp_iso_hom_app {j k : Over (op D.initial)}
    (g : j ⟶ k) :
    yoneda.map (T.system.siteDiagram.map g) ≫ T.system.iso.hom.app k =
      T.system.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS (op D.initial) D.base
        T.obj T.baseChart).map g := T.system.iso.hom.naturality g

/-- The transition morphisms of the system of affine charts are compatible with the projections to
the chart at the distinguished stage. -/
theorem yoneda_map_siteDiagram_map_comp_baseMap {j k : Over (op D.initial)} (g : j ⟶ k) :
    yoneda.map (T.system.siteDiagram.map g) ≫ T.system.baseMap k = T.system.baseMap j := by
  simp only [AffineChartSystem.baseMap]
  rw [← Category.assoc, T.yoneda_map_siteDiagram_map_comp_iso_hom_app g, Category.assoc,
    stageBaseChangeDiagram_map_comp_snd]

/-- The transition morphisms of the system of affine charts are compatible with the projections to
the stages of the system of bases. -/
theorem yoneda_map_siteDiagram_map_comp_stageMap {j k : Over (op D.initial)} (g : j ⟶ k) :
    yoneda.map (T.system.siteDiagram.map g) ≫ T.system.stageMap k =
      T.system.stageMap j ≫ D.base.map g.left := by
  simp only [AffineChartSystem.stageMap]
  rw [← Category.assoc, T.yoneda_map_siteDiagram_map_comp_iso_hom_app g, Category.assoc,
    stageBaseChangeDiagram_map_comp_fst, ← Category.assoc]

/-- The transition morphism of the system of affine charts, followed by the chart of the earlier
stage, is the chart of the later stage followed by the projection of the targets. -/
theorem yoneda_map_siteDiagram_map_comp_stageChart {j k : Over (op D.initial)} (g : j ⟶ k) :
    yoneda.map (T.system.siteDiagram.map g) ≫ T.stageChart k =
      T.stageChart j ≫ D.targetAtProj (leOfHom k.hom.unop) (leOfHom g.left.unop) := by
  apply pullback.hom_ext
  · calc yoneda.map (T.system.siteDiagram.map g) ≫ T.stageChart k ≫
          pullback.fst (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase
        = T.system.stageMap j ≫ D.base.map g.left := by
          rw [T.stageChart_comp_fst k, T.yoneda_map_siteDiagram_map_comp_stageMap g]
      _ = T.system.stageMap j ≫
            D.base.map (homOfLE (leOfHom g.left.unop)).op :=
          congrArg (fun m ↦ T.system.stageMap j ≫ m)
            (congrArg D.base.map (Subsingleton.elim _ _))
      _ = T.stageChart j ≫ D.targetAtProj (leOfHom k.hom.unop) (leOfHom g.left.unop) ≫
            pullback.fst (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase :=
          (congrArg (fun m ↦ m ≫ D.base.map (homOfLE (leOfHom g.left.unop)).op)
              (T.stageChart_comp_fst j)).symm.trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun m ↦ T.stageChart j ≫ m) (D.targetAtProj_fst _ _).symm))
  · calc yoneda.map (T.system.siteDiagram.map g) ≫ T.stageChart k ≫
          pullback.snd (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase
        = T.system.baseMap j ≫ T.chart := by
          rw [T.stageChart_comp_snd k, ← Category.assoc,
            T.yoneda_map_siteDiagram_map_comp_baseMap g]
      _ = T.stageChart j ≫ D.targetAtProj (leOfHom k.hom.unop) (leOfHom g.left.unop) ≫
            pullback.snd (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase := by
          rw [D.targetAtProj_snd, T.stageChart_comp_snd j]

/-- The projection of the limit of the system of affine charts to the chart of a stage, followed by
the chart of that stage, is the chart of the limit followed by the projection of the targets. -/
theorem yoneda_map_bridge_π_comp_stageChart (k : Over (op D.initial)) :
    yoneda.map (T.bridge.cone.π.app k) ≫ T.stageChart k =
      T.limitChart ≫ D.targetLimitProj k.left.unop (leOfHom k.hom.unop) := by
  apply pullback.hom_ext
  · calc yoneda.map (T.bridge.cone.π.app k) ≫ T.stageChart k ≫
          pullback.fst (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase
        = yoneda.map (T.bridge.cone.π.app k) ≫ T.system.stageMap k := by
          rw [T.stageChart_comp_fst k]
      _ = T.bridge.toLimit ≫ limit.π D.base k.left :=
          (T.bridge.toLimit_comp_limitπ k).symm
      _ = T.limitChart ≫ D.targetLimitProj k.left.unop (leOfHom k.hom.unop) ≫
            pullback.fst (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase :=
          (congrArg (fun m ↦ m ≫ limit.π D.base (op k.left.unop))
              T.limitChart_comp_fst).symm.trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun m ↦ T.limitChart ≫ m) (D.targetLimitProj_fst _ _).symm))
  · calc yoneda.map (T.bridge.cone.π.app k) ≫ T.stageChart k ≫
          pullback.snd (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase
        = T.bridge.toBase ≫ T.chart := by
          rw [T.stageChart_comp_snd k, ← Category.assoc, T.bridge.baseMap_comp k]
      _ = T.limitChart ≫ D.targetLimitProj k.left.unop (leOfHom k.hom.unop) ≫
            pullback.snd (D.baseAtToInitial k.left.unop (leOfHom k.hom.unop)) D.targetToBase := by
          rw [D.targetLimitProj_snd, T.limitChart_comp_snd]

/-- The chart of the target at the limit is a base change of the chart at the distinguished
stage. -/
theorem isPullback_limitChart :
    IsPullback T.limitChart T.bridge.toBase
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase) T.chart :=
  IsPullback.of_right' T.bridge.isPullback D.targetLimit_isPullback

/-- The underlying scheme of the chart of the target at the limit is affine. -/
theorem isAffine_bridge_pt :
    IsAffine ((BigFppfOver.toScheme B S hS).obj T.bridge.cone.pt) :=
  T.bridge.isAffine_pt

/-! ### The chart of the target at a stage is again étale and surjective -/

/-- The chart of the target at a stage is surjective, being a base change of the chart at the
distinguished stage. -/
theorem stageChart_surjective (j : Over (op D.initial)) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (T.stageChart j) :=
  MorphismProperty.of_isPullback (T.isPullback_stageChart j).flip T.chart_surjective

/-- The chart of the target at a stage is étale, being a base change of the chart at the
distinguished stage. -/
theorem stageChart_etale (j : Over (op D.initial)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (T.stageChart j) :=
  MorphismProperty.of_isPullback (T.isPullback_stageChart j).flip
    ((isEtale_iff_presheaf_of_yoneda B S hS T.chart).mp T.chart_etale)

/-! ### The fibre product of the morphism with the chart, at the limit -/

/-- The base change of `f : X ⟶ Y` along the chart of the target at the limit is a closed immersion
of schemes. -/
theorem isClosedImmersion_scheme_snd_limitChart
    (hf : IsClosedImmersion B S hS D.mapLimit) :
    AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd T.limitChart)) :=
  hf.property T.limitChart (hf.rep.fst T.limitChart) _ (hf.rep.isPullback T.limitChart)

/-- The fibre product `V ×_Y X` of the closed immersion `f : X ⟶ Y` with the chart `V ⟶ Y` of the
target at the limit is represented by an object of the site whose underlying scheme is affine. -/
theorem isAffine_pullback_limitChart (hf : IsClosedImmersion B S hS D.mapLimit) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.rep.pullback T.limitChart)) := by
  have := T.isClosedImmersion_scheme_snd_limitChart hf
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T.bridge.cone.pt) := T.isAffine_bridge_pt
  exact AlgebraicGeometry.isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map (hf.rep.snd T.limitChart))

/-! ### The system `V₀ ×_{Y₀} X_i`, as a descent situation -/

/-- The system `V₀ ×_{Y₀} X_i`, as a situation of Stacks 084R: its stage at `i` is
`V_i ×_{Y_i} X_i` and the vertex of its limit cone is `V ×_Y X`; it is the base change of the
descent situation of the sources along the affine point `V₀ ⟶ Y₀` of the fixed target. -/
noncomputable def chartSourceDescentSituation : DescentSituation B S hS hZ D.Stages :=
  (stagesSourceDescentSituation D).baseChangeOver B S hS hZ D.target₀_isAlgebraicSpace
    D.target₀_quasiSeparated (sourceToTargetInitial D) (sourceLimitToTargetInitial D)
    (sourceCone_π_comp D) ((BigAffineFppf.inclusion B S hS).obj T.obj) T.obj.property T.chart

/-- The vertex of the limit cone of the system `V₀ ×_{Y₀} X_i` is `V ×_Y X`, written as the fibre
product of the structure morphism `X ⟶ Y₀` with the chart `V₀ ⟶ Y₀`. -/
theorem chartSourceDescentSituation_limitCone_pt :
    (T.chartSourceDescentSituation).limitCone.pt =
      pullback (sourceLimitToTargetInitial D) T.chart := rfl

/-- The stage at `i` of the system `V₀ ×_{Y₀} X_i`, written as the fibre product of the structure
morphism `X_i ⟶ Y₀` with the chart `V₀ ⟶ Y₀`. -/
theorem chartSourceDescentSituation_system_obj (j : (D.Stages)ᵒᵖ) :
    (T.chartSourceDescentSituation).system.obj j =
      pullback ((sourceToTargetInitial D).app j) T.chart := rfl

/-- The chart of the target at the limit, against the projection `Y ⟶ Y₀`. -/
theorem isPullback_limitChart' :
    IsPullback T.limitChart T.bridge.toBase D.targetLimitToInitial T.chart :=
  T.isPullback_limitChart

/-- `V ×_Y X` is the fibre product of `f : X ⟶ Y` with the chart of the target at the limit. -/
theorem exists_isPullback_limitCone_pt :
    ∃ β : pullback (sourceLimitToTargetInitial D) T.chart ⟶ yoneda.obj T.bridge.cone.pt,
      IsPullback (pullback.fst (sourceLimitToTargetInitial D) T.chart) β
        D.mapLimit T.limitChart := by
  have s : IsPullback (pullback.fst (sourceLimitToTargetInitial D) T.chart)
      (pullback.snd (sourceLimitToTargetInitial D) T.chart)
      (D.mapLimit ≫ D.targetLimitToInitial) T.chart := by
    rw [D.mapLimit_comp_targetLimitToInitial]
    exact IsPullback.of_hasPullback _ _
  exact ⟨_, IsPullback.of_bot' s T.isPullback_limitChart'⟩

/-- If `f` is a closed immersion, the vertex of the limit cone of the system `V₀ ×_{Y₀} X_i` is an
affine algebraic space. -/
theorem isAffineSpace_chartSourceDescentSituation_limitCone_pt
    (hf : IsClosedImmersion B S hS D.mapLimit) :
    IsAffineSpace B S hS (T.chartSourceDescentSituation).limitCone.pt := by
  obtain ⟨β, hβ⟩ := T.exists_isPullback_limitCone_pt
  exact ⟨hf.rep.pullback T.limitChart, T.isAffine_pullback_limitChart hf,
    ⟨hβ.isoIsPullback _ _ (hf.rep.isPullback T.limitChart)⟩⟩

/-! ### Descending through the chart -/

/-- If the base change of `f_i` along the chart of the target at a stage is a closed immersion,
then `f_i` is a closed immersion. -/
theorem isClosedImmersion_mapAt_of_isClosedImmersion_pullback_stageChart
    (j : Over (op D.initial))
    (hV : IsClosedImmersion B S hS
      (pullback.snd (D.mapAt j.left.unop (leOfHom j.hom.unop)) (T.stageChart j))) :
    IsClosedImmersion B S hS (D.mapAt j.left.unop (leOfHom j.hom.unop)) :=
  (isAlgebraicSpace_and_isClosedImmersion_of_surjectiveEtaleChart
    (D.sourceAt_isAlgebraicSpace j.left.unop (leOfHom j.hom.unop)).isSheaf
    (D.targetAt_isAlgebraicSpace j.left.unop (leOfHom j.hom.unop))
    (T.stageChart_surjective j) (T.stageChart_etale j) hV).2

/-! ### Descending the closed-immersion property through the chart -/

include T in
/-- If the base change of `f₀` to the stage indexed by `k` is a monomorphism and the base change of
`f₀` to the limit is a closed immersion, then the base change of `f₀` to some stage is a closed
immersion. -/
theorem exists_isClosedImmersion_mapAt_of_mono
    (hf : IsClosedImmersion B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) (k : Over (op D.initial))
    (hmono : Mono (D.mapAt k.left.unop (leOfHom k.hom.unop))) :
    ∃ (i : I) (hi : D.initial ≤ i), IsClosedImmersion B S hS (D.mapAt i hi) := by
  classical
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hrep := D.relativelyRepresentable_mapAt_of_mono hf₀ (leOfHom k.hom.unop) hmono
  have hsq : IsPullback (hrep.fst (T.stageChart k)) (yoneda.map (hrep.snd (T.stageChart k)))
      (D.mapAt k.left.unop (leOfHom k.hom.unop)) (T.stageChart k) :=
    hrep.isPullback (T.stageChart k)
  have hetaleW : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst (T.stageChart k)) :=
    MorphismProperty.of_isPullback hsq.flip (T.stageChart_etale k)
  have hlftW : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :=
    D.isLocallyOfFiniteType_mapAt hf₀ k.left.unop (leOfHom k.hom.unop) _ _
      (hrep.fst (T.stageChart k)) (T.stageChart k) _ hetaleW (T.stageChart_etale k) hsq.w.symm
  have hqcW : IsQuasiCompactSpace B S hS (yoneda.obj (hrep.pullback (T.stageChart k))) :=
    isQuasiCompactSpace_of_iso B S hS hsq.isoPullback.symm
      (isQuasiCompactSpace_pullback B S hS hZ _ (T.stageChart k)
        (D.sourceAt_isAlgebraicSpace _ _) (D.targetAt_isAlgebraicSpace _ _)
        (D.isQuasiCompactSpace_sourceAt _ _)
        (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (T.system.isAffine_obj k))
        (D.isAbsolutelyQuasiSeparated_targetAt _ _))
  have hcW : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (T.stageChart k))) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hqcW
  have hVkaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (T.system.siteDiagram.obj k)) :=
    T.system.isAffine_obj k
  have hVkaff' : IsAffine (T.system.schemeDiagram.obj k) := T.system.isAffine_obj k
  have : Mono (yoneda.map (hrep.snd (T.stageChart k))) := hsq.mono_snd_of_mono hmono
  have : Mono (hrep.snd (T.stageChart k)) := yoneda.mono_of_mono_map inferInstance
  have : Mono ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :=
    Functor.map_mono (BigFppfOver.toScheme B S hS) _
  have hqsW : QuasiSeparatedSpace
      ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (T.stageChart k))) :=
    quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
  have hsnd : ∀ {W : BigFppfOver B S hS} (h : W ⟶ T.system.siteDiagram.obj k),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (hrep.snd (T.stageChart k)) h)) ↔
      _root_.AlgebraicGeometry.IsClosedImmersion
        (pullback.snd ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
          ((BigFppfOver.toScheme B S hS).map h)) := fun h ↦
    prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      ((IsPullback.of_hasPullback (hrep.snd (T.stageChart k)) h).map
        (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)
  have hlimCI : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
        ((BigFppfOver.toScheme B S hS).map (T.bridge.cone.π.app k))) := by
    have houter := ((IsPullback.of_hasPullback (hrep.snd (T.stageChart k))
      (T.bridge.cone.π.app k)).map yoneda).paste_horiz hsq
    rw [T.yoneda_map_bridge_π_comp_stageChart k] at houter
    obtain ⟨αL, hmapL⟩ :=
      D.exists_isPullback_mapLimit_targetLimitProj k.left.unop (leOfHom k.hom.unop)
    have h1 : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (hrep.snd (T.stageChart k)) (T.bridge.cone.π.app k))) :=
      hf.property T.limitChart _ _ (IsPullback.of_right' houter hmapL)
    exact (hsnd _).mp h1
  have : Nonempty I := ⟨D.initial⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsCofiltered (Over (op D.initial)) := inferInstance
  have hEhom : ∀ {a b : Over (op D.initial)} (g : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom (T.system.schemeDiagram.map g) :=
    fun g ↦ T.system.isAffineHom_map g
  have hck : CompactSpace (T.system.schemeDiagram.obj k) :=
    Scheme.compactSpace_of_isAffine _
  have hqsk : QuasiSeparatedSpace (T.system.schemeDiagram.obj k) := inferInstance
  have : CompactSpace
      (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
        Over (T.system.schemeDiagram.obj k)).left := hcW
  have : QuasiSeparatedSpace
      (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
        Over (T.system.schemeDiagram.obj k)).left := hqsW
  have : CompactSpace (Over.mk (𝟙 (T.system.schemeDiagram.obj k))).left := hck
  have : QuasiSeparatedSpace (Over.mk (𝟙 (T.system.schemeDiagram.obj k))).left := hqsk
  have : LocallyOfFiniteType (Over.homMk
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) (Category.comp_id _) :
      (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
        Over (T.system.schemeDiagram.obj k)) ⟶ Over.mk (𝟙 _)).left := hlftW
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((Over.pullback
      (((BigFppfOver.toScheme B S hS).mapCone T.bridge.cone).π.app k)).map
      (Over.homMk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
        (Category.comp_id _) :
        (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))) :
          Over (T.system.schemeDiagram.obj k)) ⟶ Over.mk (𝟙 _))).left :=
    (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _ _).mpr hlimCI
  obtain ⟨l, g, hres⟩ := _root_.AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit
    T.system.schemeDiagram _ T.bridge.schemeIsLimit k
    (Over.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k))))
    (Over.mk (𝟙 (T.system.schemeDiagram.obj k)))
    (Over.homMk ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
      (Category.comp_id _))
  have hstage : _root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (T.stageChart k)))
      (T.system.schemeDiagram.map g)) :=
    (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _ _).mp hres
  have hsite : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (hrep.snd (T.stageChart k)) (T.system.siteDiagram.map g))) :=
    (hsnd _).mpr hstage
  have hpre : IsClosedImmersion B S hS (yoneda.map
      (pullback.snd (hrep.snd (T.stageChart k)) (T.system.siteDiagram.map g))) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _).2 hsite
  have houter2 := ((IsPullback.of_hasPullback (hrep.snd (T.stageChart k))
    (T.system.siteDiagram.map g)).map yoneda).paste_horiz hsq
  rw [T.yoneda_map_siteDiagram_map_comp_stageChart g] at houter2
  obtain ⟨αS, hmapS⟩ :=
    D.exists_isPullback_mapAt_targetAtProj (leOfHom k.hom.unop) (leOfHom g.left.unop)
  refine ⟨l.left.unop, leOfHom l.hom.unop,
    T.isClosedImmersion_mapAt_of_isClosedImmersion_pullback_stageChart l ?_⟩
  exact (prop_snd_iff_of_isPullback _ (IsPullback.of_right' houter2 hmapS)
    (IsPullback.of_hasPullback _ _)).mp hpre

end TargetChart

/-- In the situation of Stacks 084W, if the base change `f` of `f₀` to the limit `B` is a closed
immersion and `f₀` is locally of finite type, then the base change `f_i` of `f₀` to some stage
`B_i` is a closed immersion. -/
@[sga "3 VIB 10.1" "partial"]
theorem exists_isClosedImmersion_mapAt_of_siteContainsBaseChangeLimits
    (D : MorphismDescentSituation B S hS hZ I)
    (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (hf : IsClosedImmersion B S hS D.mapLimit) (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsClosedImmersion B S hS (D.mapAt i hi) := by
  obtain ⟨T⟩ := D.nonempty_targetChart_of_siteContainsBaseChangeLimits hconv
  obtain ⟨i, hi, hmono⟩ := D.exists_mono_mapAt_of_siteContainsBaseChangeLimits hconv
    (mono_of_isClosedImmersion B S hS _ hf) hf₀
  exact T.exists_isClosedImmersion_mapAt_of_mono hf hf₀ (Over.mk (homOfLE hi).op) hmono

/-- In the situation of Stacks 084W with a system of bases small for the site, if the base change
`f` of `f₀` to the limit is a closed immersion and `f₀` is locally of finite type, then the base
change `f_i` of `f₀` to some stage is a closed immersion. -/
theorem exists_isClosedImmersion_mapAt (D : MorphismDescentSituation B S hS hZ I)
    (hb : IsSiteSmall B S hS D.base) (hf : IsClosedImmersion B S hS D.mapLimit)
    (hf₀ : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsClosedImmersion B S hS (D.mapAt i hi) :=
  have := D.isCofiltered_op
  D.exists_isClosedImmersion_mapAt_of_siteContainsBaseChangeLimits
    (IsSiteSmall.siteContainsBaseChangeLimits B S hS D.base hb) hf hf₀

end MorphismDescentSituation

end AlgebraicGeometry.Space

end
