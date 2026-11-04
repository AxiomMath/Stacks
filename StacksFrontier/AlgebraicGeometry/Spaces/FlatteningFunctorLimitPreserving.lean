module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFunctorChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFunctorSheafAndLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings

/-!
# Limit preservation of the flattening functor of an algebraic space

In Situation 0CWX — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site together with a quasi-coherent `𝒪_X`-module `F` — part (2) of Stacks 0CWZ asserts that the
functor `F_flat` of equation 0CWY is limit preserving in the sense of Stacks 049J, provided `f`
is quasi-compact and locally of finite presentation and `F` is of finite presentation.  **That
assertion is proved here**, at the source's own hypotheses and with nothing carried.

## Main results

* `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving`: **Stacks 0CWZ,
  part (2)**.
* `AlgebraicGeometry.Space.FlatnessSituation.exists_affine_testChart`: over an affine test
  scheme, `X_T` has an étale scheme chart with affine chart object whose structure morphism to
  the test scheme is locally of finite presentation.
* `AlgebraicGeometry.Space.FlatnessSituation.isQuasiCompactSpace_baseChangeSpace` and
  `AlgebraicGeometry.Space.FlatnessSituation.isLocallyOfFinitePresentation_baseChangeInclusion`:
  the two properties of `f` inherited by the base change `X_T ⟶ T`.
* `AlgebraicGeometry.Space.FlatnessSituation.isFinitePresentation_restrictToChartModule`: the
  chart restriction of `F_T` is of finite presentation on the chart's scheme.

## Implementation notes

The functor, the condition and the reduction of part (2) to a statement about one cofiltered
limit are
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorSheafAndLimits.lean`:
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving_iff` turns limit
preservation into the assertion that flatness of `F_T` over a cofiltered limit `T` of affine
test schemes already holds over a stage, the filtered-colimit bookkeeping being discharged
there.  Reading that assertion on one surjective étale scheme chart is
`StacksFrontier/AlgebraicGeometry/Spaces/FlatteningFunctorChartReduction.lean`, whose
`AlgebraicGeometry.Space.FlatnessSituation.TestChart.isFlatAfterBaseChange_baseChange_iff`
states the condition at a base-changed test scheme exactly as the scheme-level descent theorem
Stacks 05LY, `AlgebraicGeometry.eventually_isFlatOver_modulePullback` of
`StacksFrontier/AlgebraicGeometry/Limits/RelativeApproximation/FlatDescent.lean`, tests it.  What
this file adds is the construction of the chart and the verification of the hypotheses of
Stacks 05LY on it.

The chart is chosen affine: `X_T` is quasi-compact for `T` affine, because `f` is quasi-compact
(Stacks 03HE applied to the represented `T`, whose point space is compact), and a quasi-compact
algebraic space has an affine surjective étale chart by Stacks 03H6,
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`.  Its
structure morphism to `T` is the chart followed by the projection `X_T ⟶ T`; the chart is étale
hence locally of finite presentation, the projection is a base change of `f`, and the composite
of the two is read on the chart objects of the site through the identity charts of its source
and target.  With source and target affine the morphism is affine, hence quasi-compact and
quasi-separated, so it is of finite presentation.

The module tested is the chart restriction of `F_T`.  Its quasi-coherence is Stacks 03GA
followed by Stacks 03M0, and its finite presentation is Stacks 03DO followed by the chartwise
reading of Stacks 03DL (7):
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback` carries finite presentation
on the small étale site along the projection `X_T ⟶ X`, and
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChart` restricts it to the chart.  The
two instance arguments of Stacks 05LY are supplied with the structure ring of the chart's scheme
spelled `structureSheafRing _.toRingedSpace`; handed `Scheme.ringCatSheaf` instead, instance
search does not match them against the goal.

The index universes are those of the schemes.  Stacks 05LY constrains its index category by
`CategoryTheory.EssentiallySmall.{u}`, which for an index category in `Type u` with morphisms in
`Type u` is automatic, so part (2) is stated at
`AlgebraicGeometry.LimitPreserving.{u, u, u, u, u + 1, u}` — the instance `w = w' = u` of the
universe-polymorphic equivalence `flatFunctor_limitPreserving_iff`.  Unlike the scheme-level
Stacks 05MY, whose scheme universe is the maximum of the two index universes and so leaves them
free below it, the scheme universe here is pinned by the big fppf site, and `u` is the largest
index universe Stacks 05LY admits over it.

What part (2) asserts beyond this is its uniqueness half, which needs none of the hypotheses
above and is proved separately as
`AlgebraicGeometry.Space.FlatnessSituation.subsingleton_colimitType_flatFunctor`.

## References

* [Stacks Project, Tag 0CWZ](https://stacks.math.columbia.edu/tag/0CWZ)
* [Stacks Project, Tag 0CWX](https://stacks.math.columbia.edu/tag/0CWX)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 05MY](https://stacks.math.columbia.edu/tag/05MY)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace FlatnessSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The hypotheses of Stacks 05LY on a chart of `X_T` -/

/-- **The base change of the source to an affine test scheme is a quasi-compact algebraic
space.**  A test scheme with affine underlying scheme has compact point space, so it represents
a quasi-compact algebraic space, and quasi-compactness of `f` is exactly the assertion of
Stacks 03HE that its base change along such a morphism is quasi-compact. -/
theorem isQuasiCompactSpace_baseChangeSpace (D : FlatnessSituation.{u} B S hS)
    (hqc : IsQuasiCompact B S hS D.f.hom) (T : SchemesOver D.Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    IsQuasiCompactSpace B S hS (baseChangeSpace D.f T).1 := by
  have := hT
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T.left) :=
    Scheme.compactSpace_of_isAffine _
  exact IsQuasiCompactSpace.of_iso B S hS
    (hqc (yoneda.obj T.left) (isAlgebraicSpace_yoneda B S hS T.left)
      (isQuasiCompact_yoneda_of_compact B S hS T.left inferInstance) T.hom.hom)
    (pullbackSymmetry _ _)

/-- **The projection `X_T ⟶ T` is locally of finite presentation** when `f` is: the square of
the two projections of the fibre product is cartesian, and local finite presentation of
morphisms of algebraic spaces is stable under base change. -/
theorem isLocallyOfFinitePresentation_baseChangeInclusion (D : FlatnessSituation.{u} B S hS)
    (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom) (T : SchemesOver D.Y) :
    IsLocallyOfFinitePresentation B S hS (baseChangeInclusion D.f T).hom := by
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  exact MorphismProperty.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
      IsLocallyOfFinitePresentation B S hS f.hom)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f
      ((schemesOverToOver D.Y).obj T).hom) hlfp

/-- **An affine test chart over an affine test scheme, of finite presentation over it.**  For a
quasi-compact `f` which is locally of finite presentation and a test scheme `T` with affine
underlying scheme, `X_T` has a surjective étale scheme chart whose chart object is affine and
whose structure morphism to `T` is locally of finite presentation.

`X_T` is quasi-compact by `isQuasiCompactSpace_baseChangeSpace`, so Stacks 03H6 supplies an
affine surjective étale chart; the morphism of chart objects over `T` exists because `yoneda` is
full, and it is locally of finite presentation because that is the chartwise condition of
Stacks 03MJ (1) on the projection `X_T ⟶ T`, read on the square joining the chart to the
identity chart of `T` — `AlgebraicGeometry.Space.prop_toScheme_map_of_holdsOnEveryEtaleChart`. -/
theorem exists_affine_testChart (D : FlatnessSituation.{u} B S hS)
    (hqc : IsQuasiCompact B S hS D.f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom) (T : SchemesOver D.Y)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    ∃ C : TestChart D T, IsAffine ((BigFppfOver.toScheme B S hS).obj C.obj) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map C.down) := by
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (baseChangeSpace D.f T).1 (baseChangeSpace D.f T).2).mp
      (D.isQuasiCompactSpace_baseChangeSpace hqc T hT)
  obtain ⟨α, hα⟩ : ∃ α : U ⟶ T.left,
      a ≫ (baseChangeInclusion D.f T).hom = yoneda.map α :=
    ⟨Yoneda.fullyFaithful.preimage (a ≫ (baseChangeInclusion D.f T).hom),
      (Yoneda.fullyFaithful.map_preimage _).symm⟩
  refine ⟨{ obj := U
            chart := a
            down := α
            etale := haet
            surjective := (presheafSurjective_iff_isSurjective_yoneda B S hS _
              (baseChangeSpace D.f T).2 U a).mp hasurj
            comm := hα }, hUaff, ?_⟩
  exact prop_toScheme_map_of_holdsOnEveryEtaleChart B S hS
    (D.isLocallyOfFinitePresentation_baseChangeInclusion hlfp T) a
    ((isEtale_iff_presheaf_of_yoneda B S hS a).mp haet) hα.symm

/-- **The chart restriction of `F_T` to a test chart is of finite presentation.**  `F_T` is of
finite presentation on the small étale site of `X_T` by Stacks 03DO, being the inverse image of
`F` along the projection `X_T ⟶ X`, and the restriction of a quasi-coherent module of finite
presentation on the site to an étale scheme chart is of finite presentation on that chart. -/
theorem isFinitePresentation_restrictToChartModule (D : FlatnessSituation.{u} B S hS)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F) {T : SchemesOver D.Y}
    (C : TestChart D T) :
    SheafOfModules.IsFinitePresentation
      (restrictToChart B S hS (baseChangeSpace D.f T).2 (D.baseChangeModule T)
        (etaleChartOfIsEtale B S hS C.chart C.etale)) :=
  isFinitePresentation_restrictToChart B S hS (baseChangeSpace D.f T) (D.baseChangeModule T)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeProjection D.f T) D.F D.quasicoherent)
    (isFinitePresentationOnSite_modulePullback B S hS (baseChangeProjection D.f T) D.F hFfp) _

/-! ### Part (2) -/

/-- **Stacks 0CWZ, part (2).**  Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces
over `S` which is locally of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module of
finite presentation.  Then the functor `F_flat` of equation 0CWY is limit preserving in the sense
of Stacks 049J: it carries a cofiltered inverse limit of affine test schemes over `Y` to a
filtered colimit of sets.

`F_flat` is subterminal, so limit preservation is, by
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving_iff`, the assertion that
flatness of `F_T` over a cofiltered limit `T` of affine test schemes already holds over one of
the stages.  Pick a stage, read the condition over it on an affine surjective étale scheme chart
of `X_{T_i}` of finite presentation over `T_i`
(`AlgebraicGeometry.Space.FlatnessSituation.exists_affine_testChart`), and the condition at every
test scheme over that stage becomes flatness of the Zariski inverse image of the chart
restriction over the base-changed chart scheme
(`AlgebraicGeometry.Space.FlatnessSituation.TestChart.isFlatAfterBaseChange_baseChange_iff`).
That is the statement the scheme-level descent theorem Stacks 05LY,
`AlgebraicGeometry.eventually_isFlatOver_modulePullback`, descends to a stage; its hypotheses on
the chart are finite presentation of its structure morphism and finite presentation of the
restricted module, which are the two preceding results. -/
@[stacks 0CWZ "part (2), at the tag's own hypotheses; the index universe of the cofiltered \
system is the universe of the schemes, which is the largest Stacks 05LY admits",
  ega "IV 11.2.6.1" "(ii)"]
theorem flatFunctor_limitPreserving (D : FlatnessSituation.{u} B S hS)
    (hqc : IsQuasiCompact B S hS D.f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F) :
    LimitPreserving.{u, u, u, u, u + 1, u} D.testScheme D.flatFunctor := by
  refine D.flatFunctor_limitPreserving_iff.mpr ?_
  intro I _ _ E c hc haff _hpt hflat
  obtain ⟨i₀⟩ := (IsCofiltered.nonempty : Nonempty I)
  obtain ⟨C, hCaff, hClfp⟩ := D.exists_affine_testChart hqc hlfp (E.obj i₀) (haff i₀)
  have (i : I) : IsAffine ((E ⋙ D.testScheme).obj i) := haff i
  have (i : I) : CompactSpace ((E ⋙ D.testScheme).obj i) :=
    Scheme.compactSpace_of_isAffine _
  have (i : I) : QuasiSeparatedSpace ((E ⋙ D.testScheme).obj i) := inferInstance
  have : ∀ {i j : I} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((E ⋙ D.testScheme).map e) :=
    fun _ => _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj C.obj) := hCaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i₀).left) := haff i₀
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map C.down) := hClfp
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map C.down) :=
    _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  have hXfp : FinitePresentation ((BigFppfOver.toScheme B S hS).map C.down) :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  have hYfp : FinitePresentation (𝟙 ((E ⋙ D.testScheme).obj i₀)) :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  have : SheafOfModules.IsQuasicoherent
      (R := _root_.structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj C.obj).toRingedSpace)
      (restrictToChart B S hS (baseChangeSpace D.f (E.obj i₀)).2
        (D.baseChangeModule (E.obj i₀)) (etaleChartOfIsEtale B S hS C.chart C.etale)) :=
    C.isQuasicoherent_restrictToChartModule
  have : SheafOfModules.IsFinitePresentation
      (R := _root_.structureSheafRing
        ((BigFppfOver.toScheme B S hS).obj C.obj).toRingedSpace)
      (restrictToChart B S hS (baseChangeSpace D.f (E.obj i₀)).2
        (D.baseChangeModule (E.obj i₀)) (etaleChartOfIsEtale B S hS C.chart C.etale)) :=
    D.isFinitePresentation_restrictToChartModule hFfp C
  obtain ⟨j, e, hj⟩ := eventually_isFlatOver_modulePullback (E ⋙ D.testScheme)
    (D.testScheme.mapCone c) hc i₀
    (Over.mk ((BigFppfOver.toScheme B S hS).map C.down))
    (Over.mk (𝟙 ((E ⋙ D.testScheme).obj i₀)))
    hXfp hYfp
    (Over.homMk ((BigFppfOver.toScheme B S hS).map C.down))
    (restrictToChart B S hS (baseChangeSpace D.f (E.obj i₀)).2
      (D.baseChangeModule (E.obj i₀)) (etaleChartOfIsEtale B S hS C.chart C.etale))
    ((isFlatOver_overPullback_map_iff
      (Over.mk ((BigFppfOver.toScheme B S hS).map C.down))
      ((D.testScheme.mapCone c).π.app i₀) _).mpr
      ((C.isFlatAfterBaseChange_baseChange_iff (c.π.app i₀)).mp hflat))
  exact ⟨j, (C.isFlatAfterBaseChange_baseChange_iff (E.map e)).mpr
    ((isFlatOver_overPullback_map_iff
      (Over.mk ((BigFppfOver.toScheme B S hS).map C.down))
      ((E ⋙ D.testScheme).map e) _).mp hj)⟩

end FlatnessSituation

end AlgebraicGeometry.Space

end
