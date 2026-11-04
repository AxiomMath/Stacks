module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StructureSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The chart system of a limit situation is a system of surjective étale charts

In the proof of Stacks 07SI one chooses an affine chart `U₀ ⟶ X₀` of the chosen stage of a limit
situation and uses the base changes `Uᵢ = Xᵢ ×_{X₀} U₀` as charts of the later stages.  Two
different constructions of those base changes are in the library and they had not been joined up:

* `AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram` produces them as the diagram of
  *affine objects of the big fppf site* carried by an
  `AlgebraicGeometry.Space.AffineChartSystem`, which is what the consumer
  `isSectionsColimit_of_equalizerPresentation_of_relationChart` in the namespace
  `AlgebraicGeometry.Space.LimitSituation` takes its two systems of schemes to be; and
* `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer`, the stagewise equalizer
  presentation of Stacks 07SG for the structure sheaf, wants its chart as an object of the *small
  étale site* `AlgebraicGeometry.Space.SmallEtale` of the stage, surjective on points, together
  with a relation chart in the `AlgebraicGeometry.Space.comparisonFunctor` form Stacks 03M8 asks
  for.

This file reads the first as the second, and the reading needs **no isomorphism of schemes**: a
chart system's value at a stage already *is* an object of the site with a morphism
`AlgebraicGeometry.Space.AffineChartSystem.stageMap` to that stage, so all that is missing is the
étale-chart property of that morphism, and that is a base change of the étale-chart property of
`U₀ ⟶ X₀` along the transition morphism.  The resulting object of the small étale site therefore
has the chart system's own object of the site underneath it, on the nose, and
`AlgebraicGeometry.Space.LimitSituation.toScheme_stagesEtaleChart` and
`.appTopHom_stagesSchemeHom` — the identification of the schemes and of the restriction maps — are
proved by `rfl`.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.stagesEtaleChart`: the chart of a stage, as an object of
  the small étale site of that stage.
* `AlgebraicGeometry.Space.LimitSituation.stagesEtaleChartMap`: the map of charts induced by a
  morphism of the two scheme-valued points, as a morphism of the small étale site of the stage.
* `AlgebraicGeometry.Space.LimitSituation.chartEqualizerPresentation`: **the hypothesis `e` of
  `isSectionsColimit_of_equalizerPresentation_of_relationChart`, supplied** for the structure
  sheaf — the stagewise equalizer presentation of Stacks 07SG over the chart system of an affine
  surjective étale chart of the chosen stage and its relation.

## Main results

* `AlgebraicGeometry.Space.exists_affine_isSurjective_etaleChart` and
  `AlgebraicGeometry.Space.LimitSituation.exists_affine_isSurjective_etaleChart_stage`:
  **Stacks 03H6 in the shape the chart system consumes** — a quasi-compact algebraic space, and
  so every stage of a limit situation, has an affine scheme-valued point which is an étale chart
  surjective on points.  This is what makes the hypotheses of the presentation below
  satisfiable, so that nothing here is vacuous.
* `AlgebraicGeometry.Space.AffineChartSystem.isEtaleChart_stageMap`: **Stacks 03G2, part (4), for
  the charts of a chart system** — the base change of an étale chart along a transition morphism
  is an étale chart.
* `AlgebraicGeometry.Space.AffineChartSystem.isSurjective_stageMap`: **Stacks 03MH for the charts
  of a chart system** — the base change of a chart surjective on points is surjective on points.
* `AlgebraicGeometry.Space.AffineChartSystem.isPullback_inducedPresheafMap` and
  `.isPullback_yoneda_inducedMap`: **the relation system is the self fibre product of the chart
  system**, stagewise, as a cartesian square of presheaves.
* `AlgebraicGeometry.Space.LimitSituation.isPullback_comparisonFunctor_stagesEtaleChartMap`: that
  square read in the spaces-étale site of the stage, which is the shape of the hypothesis `hR` of
  Stacks 03M8.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_limitEqualizerPresentation_of_unit`:
  the consumer with `e` discharged, so that only the presentation `eT` at the limit and the two
  naturality statements `he`, `heT` remain.

## Implementation notes

*Why `AlgebraicGeometry.Space.smallBaseChange` is not used.*  That functor (Stacks 03G2, part (4))
base changes an étale chart along a *representable morphism of algebraic spaces* and builds its
value out of `CategoryTheory.Functor.relativelyRepresentable.fst`.  Its value at `U₀` is a
different object from the chart system's, so using it would owe an isomorphism of schemes between
the two and the compatibility of that isomorphism with the restriction maps
`AlgebraicGeometry.Space.LimitSituation.chartStagesRestriction`.  Proving the étale-chart property
directly from `AlgebraicGeometry.Space.AffineChartSystem.isPullback`, which is the same
base-change stability argument `smallBaseChange` itself uses, avoids both: the object is the chart
system's, so the two identifications are definitional.

*The relation square.*  The presheaf-level computation is three applications of the pasting
calculus for cartesian squares.  Writing `a`, `b` for the two projections of `Uⱼ = Xⱼ ×_{X₀} U₀`
and `a'`, `b'` for those of `Rⱼ = Xⱼ ×_{X₀} R₀`, cancelling `Uⱼ` out of `Rⱼ = Xⱼ ×_{X₀} R₀` gives
`Rⱼ = Uⱼ ×_{U₀} R₀`; pasting that with `R₀ = U₀ ×_{X₀} U₀` gives `Rⱼ = Uⱼ ×_{X₀} U₀`, the map
`Uⱼ ⟶ X₀` being `b ≫ f₀`; and cancelling `Uⱼ = Xⱼ ×_{X₀} U₀` out of *that* gives
`Rⱼ = Uⱼ ×_{Xⱼ} Uⱼ`, which is the square wanted.  It is carried into the spaces-étale site by
`CategoryTheory.IsPullback.of_map_of_faithful` along
`AlgebraicGeometry.Space.SpacesEtale.toSpaces` followed by the inclusion of algebraic spaces into
presheaves, exactly as in
`AlgebraicGeometry.Space.exists_etaleChart_isPullback_self`.

*No tag is attached to the base-change statements.*  Stacks 03G2, part (4) is carried by
`AlgebraicGeometry.Space.smallBaseChange` and Stacks 03MH by
`AlgebraicGeometry.Space.isSurjective_of_isPullback`; the two statements here are those results
read at a chart system, not second tag sites.

### Not proved here

**Stacks 07SI is not proved here and no `@[stacks]` attribute appears in this file.**  Of the four
hypotheses `e`, `eT`, `he`, `heT` left open by
`isSectionsColimit_of_equalizerPresentation_of_relationChart`, this file supplies exactly `e`, for
the structure sheaf; its own hypotheses on the chart of the chosen stage are satisfiable by
`AlgebraicGeometry.Space.LimitSituation.exists_affine_isSurjective_etaleChart_stage`, and those on
the relation by
`AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated` at a
separated stage.  What remains, relative to
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_limitEqualizerPresentation_of_unit`:

* **`eT`, the presentation at the limit.**  Stacks 03M8 for the structure sheaf of the limit
  algebraic space, over the chart `U = lim Uᵢ` of
  `AlgebraicGeometry.Space.LimitSituation.chartStagesCone`.  Nothing *here* says that cone's
  vertex is an étale chart of the limit, nor that it is surjective on points, those being limit
  statements about the system of charts rather than stagewise ones.  Both are nevertheless
  proved, in `StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartLimitEtaleChart.lean`, by exactly
  the base-change arguments of this file applied to the *limit projection* in place of a
  transition morphism: `AlgebraicGeometry.Space.LimitSituation.isPullback_limitChartToSpace`
  exhibits the vertex as `X ×_{X₀} U₀`, and
  `AlgebraicGeometry.Space.LimitSituation.isEtaleChart_limitChartToSpace` and
  `.isSurjective_limitChartToSpace` are the two stability statements at that square.
* **`he`, naturality in the stage.**  By
  `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer_apply_val` the two sides are
  evaluation at the charts, so what is needed is the compatibility of the components of
  `AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso` with
  `AlgebraicGeometry.Space.modulePullbackCompIso`, the comparison through which
  `AlgebraicGeometry.Space.LimitSituation.stageTransition` is defined.  That compatibility is not
  established anywhere in the library.  It is not the components themselves that are
  missing: the component of the inverse image of the structure sheaf on the unit function is
  `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_val_app_one`, corepresentability yielding
  that one value through the transpose computed in
  `StacksFrontier/AlgebraicGeometry/Spaces/StructureSheafPullbackUnitSections.lean`.  What remains
  open is the compatibility with `AlgebraicGeometry.Space.modulePullbackCompIso` alone.
* **`heT`**, the same statement for the maps to the limit, and therefore dependent on `eT`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SG](https://stacks.math.columbia.edu/tag/07SG)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### An affine surjective étale chart of a quasi-compact algebraic space -/

section Existence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03H6, in the shape the chart system of Stacks 03WF consumes.**  A quasi-compact
algebraic space has an *affine* scheme-valued point which is an étale chart surjective on
points.

This is `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`
with its affine object read as an object of the big *affine* fppf category, its étaleness read
as the étale-chart property (`AlgebraicGeometry.Space.presheaf_etale_of_isEtale`) and its
surjectivity read on points (Stacks 03H5,
`AlgebraicGeometry.Space.surjective_iff_surjective_pointsMap`).  It is what makes the
hypotheses of `AlgebraicGeometry.Space.LimitSituation.chartEqualizerPresentation`
satisfiable. -/
theorem exists_affine_isSurjective_etaleChart (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hqc : IsQuasiCompactSpace B S hS F) :
    ∃ (U : BigAffineFppf B S hS)
      (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U) ⟶ F),
      IsEtaleChart B S hS F (CostructuredArrow.mk f) ∧ IsSurjective B S hS f := by
  obtain ⟨U, f, haff, hsurj, hetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).1 hqc
  exact ⟨⟨U, haff⟩, f, presheaf_etale_of_isEtale B S hS hetale,
    (surjective_iff_surjective_pointsMap B S hS F hF U f).1 hsurj⟩

/-- **Every stage of a limit situation has an affine surjective étale chart.**  The stages of a
limit situation are algebraic spaces and quasi-compact, both by the fields of Situation 084R, so
`AlgebraicGeometry.Space.exists_affine_isSurjective_etaleChart` applies to each of them — in
particular to the chosen stage, which is the one the chart systems of the proof of Stacks 07SI
are built over. -/
theorem LimitSituation.exists_affine_isSurjective_etaleChart_stage
    {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A : LimitSituation B S hS hZ X) (i : A.I) :
    ∃ (U : BigAffineFppf B S hS)
      (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U) ⟶ A.system.obj (op i)),
      IsEtaleChart B S hS (A.system.obj (op i)) (CostructuredArrow.mk f) ∧
        IsSurjective B S hS f :=
  exists_affine_isSurjective_etaleChart B S hS _ (A.isAlgebraicSpace i) (A.quasiCompact i)

end Existence

/-! ### The charts of a chart system are surjective étale charts -/

section Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

/-- **A projection of a self fibre product of an étale chart, composed with the chart, is an
étale chart.**  If `f₀ : yoneda U₀ ⟶ F` is an étale chart and `R₀` is the fibre product
`U₀ ×_F U₀` with projections `t` and `u`, then `t` is a base change of `f₀` and so an étale chart
of `yoneda U₀`, whence `t ≫ f₀` is an étale chart of `F`.

In the proof of Stacks 07SI this is the étale-chart property of the relation `R₀ ⟶ X₀`, which is
the scheme-valued point the relation system of the proof is the chart system of. -/
theorem isEtaleChart_comp_of_isPullback {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V W : BigFppfOver B S hS} {g : yoneda.obj V ⟶ F}
    {t u : yoneda.obj W ⟶ yoneda.obj V}
    (hg : IsEtaleChart B S hS F (CostructuredArrow.mk g)) (hpb : IsPullback t u g g) :
    IsEtaleChart B S hS F (CostructuredArrow.mk (t ≫ g)) :=
  have := isMultiplicative_presheaf_etale B S hS
  MorphismProperty.comp_mem _ _ _
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb.flip hg) hg

namespace AffineChartSystem

variable (C : AffineChartSystem B S hS i₀ D U₀ f₀)

/-- **Stacks 03G2, part (4), for the charts of a chart system.**  If the scheme-valued point
`f₀ : yoneda U₀ ⟶ D i₀` a chart system is built from is an étale chart of the base stage, then
the projection of every chart `Uⱼ = Dⱼ ×_{D i₀} U₀` to its own stage is an étale chart of that
stage: the chart is the base change of `f₀` along the transition morphism
`AlgebraicGeometry.Space.AffineChartSystem.isPullback`, and the étale-chart property of a
morphism of presheaves is stable under base change.

The tag is carried by `AlgebraicGeometry.Space.smallBaseChange`; this is that stability read at
a chart system, and so is not a second tag site. -/
theorem isEtaleChart_stageMap
    (hf₀ : IsEtaleChart B S hS (D.obj i₀) (CostructuredArrow.mk f₀)) (j : Over i₀) :
    IsEtaleChart B S hS (D.obj j.left) (CostructuredArrow.mk (C.stageMap j)) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (C.isPullback j).flip hf₀

/-- **Stacks 03MH for the charts of a chart system.**  If the scheme-valued point a chart system
is built from is surjective on points, so is the projection of every chart to its own stage: a
point of the stage and the point of `U₀` above its image in `D i₀` lift to a point of the base
change, by Stacks 03H4.

The tag is carried by `AlgebraicGeometry.Space.isSurjective_of_isPullback`; this is that result
read at a chart system. -/
theorem isSurjective_stageMap (hf₀ : IsSurjective B S hS f₀) (j : Over i₀) :
    IsSurjective B S hS (C.stageMap j) := by
  intro z
  obtain ⟨x, hx⟩ := hf₀ (pointsMap B S hS (D.obj j.left) (D.map j.hom) z)
  obtain ⟨w, hw, -⟩ :=
    exists_point_of_isPullback_presheaf B S hS (C.isPullback j) z x hx.symm
  exact ⟨w, hw⟩

/-! ### The relation system is the self fibre product of the chart system -/

section Relation

variable {R₀ : BigAffineFppf B S hS}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ D.obj i₀}
  {t u : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (E : AffineChartSystem B S hS i₀ D R₀ g₀)

/-- **The relation system of a chart system is the self fibre product of the chart system**, as a
cartesian square of presheaves at a single stage.  Let `t` and `u` be two morphisms of
scheme-valued points `R₀ ⟶ U₀` over `D i₀` exhibiting `R₀` as `U₀ ×_{D i₀} U₀`.  Then the two
maps of charts they induce exhibit `Rⱼ = Dⱼ ×_{D i₀} R₀` as the fibre product of
`Uⱼ = Dⱼ ×_{D i₀} U₀` with itself over the stage `Dⱼ`.

Three applications of the pasting calculus; see the implementation notes of this file. -/
theorem isPullback_inducedPresheafMap (ht : t ≫ f₀ = g₀) (hu : u ≫ f₀ = g₀)
    (hpb : IsPullback t u f₀ f₀) (j : Over i₀) :
    IsPullback (C.inducedPresheafMap E ht j) (C.inducedPresheafMap E hu j)
      (C.stageMap j) (C.stageMap j) := by
  have h1 : IsPullback (E.baseMap j) (C.inducedPresheafMap E ht j) t (C.baseMap j) := by
    refine IsPullback.of_bot ?_ (C.inducedPresheafMap_comp_baseMap E ht j).symm
      (C.isPullback j).flip
    rw [C.inducedPresheafMap_comp_stageMap E ht j, ht]
    exact (E.isPullback j).flip
  have h2 := h1.paste_horiz hpb.flip
  refine (IsPullback.of_right ?_ ?_ (C.isPullback j).flip).flip
  · rw [C.inducedPresheafMap_comp_baseMap E hu j, (C.isPullback j).w]
    exact h2
  · rw [C.inducedPresheafMap_comp_stageMap E hu j, C.inducedPresheafMap_comp_stageMap E ht j]

/-- **The same square, with its two parallel maps read as morphisms of the site.**  This is the
form in which the square is carried into the spaces-étale site of the stage, the morphisms of the
small étale site there being morphisms of the big fppf site of `S`. -/
theorem isPullback_yoneda_inducedMap (ht : t ≫ f₀ = g₀) (hu : u ≫ f₀ = g₀)
    (hpb : IsPullback t u f₀ f₀) (j : Over i₀) :
    IsPullback (yoneda.map (C.inducedMap E ht j)) (yoneda.map (C.inducedMap E hu j))
      (C.stageMap j) (C.stageMap j) := by
  rw [C.yoneda_map_inducedMap E ht j, C.yoneda_map_inducedMap E hu j]
  exact C.isPullback_inducedPresheafMap E ht hu hpb j

end Relation

end AffineChartSystem

end Chart

/-! ### The chart of a stage of a limit situation, in its small étale site -/

namespace LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X) {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))

/-- **The chart of a stage, as an object of the small étale site of that stage.**  The value of a
chart system at a stage is an affine object of the big fppf site of `S` with a projection to that
stage, and `AlgebraicGeometry.Space.AffineChartSystem.isEtaleChart_stageMap` makes that projection
an étale chart; so the pair is an object of the small étale site of the stage.

It is the *same* object of the site the chart system carries, so the underlying scheme is on the
nose the value of `AlgebraicGeometry.Space.LimitSituation.stagesSchemeDiagram`; see
`AlgebraicGeometry.Space.LimitSituation.toScheme_stagesEtaleChart`. -/
noncomputable def stagesEtaleChart (i : A.Stages) : SmallEtale B S hS (A.stage i.1).obj :=
  ⟨CostructuredArrow.mk (C.stageMap ((stagesOverEquivalence A).functor.obj (op i))),
    C.isEtaleChart_stageMap hf₀ _⟩

/-- **The scheme of the chart of a stage is the value of the reindexed diagram of schemes.**  No
transport: the object of the site underlying the étale chart is the chart system's own, and the
reindexed diagram of schemes is that object read as a scheme. -/
theorem toScheme_stagesEtaleChart (i : A.Stages) :
    (BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS (A.stage i.1).obj).obj (A.stagesEtaleChart C hf₀ i))
      = (stagesSchemeDiagram A C).obj (op i) :=
  rfl

/-- **The chart of a stage is surjective on points** as soon as the chart of the chosen stage
is. -/
theorem isSurjective_stagesEtaleChart (hsurj : IsSurjective B S hS f₀) (i : A.Stages) :
    IsSurjective B S hS (A.stagesEtaleChart C hf₀ i).1.hom :=
  C.isSurjective_stageMap hsurj _

section Relation

variable {R₀ : BigAffineFppf B S hS}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ A.system.obj (op A.base)}
  {t u : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (E : AffineChartSystem B S hS (op A.base) A.system R₀ g₀)
  (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))

/-- **The induced map of charts, as a morphism of the small étale site of the stage.**  The
triangle over the stage is
`AlgebraicGeometry.Space.AffineChartSystem.inducedPresheafMap_comp_stageMap`. -/
noncomputable def stagesEtaleChartMap (ht : t ≫ f₀ = g₀) (i : A.Stages) :
    A.stagesEtaleChart E hg₀ i ⟶ A.stagesEtaleChart C hf₀ i :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (C.inducedMap E ht ((stagesOverEquivalence A).functor.obj (op i)))
    (C.yoneda_map_inducedMap E ht _ ▸ C.inducedPresheafMap_comp_stageMap E ht _))

/-- **Restriction along that morphism is the restriction map of the reindexed systems.**  Again no
transport: the morphism of the small étale site is the chart system's own induced map of charts,
and `AlgebraicGeometry.Space.LimitSituation.chartStagesRestriction` is global sections of that
map. -/
theorem appTopHom_stagesSchemeHom (ht : t ≫ f₀ = g₀) (i : A.Stages)
    (a : Γ((stagesSchemeDiagram A C).obj (op i), ⊤)) :
    appTopHom (stagesSchemeHom A C E ht) i a
      = ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS (A.stage i.1).obj).map
            (A.stagesEtaleChartMap C hf₀ E hg₀ ht i))).appTop.hom a :=
  rfl

/-- **The relation chart of a stage, in the shape Stacks 03M8 asks for.**  The two induced maps of
charts exhibit the comparison image of `Rᵢ` as the fibre product of the comparison image of `Uᵢ`
with itself over the terminal object of the spaces-étale site of the stage, that is as
`Uᵢ ×_{Xᵢ} Uᵢ`.

This is `AlgebraicGeometry.Space.AffineChartSystem.isPullback_yoneda_inducedMap` carried along
`AlgebraicGeometry.Space.SpacesEtale.toSpaces` followed by the inclusion of algebraic spaces into
presheaves, which is faithful and reflects the limit in question; the two morphisms to the
terminal object become the chart's own structure morphism by
`AlgebraicGeometry.Space.SpacesEtale.toSpaces_map_from_idObj`. -/
theorem isPullback_comparisonFunctor_stagesEtaleChartMap
    (ht : t ≫ f₀ = g₀) (hu : u ≫ f₀ = g₀) (hpb : IsPullback t u f₀ f₀) (i : A.Stages) :
    IsPullback
      ((comparisonFunctor B S hS (A.stage i.1)).map
        (A.stagesEtaleChartMap C hf₀ E hg₀ ht i))
      ((comparisonFunctor B S hS (A.stage i.1)).map
        (A.stagesEtaleChartMap C hf₀ E hg₀ hu i))
      ((SpacesEtale.isTerminal_idObj B S hS (A.stage i.1)).from
        ((comparisonFunctor B S hS (A.stage i.1)).obj (A.stagesEtaleChart C hf₀ i)))
      ((SpacesEtale.isTerminal_idObj B S hS (A.stage i.1)).from
        ((comparisonFunctor B S hS (A.stage i.1)).obj (A.stagesEtaleChart C hf₀ i))) := by
  refine IsPullback.of_map_of_faithful
    (SpacesEtale.toSpaces B S hS (A.stage i.1) ⋙ ObjectProperty.ι _) ?_
  have hfrom : (SpacesEtale.toSpaces B S hS (A.stage i.1) ⋙ ObjectProperty.ι _).map
        ((SpacesEtale.isTerminal_idObj B S hS (A.stage i.1)).from
          ((comparisonFunctor B S hS (A.stage i.1)).obj (A.stagesEtaleChart C hf₀ i)))
      = C.stageMap ((stagesOverEquivalence A).functor.obj (op i)) :=
    congrArg (fun k => k.hom) (SpacesEtale.toSpaces_map_from_idObj B S hS
      ((comparisonFunctor B S hS (A.stage i.1)).obj (A.stagesEtaleChart C hf₀ i)))
  rw [hfrom]
  exact C.isPullback_yoneda_inducedMap E ht hu hpb _

/-- **The stagewise equalizer presentation of Stacks 07SG over a chart system.**  With the
coefficients `ℱ₀` of Stacks 07SI taken to be the structure sheaf of the chosen stage, the group
`Γ(Xᵢ, ℱᵢ)` is in bijection with the global functions on the chart `Uᵢ` of the chart system
equalized by the two maps the relation induces:

`Γ(Xᵢ, ℱᵢ) ≃ {x : Γ(Uᵢ, 𝒪) // p^*x = q^*x}`.

This is `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer` at the étale chart
`AlgebraicGeometry.Space.LimitSituation.stagesEtaleChart` and the relation square
`AlgebraicGeometry.Space.LimitSituation.isPullback_comparisonFunctor_stagesEtaleChartMap`; the
equalized pair is the pair of restriction maps of the reindexed systems on the nose, by
`AlgebraicGeometry.Space.LimitSituation.appTopHom_stagesSchemeHom`. -/
noncomputable def stageSectionsEquivChartEqualizer (hsurj : IsSurjective B S hS f₀)
    (ht : t ≫ f₀ = g₀) (hu : u ≫ f₀ = g₀) (hpb : IsPullback t u f₀ f₀) (i : A.Stages) :
    A.stageSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i ≃
      {x : (Γ((stagesSchemeDiagram A C).obj (op i), ⊤) : Type u) //
        appTopHom (stagesSchemeHom A C E ht) i x
          = appTopHom (stagesSchemeHom A C E hu) i x} :=
  stageSectionsEquivEqualizer B S hS A i (A.isSurjective_stagesEtaleChart C hf₀ hsurj i)
    (A.isPullback_comparisonFunctor_stagesEtaleChartMap C hf₀ E hg₀ ht hu hpb i)

end Relation

/-! ### The hypothesis `e` of the consumer, supplied -/

section Consumer

variable {R₀ : BigAffineFppf B S hS}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}

/-- **The hypothesis `e` of
`isSectionsColimit_of_equalizerPresentation_of_relationChart` in this namespace, supplied for the
structure sheaf.**  Let `U₀ ⟶ X₀` be an affine scheme-valued point of the chosen
stage of a limit situation which is an étale chart surjective on points, and let `t` and
`yoneda s` be the two projections of its relation `R₀ = U₀ ×_{X₀} U₀`, which at a separated stage
is again affine by
`AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated`.
Then, with the coefficients `ℱ₀` of Stacks 07SI taken to be the structure sheaf of the chosen
stage, the group `Γ(Xᵢ, ℱᵢ)` is in bijection with the equalizer of the two restriction maps
`Γ(Uᵢ, ⊤) → Γ(Rᵢ, ⊤)` of the chart system and the relation system — which is literally the
hypothesis `e` of that statement. -/
noncomputable def chartEqualizerPresentation
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀) (i : A.Stages) :
    A.stageSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i ≃
      {x : (Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤) : Type u) //
        A.chartStagesRestriction (τ := t) (f₀ := f₀) rfl i x
          = A.chartStagesRestriction (τ := yoneda.map s) hpb.w.symm i x} :=
  A.stageSectionsEquivChartEqualizer (A.chartSystem U₀ f₀) hf₀
    (A.chartSystem R₀ (t ≫ f₀)) (isEtaleChart_comp_of_isPullback hf₀ hpb) hsurj rfl
    hpb.w.symm hpb i

/-- **The consumer of the equalizer presentation of Stacks 07SI with its stagewise presentation
`e` discharged**, for the structure sheaf.

What is left is the presentation `eT` at the limit and the two naturality statements `he` and
`heT`; see the "Not proved here" section of this file's module documentation for what each of
them needs.  This statement is therefore **not** Stacks 07SI and carries no tag. -/
theorem isSectionsColimit_of_limitEqualizerPresentation_of_unit
    (hX : IsAlgebraicSpace B S hS X) (hI : #A.I < B.cutoff.ord.cof)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (eT : A.limitSections
        (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX ≃
      {x : (Γ((A.chartStagesCone U₀ f₀ hI).pt, ⊤) : Type u) //
        A.chartStagesRestrictionLimit (τ := t) (f₀ := f₀) rfl hI x
          = A.chartStagesRestrictionLimit (τ := yoneda.map s) hpb.w.symm hI x})
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (σ : A.stageSections
        (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i),
      (A.chartEqualizerPresentation hf₀ hsurj hpb j
          (A.stageTransition (SheafOfModules.unit
            (structureRingSheaf B S hS (A.stage A.base))) i j h σ)).1
        = ((A.chartStagesDiagram U₀ f₀).map (homOfLE h).op).appTop.hom
            (A.chartEqualizerPresentation hf₀ hsurj hpb i σ).1)
    (heT : ∀ (i : A.Stages) (σ : A.stageSections
        (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i),
      (eT (A.stageProjection (SheafOfModules.unit
            (structureRingSheaf B S hS (A.stage A.base))) hX i σ)).1
        = ((A.chartStagesCone U₀ f₀ hI).π.app (op i)).appTop.hom
            (A.chartEqualizerPresentation hf₀ hsurj hpb i σ).1) :
    A.IsSectionsColimit
      (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX :=
  A.isSectionsColimit_of_equalizerPresentation_of_relationChart _ hX hI f₀ hpb
    (A.chartEqualizerPresentation hf₀ hsurj hpb) eT he heT

end Consumer

end LimitSituation

end AlgebraicGeometry.Space

end
