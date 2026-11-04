module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation of a module on an algebraic space from a dense open of the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation, let `F` be a quasi-coherent `𝒪_X`-module of finite type which is
flat over `Y`, and let `V ⊆ Y` be an open subspace whose inclusion is quasi-compact and
scheme-theoretically dense.  If the restriction of `F` to `f⁻¹V` is of finite presentation, then
`F` is of finite presentation.  This is Stacks 0876, the algebraic-space form of Stacks 081N.

Everything is read on the étale scheme charts, and on one commuting square of such charts the
statement is exactly Stacks 081N, the theorem
`isFinitePresentation_of_isFlatOver_of_retrocompact_dense_open` in the namespace
`AlgebraicGeometry.FinitePresentationFromDenseOpen`.
What this file adds over that theorem is the translation of the hypothesis on the open subspace:
the open subscheme of a chart of `Y` cut out by `V` is
`AlgebraicGeometry.Space.chartOpenOfOpenSubspace`, the preimage of the point set of `V` under the
map on points of the chart, which is open because an open subspace has open point set (Tag 03BZ)
and a morphism of presheaves is continuous on points (Tag 03BX).  Its inverse image along the
vertical morphism of the square is the chart-level `f⁻¹V`, by
`AlgebraicGeometry.Space.preimage_chartOpenOfOpenSubspace`.

## Main definitions

* `AlgebraicGeometry.Space.chartOpenOfOpenSubspace` is the Zariski open of an étale scheme chart
  cut out by an open subspace of the ambient algebraic space.
* `AlgebraicGeometry.Space.IsRetrocompactOnCharts` and
  `AlgebraicGeometry.Space.IsSchemeTheoreticallyDenseOnCharts` are the chartwise forms of the two
  halves of hypothesis (3) of the source, that the inclusion of `V` is quasi-compact and
  scheme-theoretically dense.
* `AlgebraicGeometry.Space.IsFinitePresentationOverOpenOnCharts` is the chartwise form of
  hypothesis (4), that `F` restricted to `f⁻¹V` is of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_chartModule_of_isFlatOver_of_dense_open` is
  **Stacks 0876**, read on a commuting square of étale scheme charts;
  `AlgebraicGeometry.Space.isFinitePresentation_chartModule_of_isFlatOver_of_dense_open_charts`
  is the same statement with hypothesis (3) in its chartwise form.
* `AlgebraicGeometry.Space.opensRange_snd_eq_chartOpenOfOpenSubspace` identifies the open
  subscheme of a chart cut out by `V` with the image of the morphism of schemes representing
  `V ×_Y W`; it is what turns the two halves of hypothesis (3) into their chartwise forms, in
  `AlgebraicGeometry.Space.isRetrocompactOnCharts_of_isQuasiCompact` and
  `AlgebraicGeometry.Space.isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense`.
* `AlgebraicGeometry.Space.preimage_chartOpenOfOpenSubspace` identifies the inverse image of the
  chart-level `V` along the vertical morphism of a commuting square of charts with the chart-level
  inverse image of `V` along `f`; it is what makes the chartwise hypothesis (4) above the
  chartwise reading of `F|_{f⁻¹V}`.
* `AlgebraicGeometry.Space.continuous_pointOfEtaleChart` and
  `AlgebraicGeometry.Space.pointOfEtaleChart_map_g` are the two facts about the map on points of
  an étale scheme chart that the translation rests on.

## Implementation notes

A module on an algebraic space is an object of `AlgebraicGeometry.Space.Modules`, a sheaf of
modules on the small étale site, and the only comparison of such a module with a module on a
scheme available in this development is `AlgebraicGeometry.Space.restrictToChart`.  Accordingly
quasi-coherence, finite type and finite presentation of the module are read chartwise, exactly as
in `StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean` for Tag 0DLR: the
hypotheses are `AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
`AlgebraicGeometry.Space.IsFiniteTypeOnCharts` of that file, flatness over `Y` is
`AlgebraicGeometry.Space.IsFlatOver` of Tag 05VV, which is chartwise by definition, and the
conclusion is finite presentation of the restriction of `F` to the source chart of a commuting
square of étale scheme charts.  The conclusion is stated for a square rather than for an
arbitrary chart of `X` because not every étale scheme chart of `X` is the source of a square over
`f`, and because nothing in this development compares the restrictions of a module to two charts
related by a morphism.

Hypothesis (3), on the other hand, is taken in the form the source states it: the inclusion of
`V` is quasi-compact in the sense of Tag 03HE and `V` is scheme-theoretically dense in the sense
of Tag 0834.  Both halves are passed to their chartwise forms here, which is what Stacks 081N
asks for at the scheme level.  For density that is Tag 0836, through
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_forall_chart` and
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_preimage_eq_top_iff`; for
quasi-compactness it is Tag 03HD,
`AlgebraicGeometry.Space.presheaf_quasiCompact_of_isQuasiCompact`.  Both reduce to identifying
the open subscheme that `V` cuts out in a chart with the image of the morphism of schemes
representing `V ×_Y W`, which is
`AlgebraicGeometry.Space.opensRange_snd_eq_chartOpenOfOpenSubspace`.  The chartwise forms remain
available as `AlgebraicGeometry.Space.IsRetrocompactOnCharts` and
`AlgebraicGeometry.Space.IsSchemeTheoreticallyDenseOnCharts`, and
`AlgebraicGeometry.Space.isFinitePresentation_chartModule_of_isFlatOver_of_dense_open_charts`
is the version of the theorem stated with them.

The module universe is the universe of the structure rings, as it must be for
`AlgebraicGeometry.Space.restrictToChart` to land in `AlgebraicGeometry.Scheme.Modules` of the
chart; this is the convention of `AlgebraicGeometry.Space.IsFlatOver`.

`AlgebraicGeometry.Space.pointTopology` of Tag 03BY is a plain definition rather than an instance
and is made a local instance here.

## References

* [Stacks Project, Tag 0876](https://stacks.math.columbia.edu/tag/0876)
* [Stacks Project, Tag 081N](https://stacks.math.columbia.edu/tag/081N)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 0836](https://stacks.math.columbia.edu/tag/0836)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The open subscheme of a chart cut out by an open subspace -/

section ChartOpen

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The map on points of an étale scheme chart is continuous: it is the map on points of the
chart, which is continuous by clause (2) of Tag 03BX, read through the homeomorphism of clause
(1) between the points of a represented presheaf and the points of the representing scheme. -/
theorem continuous_pointOfEtaleChart (U : SmallEtale B S hS X) :
    Continuous (pointOfEtaleChart B S hS U) :=
  (continuous_pointsMap B S hS U.obj.hom).comp
    (schemePointsHomeomorph B S hS U.obj.left).symm.continuous

/-- The Zariski open of an étale scheme chart of `X` cut out by an open subspace `V ⊆ X`: the
preimage of the point set of `V` under the map on points of the chart.  It is open because the
point set of an open subspace is open, by Tag 03BZ. -/
noncomputable def chartOpenOfOpenSubspace (V : Subfunctor X) (hV : IsOpenSubspace B S hS V)
    (U : SmallEtale B S hS X) : (etaleChartScheme B S hS U).Opens :=
  ⟨pointOfEtaleChart B S hS U ⁻¹' Set.range (pointsMap B S hS V.toFunctor V.ι),
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2).preimage
      (continuous_pointOfEtaleChart B S hS U)⟩

/-- Membership in the open subscheme of a chart cut out by an open subspace, unfolded. -/
theorem mem_chartOpenOfOpenSubspace_iff (V : Subfunctor X) (hV : IsOpenSubspace B S hS V)
    (U : SmallEtale B S hS X) (u : etaleChartScheme B S hS U) :
    u ∈ chartOpenOfOpenSubspace B S hS V hV U ↔
      pointOfEtaleChart B S hS U u ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) :=
  Iff.rfl

/-- The point set of the inverse image of an open subspace is the preimage of its point set: one
inclusion is functoriality of the map on points and the other lifts a point of the source whose
image lies in the subspace through the Cartesian square of Tag 083Q. -/
private theorem range_pointsMap_preimage {Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : W ⟶ Z)
    (V : Subfunctor Z) :
    Set.range (pointsMap B S hS (V.preimage p).toFunctor (V.preimage p).ι) =
      pointsMap B S hS W p ⁻¹' Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨z, rfl⟩
    refine ⟨pointsMap B S hS (V.preimage p).toFunctor (V.fromPreimage p) z, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  · rintro x ⟨w, hw⟩
    obtain ⟨z, -, hz⟩ :=
      exists_points_of_isPullback B S hS (Subfunctor.isPullback_preimage p V) w x hw
    exact ⟨z, hz⟩

/-- The map on points of the morphism of the site representing the inverse image of an open
subspace along a scheme chart has the same image as the map on points of the inclusion of that
inverse image: the two differ by the isomorphism
`AlgebraicGeometry.Space.preimageIso`, which is surjective on points. -/
private theorem range_pointsMap_yoneda_snd (V : Subfunctor X) (hV : IsOpenSubspace B S hS V)
    (U : SmallEtale B S hS X) :
    Set.range (pointsMap B S hS (yoneda.obj (hV.2.rep.pullback U.1.hom))
        (yoneda.map (hV.2.rep.snd U.1.hom))) =
      Set.range (pointsMap B S hS (V.preimage U.1.hom).toFunctor (V.preimage U.1.hom).ι) := by
  have hsurj : Function.Surjective (pointsMap B S hS
      (yoneda.obj (hV.2.rep.pullback U.1.hom))
      (preimageIso B S hS V hV.2.rep U.1.hom).hom) := fun y =>
    ⟨pointsMap B S hS _ (preimageIso B S hS V hV.2.rep U.1.hom).inv y, by
      rw [← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id, id_eq]⟩
  rw [← preimageIso_hom_ι B S hS V hV.2.rep U.1.hom, pointsMap_comp, Set.range_comp,
    hsurj.range_eq, Set.image_univ]

/-- **The open subscheme of a chart cut out by an open subspace is the image of the morphism of
schemes representing the inverse image of that subspace in the chart.**

Both are read off the points of the chart: the points of the inverse image `V ×_X U` are the
preimage of the points of `V` under the map on points of the chart, by
`AlgebraicGeometry.Space.range_pointsMap_preimage`, and the inverse image is represented by
`hV.2.rep.snd U.1.hom`, so the comparison bijection of Tag 03BV between the points of a
represented presheaf and the points of the representing scheme carries one set onto the
other. -/
theorem opensRange_snd_eq_chartOpenOfOpenSubspace (V : Subfunctor X)
    (hV : IsOpenSubspace B S hS V) (U : SmallEtale B S hS X)
    [AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd U.1.hom))] :
    ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd U.1.hom)).opensRange =
      chartOpenOfOpenSubspace B S hS V hV U := by
  have hset : Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd U.1.hom)) =
      pointsToScheme B S hS U.1.left ''
        (pointsMap B S hS (yoneda.obj U.1.left) U.1.hom ⁻¹'
          Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
    rw [← image_pointsToScheme_range, range_pointsMap_yoneda_snd B S hS V hV U,
      range_pointsMap_preimage B S hS U.1.hom V]
  refine TopologicalSpace.Opens.ext (Set.ext fun u => ?_)
  rw [Scheme.Hom.coe_opensRange, hset, SetLike.mem_coe, mem_chartOpenOfOpenSubspace_iff]
  refine ⟨?_, fun hu => ⟨(pointsEquivScheme B S hS U.1.left).symm u, hu,
    (pointsEquivScheme B S hS U.1.left).apply_symm_apply u⟩⟩
  rintro ⟨w, hw, rfl⟩
  have hww : (pointsEquivScheme B S hS U.1.left).symm
      (pointsToScheme B S hS U.1.left w) = w :=
    (pointsEquivScheme B S hS U.1.left).symm_apply_apply w
  change pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
    ((pointsEquivScheme B S hS U.1.left).symm _) ∈ _
  rwa [hww]

end ChartOpen

/-! ### Charts of a morphism -/

section ChartDiagramPoints

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A commuting square of étale scheme charts commutes on points: the vertical morphism of
schemes followed by the map on points of the chart of the target is the map on points of the
chart of the source followed by the map on points of the morphism of algebraic spaces. -/
theorem pointOfEtaleChart_map_g {f : X ⟶ Y} (d : ChartDiagram B S hS X Y f)
    (u : etaleChartScheme B S hS d.U) :
    pointOfEtaleChart B S hS d.V ((BigFppfOver.toScheme B S hS).map d.g u) =
      pointsMap B S hS X f (pointOfEtaleChart B S hS d.U u) := by
  have hu : pointsToScheme B S hS d.U.obj.left
      ((pointsEquivScheme B S hS d.U.obj.left).symm u) = u :=
    (pointsEquivScheme B S hS d.U.obj.left).apply_symm_apply u
  have hkey : (pointsEquivScheme B S hS d.V.obj.left).symm
        ((BigFppfOver.toScheme B S hS).map d.g u) =
      pointsMap B S hS (yoneda.obj d.U.obj.left) (yoneda.map d.g)
        ((pointsEquivScheme B S hS d.U.obj.left).symm u) := by
    refine ((pointsEquivScheme B S hS d.V.obj.left).symm_apply_eq).mpr ?_
    change _ = pointsToScheme B S hS d.V.obj.left _
    rw [pointsToScheme_pointsMap_yoneda, hu]
  change pointsMap B S hS (yoneda.obj d.V.obj.left) d.V.obj.hom _ = _
  rw [hkey, ← pointsMap_comp_apply, ← d.comm, pointsMap_comp_apply]
  rfl

/-- On a commuting square of étale scheme charts, the inverse image along the vertical morphism of
schemes of the open subscheme that an open subspace `V ⊆ Y` cuts out in the chart of the target is
the open subscheme that `f⁻¹V` cuts out in the chart of the source.  This is what makes the
chartwise hypothesis `AlgebraicGeometry.Space.IsFinitePresentationOverOpenOnCharts` the chartwise
reading of finite presentation of the restriction of a module to `f⁻¹V`. -/
theorem preimage_chartOpenOfOpenSubspace {f : X ⟶ Y} (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) (hVf : IsOpenSubspace B S hS (V.preimage f))
    (d : ChartDiagram B S hS X Y f) :
    (BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ chartOpenOfOpenSubspace B S hS V hV d.V =
      chartOpenOfOpenSubspace B S hS (V.preimage f) hVf d.U := by
  ext u
  change pointOfEtaleChart B S hS d.V ((BigFppfOver.toScheme B S hS).map d.g u) ∈
      Set.range (pointsMap B S hS V.toFunctor V.ι) ↔
    pointOfEtaleChart B S hS d.U u ∈
      Set.range (pointsMap B S hS (V.preimage f).toFunctor (V.preimage f).ι)
  rw [range_pointsMap_preimage, pointOfEtaleChart_map_g]
  exact Iff.rfl

end ChartDiagramPoints

/-! ### The chartwise hypotheses and conclusion -/

section Chartwise

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An open subspace of an algebraic space is *retrocompact on charts* when the open subscheme it
cuts out in every étale scheme chart is retrocompact.  This is the chartwise form of
quasi-compactness of its inclusion, and is the hypothesis Stacks 081N takes at the scheme
level. -/
abbrev IsRetrocompactOnCharts (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) : Prop :=
  ∀ W : SmallEtale B S hS Y,
    IsRetrocompact (chartOpenOfOpenSubspace B S hS V hV W : Set (etaleChartScheme B S hS W))

/-- An open subspace of an algebraic space is *scheme-theoretically dense on charts* when the open
subscheme it cuts out in every étale scheme chart is scheme-theoretically dense in that chart, in
the sense of Tag 01RB. -/
abbrev IsSchemeTheoreticallyDenseOnCharts (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) : Prop :=
  ∀ W : SmallEtale B S hS Y,
    Scheme.Opens.IsSchemeTheoreticallyDense (chartOpenOfOpenSubspace B S hS V hV W)

/-- A module on the source of a morphism of algebraic spaces is *of finite presentation over an
open subspace `V` of the target, on charts* when, on every commuting square of étale scheme
charts, the restriction of the module to the inverse image of the chart-level `V` is of finite
presentation.  By `AlgebraicGeometry.Space.preimage_chartOpenOfOpenSubspace` that inverse image is
the chart-level `f⁻¹V`, so this is the chartwise reading of finite presentation of
`F|_{f⁻¹V}`. -/
abbrev IsFinitePresentationOverOpenOnCharts (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) : Prop :=
  ∀ d : ChartDiagram B S hS X Y f,
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ
        chartOpenOfOpenSubspace B S hS V hV d.V).ι).obj
      (chartModule B S hS hX F d.U)).IsFinitePresentation

/-- **A scheme-theoretically dense open subspace is scheme-theoretically dense on charts.**  The
space-level notion of Tag 0834 implies the chartwise one, so the hypothesis of Stacks 0876 may be
taken in the form the source states it.

By Tag 0836 -- more precisely by its two ingredients
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_forall_chart` and
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_preimage_eq_top_iff` -- density says
that the morphism of schemes representing `V ×_Y W` is scheme-theoretically dominant for every
étale scheme chart `W` of `Y`; over all charts at once that is injectivity of its structure-sheaf
map, by `AlgebraicGeometry.Space.forall_mono_c_iff_forall_isSchemeTheoreticallyDominant`, and for
an open immersion of schemes injectivity of the structure-sheaf map is scheme-theoretic density of
the image, Tag 01RE.  The image is the open subscheme that `V` cuts out in the chart, by
`AlgebraicGeometry.Space.opensRange_snd_eq_chartOpenOfOpenSubspace`. -/
theorem isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) (hdense : IsSchemeTheoreticallyDense B S hS V) :
    IsSchemeTheoreticallyDenseOnCharts B S hS V hV := by
  intro W
  have hdom : ∀ W' : SmallEtale B S hS Y, IsSchemeTheoreticallyDominant
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd W'.1.hom)) := fun W' =>
    (schemeTheoreticImageSubfunctor_preimage_eq_top_iff B S hS hV.2 W'.1.hom).mp
      ((isSchemeTheoreticallyDense_iff_forall_chart B S hS V).mp hdense W')
  have hoi : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd W.1.hom)) :=
    hV.2.property_snd W.1.hom
  rw [← opensRange_snd_eq_chartOpenOfOpenSubspace B S hS V hV W]
  exact (isSchemeTheoreticallyDense_opensRange_iff_mono _).mpr
    ((forall_mono_c_iff_forall_isSchemeTheoreticallyDominant B S hS hV.2).mpr hdom W)

/-- The image of a quasi-compact open immersion of schemes is retrocompact: its intersection
with a compact open is the image of the inverse image of that open, which is compact because the
morphism is quasi-compact. -/
@[ega "IV 1.2.7" "partial"]
private theorem isRetrocompact_opensRange_of_quasiCompact {A Z : Scheme.{u}} (g : A ⟶ Z)
    [AlgebraicGeometry.IsOpenImmersion g] [AlgebraicGeometry.QuasiCompact g] :
    IsRetrocompact (g.opensRange : Set Z) := by
  intro P hPcompact hPopen
  rw [Scheme.Hom.coe_opensRange, Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  exact (AlgebraicGeometry.QuasiCompact.isCompact_preimage P hPopen hPcompact).image
    (by fun_prop)

/-- **An open subspace whose inclusion is quasi-compact is retrocompact on charts.**  The
space-level notion of Tag 03HE implies the chartwise one, so the quasi-compactness half of
hypothesis (3) of Stacks 0876 may be taken in the form the source states it.

By Stacks 03HD, `AlgebraicGeometry.Space.presheaf_quasiCompact_of_isQuasiCompact`, a
quasi-compact representable morphism has quasi-compact represented base changes, so the morphism
of schemes representing `V ×_Y W` is quasi-compact for every étale scheme chart `W` of `Y`; its
image is retrocompact, and that image is the open subscheme that `V` cuts out in the chart, by
`AlgebraicGeometry.Space.opensRange_snd_eq_chartOpenOfOpenSubspace`. -/
theorem isRetrocompactOnCharts_of_isQuasiCompact (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V) (hVqc : IsQuasiCompact B S hS V.ι) :
    IsRetrocompactOnCharts B S hS V hV := by
  intro W
  have hoi : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd W.1.hom)) :=
    hV.2.property_snd W.1.hom
  have hQC : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd W.1.hom)) :=
    (presheaf_quasiCompact_of_isQuasiCompact B S hS hV.2.rep hVqc).property W.1.hom _ _
      (hV.2.rep.isPullback W.1.hom)
  rw [← opensRange_snd_eq_chartOpenOfOpenSubspace B S hS V hV W]
  exact isRetrocompact_opensRange_of_quasiCompact _

end Chartwise

/-! ### Stacks 0876 -/

section Main

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

open AlgebraicGeometry.FinitePresentationFromDenseOpen in
/-- **Stacks 0876, with hypothesis (3) read on the charts.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over a scheme `S` contained in a big fppf site `B` which is locally of finite
presentation, let `F` be an `𝒪_X`-module which is quasi-coherent of finite type on charts and
flat over `Y`, and let `V ⊆ Y` be an open subspace which is retrocompact and
scheme-theoretically dense on charts.  If `F` restricted to `f⁻¹V` is of finite presentation on
charts, then on every commuting square of étale scheme charts the restriction of `F` to the chart
of `X` is of finite presentation.

On one such square this is Stacks 081N for the vertical morphism of schemes, which is locally of
finite presentation because `f` is, with the open subscheme of the chart of `Y` cut out by `V` as
the retrocompact scheme-theoretically dense open of the base.

`AlgebraicGeometry.Space.isFinitePresentation_chartModule_of_isFlatOver_of_dense_open` is the
same statement with hypothesis (3) in the form the source states it; this version is the one to
apply when the chartwise conditions are what is known. -/
theorem isFinitePresentation_chartModule_of_isFlatOver_of_dense_open_charts
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hflat : IsFlatOver B S hS hX f F)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVretro : IsRetrocompactOnCharts B S hS V hV)
    (hVdense : IsSchemeTheoreticallyDenseOnCharts B S hS V hV)
    (hfp : IsFinitePresentationOverOpenOnCharts B S hS hX f F V hV)
    (d : ChartDiagram B S hS X Y f) :
    (chartModule B S hS hX F d.U).IsFinitePresentation := by
  have := hqc d.U
  have := hft d.U
  have := locallyOfFinitePresentation_chartDiagram B S hS hf d
  exact isFinitePresentation_of_isFlatOver_of_retrocompact_dense_open
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS hX F d.U) (hflat d)
    (chartOpenOfOpenSubspace B S hS V hV d.V) (hVretro d.V) (hVdense d.V) (hfp d)

/-- **Stacks 0876.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B` which is locally of finite presentation, let `F` be an
`𝒪_X`-module which is quasi-coherent of finite type on charts and flat over `Y`, and let `V ⊆ Y`
be an open subspace whose inclusion is quasi-compact and which is scheme-theoretically dense in
the sense of Tag 0834.  If `F` restricted to `f⁻¹V` is of finite presentation on charts, then on
every commuting square of étale scheme charts the restriction of `F` to the chart of `X` is of
finite presentation.

Hypothesis (3) of the source is exactly the two hypotheses `hVqc` and `hVdense` here.  They give
the chartwise conditions of
`AlgebraicGeometry.Space.isFinitePresentation_chartModule_of_isFlatOver_of_dense_open_charts` by
`AlgebraicGeometry.Space.isRetrocompactOnCharts_of_isQuasiCompact` (Stacks 03HD) and
`AlgebraicGeometry.Space.isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense`
(Stacks 0836), and on one commuting square of charts the statement is then Stacks 081N for the
vertical morphism of schemes. -/
@[stacks 0876 "hypotheses (1) and (2) and the conclusion are read on the etale scheme charts: \
they are the corresponding properties of the restriction of the module to the charts, as for \
Space.IsFlatOver of Tag 05VV. Hypothesis (4) is read on the open subscheme that V cuts out in \
each chart of the target, which by Space.preimage_chartOpenOfOpenSubspace is the chart-level \
inverse image of V. The conclusion is stated on a commuting square of charts of f rather than \
on an arbitrary chart of the source, since not every chart of the source is the source of such \
a square"]
theorem isFinitePresentation_chartModule_of_isFlatOver_of_dense_open
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hflat : IsFlatOver B S hS hX f F)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompact B S hS V.ι)
    (hVdense : IsSchemeTheoreticallyDense B S hS V)
    (hfp : IsFinitePresentationOverOpenOnCharts B S hS hX f F V hV)
    (d : ChartDiagram B S hS X Y f) :
    (chartModule B S hS hX F d.U).IsFinitePresentation :=
  isFinitePresentation_chartModule_of_isFlatOver_of_dense_open_charts B S hS hX F hf hqc hft
    hflat V hV (isRetrocompactOnCharts_of_isQuasiCompact B S hS V hV hVqc)
    (isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense B S hS V hV hVdense) hfp d

end Main

end AlgebraicGeometry.Space

end
