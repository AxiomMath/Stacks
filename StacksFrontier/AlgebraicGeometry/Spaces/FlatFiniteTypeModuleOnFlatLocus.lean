module

public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.ModuleFlatLocusFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# Stacks 0DLR: the module on the relative flat locus

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation, let `F` be a quasi-coherent `𝒪_X`-module of finite type and
assume the weakly associated points of `Y` are locally finite.  Stacks 0DLR asserts that the
locus `U = {x ∈ |X| : F flat at x over Y}` is open and that `F|_U` is an `𝒪_U`-module of finite
presentation and flat over `Y`.  As printed, with the weakly associated points locally finite in
`|Y|`, this is false (a counterexample has a target which is not decent); see the
implementation notes.

The locus `U` is `AlgebraicGeometry.Space.flatLocus` and its openness is
`AlgebraicGeometry.Space.isOpen_flatLocus`, both in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean`.  This file carries the
two assertions about the module on `U`, stated about `F|_U` as a module on the open subspace `U`
itself: `U` is an algebraic space over `S` by the open-subspace half of the tag, `F|_U` is the
inverse image of `F` of Stacks 03LU along the open immersion `U ⟶ X`, and the two conclusions are
finite presentation of that module and its flatness over `Y` along the composite `U ⟶ X ⟶ Y` in
the sense of Tag 05VV.  Both are read on the étale scheme charts of `U`, as every property of a
module on an algebraic space is in this development.

What makes that possible is the identification of the restriction of `F|_U` to a chart of `U`
with the restriction of `F` to the same chart read as a chart of `X`,
`AlgebraicGeometry.Space.restrictToChartEtaleSourceIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceChartRestriction.lean`, together with
Stacks 05VU: a chart of `U` has every point of its scheme in the relative flat locus, by
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleFibre.lean`, so the scheme-level
theorem Stacks 05IK applies to the whole of that scheme and not merely to an open part of it.

## Main definitions

* `AlgebraicGeometry.Space.flatLocusSpace`, `AlgebraicGeometry.Space.flatLocusSpaceι` and
  `AlgebraicGeometry.Space.flatLocusRestrict`: the locus `U` as an algebraic space, its open
  immersion into `X`, and the module `F|_U`.  Each takes the open-subspace half of Stacks 0DLR
  itself, rather than the conditions on `f` and `F` from which it follows, so that no reading of
  those conditions is built into the objects.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentationOnCharts_flatLocusRestrict` and
  `AlgebraicGeometry.Space.isFlatOver_flatLocusRestrict`: **the two assertions of Stacks 0DLR
  about the module on `U`**, that `F|_U` is an `𝒪_U`-module of finite presentation and that it is
  flat over `Y`.  Both are stated at the correction of the source recorded in `errata.md`:
  condition (3) is read on one surjective étale scheme chart of the target, as the source's proof
  reads it, since on `|Y|` the statement is false; the every-chart
  reading the finite presentation proof consumes is derived from it by
  `AlgebraicGeometry.Space.hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart`.
* `AlgebraicGeometry.Space.isOpen_preimage_flatLocus`: the preimage of `U` in a source chart is
  open, being the relative flat locus of that chart by Stacks 05VU.
* `AlgebraicGeometry.Space.isFinitePresentation_restrict_preimage_flatLocus` and
  `AlgebraicGeometry.Space.isFlatOver_restrict_preimage_flatLocus`: the same two assertions read
  on a chart of `X`, the module being restricted to the preimage of `U` there.

## Implementation notes

The conditions on the module are the source's own, read on the small étale site:
quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, which is what Stacks 05VU consumes
through Stacks 05VP, and finite type is `SheafOfModules.IsFiniteTypeOnSite`.  The chartwise
readings that the scheme-level theorem Stacks 05IK consumes are *derived* from those, by
`AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionFromSite.lean`, so neither is asked for
here.

The source's condition (3) is that the weakly associated points of `Y` be locally finite in `|Y|`,
and the proof of Stacks 0DLR reads it on one *surjective* étale scheme chart of `Y`.  The two
readings can differ when `Y` is not decent, and with the first the statement is false
(`Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus`); the two
assertions here use the second, which is the correction recorded in `errata.md`.  Their proofs
consume the reading on *every* étale scheme chart,
`AlgebraicGeometry.Space.HasLocallyFiniteWeaklyAssociatedPointsOnCharts`, which is a priori
stronger; the two readings agree unconditionally by
`AlgebraicGeometry.Space.hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart` of
`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedLocallyFiniteCharts.lean`, so the
every-chart reading is not an added condition.

The finite presentation assertion needs one further step that the flatness assertion does not.
Flatness over `Y` is a condition on one commuting square of charts at a time, and every square of
charts of `U ⟶ Y` pushes forward to a square of charts of `f`; finite presentation of the chart
restriction is a condition on a chart alone, and a chart of `U` admitting no square over `Y` is
reached by étale descent instead — the condition is read on one chart surjective on points,
chosen to lie over a chart of `Y` by Tag 02X1, and propagated to every chart by
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChartScheme_of_isSurjective` of
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationEtaleChart.lean`.  This is the source's
own "the question is étale local on `X` and `Y`".

The two open sets the module is restricted to in the chartwise forms are the same set, so no new
identification of loci is introduced for them: the equality of the chart's flat locus with the
preimage of `U` is `AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus`, used
pointwise.

The module universe is the universe of the structure rings, as it must be for
`AlgebraicGeometry.Space.restrictToChart` to land in `AlgebraicGeometry.Scheme.Modules` of the
chart.

## References

* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Xs Ys : AlgebraicSpaces B S hS}

/-! ### The preimage of the relative flat locus in a chart -/

/-- The preimage of the relative flat locus `U = {x ∈ |X| : F flat at x over Y}` in an étale
scheme chart of the source is open: by Stacks 05VU it is the relative flat locus of that chart,
which is open by the chartwise half of Stacks 0DLR. -/
theorem isOpen_preimage_flatLocus (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Ys.1)
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) :
    IsOpen (pointOfEtaleChart B S hS d.U ⁻¹' flatLocus B S hS Xs.2 f.hom F) := by
  have heq : pointOfEtaleChart B S hS d.U ⁻¹' flatLocus B S hS Xs.2 f.hom F =
      chartFlatLocus B S hS Xs.2 F d :=
    Set.ext fun u => (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).symm
  rw [heq]
  exact isOpen_chartFlatLocus B S hS Xs.2 F hf
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS Xs F hqc)
    (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS Xs F hqc hft) hwa d

/-! ### The module on the relative flat locus -/

/-- The restriction of the module on a chart to an open set of points lying over the relative flat
locus is of finite presentation. -/
private theorem isFinitePresentation_restrict_chartModule_of_mem_flatLocus (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Ys.1)
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) (Z : (etaleChartScheme B S hS d.U).Opens)
    (hZ : ∀ u ∈ Z, pointOfEtaleChart B S hS d.U u ∈ flatLocus B S hS Xs.2 f.hom F) :
    ((chartModule B S hS Xs.2 F d.U).restrict Z.ι).IsFinitePresentation := by
  have := locallyOfFinitePresentation_chartDiagram B S hS hf d
  have := isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS Xs F hqc d.U
  have := isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS Xs F hqc hft d.U
  exact _root_.AlgebraicGeometry.isFinitePresentation_restrict_of_subset_flatLocus
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS Xs.2 F d.U) (hwa d.V)
    _ fun u hu => (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).2 (hZ u hu)

/-- **The finite presentation assertion of Stacks 0DLR, read on a chart of the source.** On a
commuting square of étale scheme charts of `f`, the restriction of the module to the source
chart, restricted further to the preimage of the relative flat locus
`U = {x ∈ |X| : F flat at x over Y}`, is of finite presentation.

That the open set restricted to is cut out by `U` and not by the chart is Stacks 05VU, through
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus`.  The tag's own
assertion, about `F|_U` as a module on the open subspace `U` itself, is
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_flatLocusRestrict` below. -/
theorem isFinitePresentation_restrict_preimage_flatLocus (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Ys.1)
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) :
    letI Z : (etaleChartScheme B S hS d.U).Opens :=
      ⟨pointOfEtaleChart B S hS d.U ⁻¹' flatLocus B S hS Xs.2 f.hom F,
        isOpen_preimage_flatLocus B S hS f F hf hft hwa d⟩
    ((chartModule B S hS Xs.2 F d.U).restrict Z.ι).IsFinitePresentation :=
  isFinitePresentation_restrict_chartModule_of_mem_flatLocus B S hS f F hf hft hwa d _
    fun _ hu => hu

/-- **The flatness assertion of Stacks 0DLR, read on a chart of the source.** On a commuting
square of étale scheme charts of `f`, the restriction of the module to the source chart,
restricted further to the preimage of the relative flat locus
`U = {x ∈ |X| : F flat at x over Y}`, is flat over the target chart.

That the open set restricted to is cut out by `U` and not by the chart is Stacks 05VU, through
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus`.  The tag's own
assertion, about `F|_U` as a module on the open subspace `U` itself, is
`AlgebraicGeometry.Space.isFlatOver_flatLocusRestrict` below. -/
theorem isFlatOver_restrict_preimage_flatLocus (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Ys.1)
    (d : ChartDiagram B S hS Xs.1 Ys.1 f.hom) :
    letI Z : (etaleChartScheme B S hS d.U).Opens :=
      ⟨pointOfEtaleChart B S hS d.U ⁻¹' flatLocus B S hS Xs.2 f.hom F,
        isOpen_preimage_flatLocus B S hS f F hf hft hwa d⟩
    _root_.AlgebraicGeometry.IsFlatOver
      (Z.ι ≫ (BigFppfOver.toScheme B S hS).map d.g).toLRSHom.toShHom
      ((chartModule B S hS Xs.2 F d.U).restrict Z.ι) :=
  _root_.AlgebraicGeometry.isFlatOver_restrict_of_subset_flatLocus
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS Xs.2 F d.U) _
    fun u hu => (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).2 hu

/-! ### The module on the open subspace cut out by the relative flat locus -/

/-- The relative flat locus `U = {x ∈ |X| : F flat at x over Y}`, as an algebraic space over `S`.
The subfunctor it cuts out is an open subspace of `X` in the sense of Tag 03BZ by the
open-subspace half of Stacks 0DLR, and that fact is the argument `hopen`.

Taking the open-subspace half itself, rather than the conditions on `f` and `F` from which it
follows, keeps those conditions out of the definitional chain: `hopen` is a proposition, so by
proof irrelevance the space is the same whichever route proves it, and a caller may prove it at
the source's own reading of condition (3) by
`AlgebraicGeometry.Space.isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart`. -/
noncomputable abbrev flatLocusSpace (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F)) :
    AlgebraicSpaces B S hS :=
  ⟨(flatLocusOpenSubspace B S hS Xs.2 f.hom F).toFunctor, hopen.1⟩

/-- The open immersion `U ⟶ X` of the relative flat locus into the source. -/
noncomputable abbrev flatLocusSpaceι (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F)) :
    flatLocusSpace B S hS f F hopen ⟶ Xs :=
  ObjectProperty.homMk (flatLocusOpenSubspace B S hS Xs.2 f.hom F).ι

/-- The module `F|_U` on the relative flat locus: the inverse image of `F` of Stacks 03LU along
the open immersion `U ⟶ X`. -/
noncomputable abbrev flatLocusRestrict (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F)) :
    Modules.{u, u} B S hS (flatLocusSpace B S hS f F hopen).1
      (flatLocusSpace B S hS f F hopen).2 :=
  (modulePullback B S hS (flatLocusSpaceι B S hS f F hopen)).obj F

/-- The open immersion of the relative flat locus into the source is étale. -/
theorem isEtale_flatLocusSpaceι (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F)) :
    IsEtale B S hS (flatLocusSpaceι B S hS f F hopen).hom :=
  isEtale_ι_of_isOpenSubspace hopen

/-- Every point of a chart of the relative flat locus, read as a chart of the source, lies in
the locus. -/
theorem mem_flatLocus_pointOfEtaleChart_chartOfEtaleSource (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    (hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F))
    (W : SmallEtale B S hS (flatLocusSpace B S hS f F hopen).1)
    (w : etaleChartScheme B S hS W) :
    pointOfEtaleChart B S hS
        (chartOfEtaleSource B S hS (isEtale_flatLocusSpaceι B S hS f F hopen) W) w ∈
      flatLocus B S hS Xs.2 f.hom F := by
  rw [pointOfEtaleChart_chartOfEtaleSource B S hS
      (isEtale_flatLocusSpaceι B S hS f F hopen) W w,
    ← range_pointsMap_flatLocusOpenSubspace B S hS Xs.2 f.hom F]
  exact Set.mem_range_self _

/-- **The restriction of `F` to a chart of the relative flat locus carrying a commuting square of
étale scheme charts over `Y` is of finite presentation.**  The chart, read as a chart of `X`, has
every point of its scheme in the relative flat locus, so the scheme-level theorem Stacks 05IK
applies to the whole of that scheme. -/
theorem isFinitePresentation_restrictToChart_flatLocusRestrict_chartDiagram (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Ys.1)
    (hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F))
    (d : ChartDiagram B S hS (flatLocusSpace B S hS f F hopen).1 Ys.1
      ((flatLocusSpaceι B S hS f F hopen).hom ≫ f.hom)) :
    (restrictToChart B S hS (flatLocusSpace B S hS f F hopen).2
      (flatLocusRestrict B S hS f F hopen) d.U).IsFinitePresentation := by
  set d' := chartDiagramOfEtaleSource B S hS
    (isEtale_flatLocusSpaceι B S hS f F hopen) f d with hd'
  have := isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS Xs F hqc d'.U
  exact SheafOfModules.IsFinitePresentation.of_iso
    (_root_.AlgebraicGeometry.isFinitePresentation_of_restrict_top
      (chartModule B S hS Xs.2 F d'.U)
      (isFinitePresentation_restrict_chartModule_of_mem_flatLocus B S hS f F hf hft hwa d' ⊤
        fun _ _ => mem_flatLocus_pointOfEtaleChart_chartOfEtaleSource B S hS f F hopen d.U _))
    (restrictToChartEtaleSourceIso B S hS
      (isEtale_flatLocusSpaceι B S hS f F hopen) F hqc d.U)

/-- **Stacks 0DLR: `F|_U` is an `𝒪_U`-module of finite presentation.**  For a morphism of
algebraic spaces locally of finite presentation, a module quasi-coherent of finite type on the
small étale site and a target whose weakly associated points are locally finite on the scheme of
one surjective étale chart, the module `F|_U` on the open subspace
`U = {x ∈ |X| : F flat at x over Y}` is of finite presentation.

Conditions (1) and (2) are the source's own; condition (3), local finiteness of the weakly
associated points of `Y` in `|Y|`, is replaced by local finiteness on one *surjective* étale
scheme chart, as the source's proof reads it.  This is the correction of Stacks 0DLR recorded in
`errata.md`: with (3) on `|Y|` the statement is false,
`Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus`.
The every-chart reading the proof consumes is derived from it by
`AlgebraicGeometry.Space.hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart`.

The conclusion is read on the étale scheme charts of `U`, as every property of a module on an
algebraic space is in this development.  The proof is the source's: the condition is étale local,
so it is enough to read it on one chart of `U` surjective on points, and such a chart may be
chosen to lie over a chart of `Y` (Tag 02X1), where the scheme-level theorem Stacks 05IK applies;
the passage back to every chart is
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChartScheme_of_isSurjective`. -/
@[stacks 0DLR "F|_U is an O_U-module of finite presentation, for U the open subspace cut out by \
the flat locus, at the Stacks erratum: condition (3) of the source, local finiteness of the weakly \
associated points of Y in |Y|, is replaced by local finiteness of the weakly associated points of \
the scheme of one surjective etale chart of Y, which is how the source's proof reads it and which \
implies (3). The tag as published, with (3) on |Y|, is false, refuted (with a target which is not \
decent) by the theorem \
Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus of \
StacksFrontier/Examples/Flatness/NonOpenFlatLocusWeaklyAssociated.lean. The module is quasi-coherent \
of finite type on the small etale site; the conclusion is read on the etale scheme charts of U, as \
every property of a module on an algebraic space is in this development"]
theorem isFinitePresentationOnCharts_flatLocusRestrict (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [hqc : F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (V₀ : SmallEtale B S hS Ys.1)
    (hV₀ : IsSurjectiveChart B S hS V₀)
    (h₀ : ∀ v : etaleChartScheme B S hS V₀,
      ∃ W : (etaleChartScheme B S hS V₀).Opens, v ∈ W ∧
        (Stacks.Divisors.schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V₀) ∩
          (W : Set (etaleChartScheme B S hS V₀))).Finite) :
    IsFinitePresentationOnCharts B S hS
      (flatLocusSpace B S hS f F
        (isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart B S hS Xs f.hom F hf hqc hft
          V₀ hV₀ h₀)).2
      (flatLocusRestrict B S hS f F
        (isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart B S hS Xs f.hom F hf hqc hft
          V₀ hV₀ h₀)) := by
  have hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F) :=
    isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart B S hS Xs f.hom F hf hqc hft
      V₀ hV₀ h₀
  have hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Ys.1 :=
    hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart B S hS V₀ hV₀ h₀
  change IsFinitePresentationOnCharts B S hS (flatLocusSpace B S hS f F hopen).2
    (flatLocusRestrict B S hS f F hopen)
  have hMqc : (flatLocusRestrict B S hS f F hopen).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F hqc
  obtain ⟨V, hVsurj⟩ := exists_surjective_smallEtale_chart B S hS Ys.1 Ys.2
  obtain ⟨U₀, p, α, hsq, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hopen.1 Ys.2
      ((flatLocusSpaceι B S hS f F hopen).hom ≫ f.hom) V.1.left V.1.hom
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Ys.1 Ys.2 V.1.left V.1.hom).2 hVsurj)
      V.property
  set A : SmallEtale B S hS (flatLocusSpace B S hS f F hopen).1 :=
    ⟨CostructuredArrow.mk p, hpEtale⟩ with hA
  have hAsurj : IsSurjective B S hS A.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS
      (flatLocusOpenSubspace B S hS Xs.2 f.hom F).toFunctor hopen.1 U₀ p).1 hpSurj
  have hAfp : (restrictToChart B S hS (flatLocusSpace B S hS f F hopen).2
      (flatLocusRestrict B S hS f F hopen) A).IsFinitePresentation :=
    isFinitePresentation_restrictToChart_flatLocusRestrict_chartDiagram B S hS f F hf hft hwa
      hopen ⟨A, V, α, hsq⟩
  intro A'
  exact SheafOfModules.IsFinitePresentation.of_iso
    (isFinitePresentation_restrictToChartScheme_of_isSurjective B S hS _
      (flatLocusSpace B S hS f F hopen).2
      (flatLocusRestrict B S hS f F hopen) hMqc A hAsurj
      (SheafOfModules.IsFinitePresentation.of_iso hAfp
        (restrictToChartIsoRestrictToChartScheme B S hS _ _ A)) A')
    (restrictToChartIsoRestrictToChartScheme B S hS _ _ A').symm

/-- **Stacks 0DLR: `F|_U` is flat over `Y`.**  For a morphism of algebraic spaces locally of
finite presentation, a module quasi-coherent of finite type on the small étale site and a target
whose weakly associated points are locally finite on the scheme of one surjective étale chart,
the module `F|_U` on the open subspace `U = {x ∈ |X| : F flat at x over Y}` is flat over `Y` along
the composite `U ⟶ X ⟶ Y`, in the sense of Tag 05VV.

Conditions (1) and (2) are the source's own; condition (3) is replaced by local finiteness of the
weakly associated points on one *surjective* étale scheme chart of the target, as the source's
proof reads it, which is the correction of Stacks 0DLR recorded in `errata.md` (with (3) on `|Y|`
the statement is false,
`Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus`).

On a commuting square of étale scheme charts of `U ⟶ Y`, the chart of `U` is a chart of `X` whose
points all lie in the relative flat locus, so the square witnesses flatness at each of them by
Stacks 05VU. -/
@[stacks 0DLR "F|_U is flat over Y along the composite U -> X -> Y, for U the open subspace cut \
out by the flat locus, at the Stacks erratum: condition (3) of the source, local finiteness of the \
weakly associated points of Y in |Y|, is replaced by local finiteness of the weakly associated \
points of the scheme of one surjective etale chart of Y, which is how the source's proof reads it \
and which implies (3). The tag as published, with (3) on |Y|, is false, refuted (with a target \
which is not decent) by the theorem \
Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus of \
StacksFrontier/Examples/Flatness/NonOpenFlatLocusWeaklyAssociated.lean. Flatness of a module on an \
algebraic space over the target is Tag 05VV, read on the commuting squares of etale scheme charts"]
theorem isFlatOver_flatLocusRestrict (f : Xs ⟶ Ys) (F : Modules.{u, u} B S hS Xs.1 Xs.2)
    [hqc : F.IsQuasicoherentOnSite] (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (V₀ : SmallEtale B S hS Ys.1)
    (hV₀ : IsSurjectiveChart B S hS V₀)
    (h₀ : ∀ v : etaleChartScheme B S hS V₀,
      ∃ W : (etaleChartScheme B S hS V₀).Opens, v ∈ W ∧
        (Stacks.Divisors.schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V₀) ∩
          (W : Set (etaleChartScheme B S hS V₀))).Finite) :
    IsFlatOver B S hS
      (flatLocusSpace B S hS f F
        (isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart B S hS Xs f.hom F hf hqc hft
          V₀ hV₀ h₀)).2
      ((flatLocusSpaceι B S hS f F
        (isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart B S hS Xs f.hom F hf hqc hft
          V₀ hV₀ h₀)).hom ≫ f.hom)
      (flatLocusRestrict B S hS f F
        (isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart B S hS Xs f.hom F hf hqc hft
          V₀ hV₀ h₀)) := by
  have hopen : IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS Xs.2 f.hom F) :=
    isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart B S hS Xs f.hom F hf hqc hft
      V₀ hV₀ h₀
  change IsFlatOver B S hS (flatLocusSpace B S hS f F hopen).2
    ((flatLocusSpaceι B S hS f F hopen).hom ≫ f.hom) (flatLocusRestrict B S hS f F hopen)
  intro d u
  refine (_root_.AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _
    (restrictToChartEtaleSourceIso B S hS
      (isEtale_flatLocusSpaceι B S hS f F hopen) F hqc d.U) u).1 ?_
  exact (isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F
      (chartDiagramOfEtaleSource B S hS
        (isEtale_flatLocusSpaceι B S hS f F hopen) f d) u).2
    (mem_flatLocus_pointOfEtaleChart_chartOfEtaleSource B S hS f F hopen d.U u)

end AlgebraicGeometry.Space

end
