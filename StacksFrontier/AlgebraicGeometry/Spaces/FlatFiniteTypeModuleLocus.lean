module

public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.ModuleFlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The relative flat locus of a finite type module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which
is locally of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module of finite type.
If the weakly associated points of `Y` are locally finite, then the locus `U` of points of `X`
at which `F` is flat over `Y` is open, and on `U` the module is of finite presentation and flat
over `Y`. This is Stacks 0DLR.

The locus is the union of the images of the flat loci of the commuting squares of étale scheme
charts of `f`, each of which is open by the scheme-level theorem Stacks 05IK
(`AlgebraicGeometry.isOpen_flatLocus`).

## Main definitions

* `AlgebraicGeometry.Space.pointOfEtaleChart` is the point of `X` determined by a point of an étale
  scheme chart of `X`.
* `AlgebraicGeometry.Space.chartModule` is the restriction of an `𝒪_X`-module to an étale
  scheme chart, read as a module on that scheme.
* `AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
  `AlgebraicGeometry.Space.IsFiniteTypeOnCharts` are the chartwise forms of quasi-coherence and
  of finite type, and
  `AlgebraicGeometry.Space.HasLocallyFiniteWeaklyAssociatedPointsOnCharts` the chartwise form
  of local finiteness of the weakly associated points.
* `AlgebraicGeometry.Space.chartFlatLocus` is the relative flat locus on one commuting square
  of étale scheme charts, and `AlgebraicGeometry.Space.flatLocus` the relative flat locus in
  the point space of `X`.
* `AlgebraicGeometry.Space.flatLocusOpenSubspace` is the subfunctor of `X` it cuts out.

## Main results

* `AlgebraicGeometry.Space.isOpen_flatLocus`: the relative flat locus is open in the point space
  of `X`.
* `AlgebraicGeometry.Space.isOpenSubspace_flatLocusOpenSubspace`: the relative flat locus cuts
  out an open subspace of `X`, whose point set is the locus by
  `AlgebraicGeometry.Space.range_pointsMap_flatLocusOpenSubspace`.
* `AlgebraicGeometry.Space.isFinitePresentation_restrict_chartFlatLocus` and
  `AlgebraicGeometry.Space.isFlatOver_restrict_chartFlatLocus`: on the flat locus of a commuting
  square of étale scheme charts, the restricted module is of finite presentation and flat over
  the target chart.
* `AlgebraicGeometry.Space.isOpen_chartFlatLocus`: the flat locus of a commuting square of étale
  scheme charts is open.
* `AlgebraicGeometry.Space.exists_chartDiagram_pointOfEtaleChart`: every point of `X` lies in
  the image of the source chart of some commuting square of étale scheme charts.

## Implementation notes

A module on an algebraic space is compared with a module on a scheme only through
`AlgebraicGeometry.Space.restrictToChart`, so the hypotheses on `F` and on the weakly associated
points of `Y` are taken chartwise, as `AlgebraicGeometry.Space.IsFlatOver` takes flatness. The
chartwise condition on `Y` follows from the condition on one surjective étale chart by
`AlgebraicGeometry.Space.hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart`.

The relative flat locus is the existential condition of clause (1) of Tag 05VU: some commuting
square of étale scheme charts through the point witnesses flatness. Its independence of the
chosen square needs `F` to be quasi-coherent on the small étale site, which is not assumed here,
so the assertions about the module are stated on the flat locus of a single square.

The module universe is the universe of the structure rings, as it must be for
`AlgebraicGeometry.Space.restrictToChart` to land in `AlgebraicGeometry.Scheme.Modules` of the
chart. `AlgebraicGeometry.Space.pointTopology` is made a local instance.

## References

* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of an étale scheme chart -/

/-- The point of an algebraic space determined by a point of one of its étale scheme charts. -/
noncomputable def pointOfEtaleChart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS X)
    (u : etaleChartScheme B S hS U) : points B S hS X :=
  pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
    ((pointsEquivScheme B S hS U.obj.left).symm u)

/-- The image of an open set of an étale scheme chart is open in the point space: an étale chart
is an open map on points, by Tag 03BX. -/
theorem isOpen_image_pointOfEtaleChart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS X) {Z : Set (etaleChartScheme B S hS U)} (hZ : IsOpen Z) :
    IsOpen (pointOfEtaleChart B S hS U '' Z) := by
  have himg : pointOfEtaleChart B S hS U '' Z =
      pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom ''
        ((schemePointsHomeomorph B S hS U.obj.left).symm '' Z) := by
    rw [Set.image_image]
    rfl
  rw [himg]
  exact isOpenMap_pointsMap_of_presheafEtale B S hS U.obj.hom U.property _
    ((schemePointsHomeomorph B S hS U.obj.left).symm.isOpenMap _ hZ)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Every point of the source of a morphism of algebraic spaces is the image of a point of the
source chart of some commuting square of étale scheme charts. -/
theorem exists_chartDiagram_pointOfEtaleChart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X) :
    ∃ (d : ChartDiagram B S hS X Y f) (u : etaleChartScheme B S hS d.U),
      pointOfEtaleChart B S hS d.U u = x := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hX hY f x
  refine ⟨{ U := ⟨CostructuredArrow.mk c.a, c.a_etale⟩
            V := ⟨CostructuredArrow.mk c.b, c.b_etale⟩
            g := c.h
            comm := c.comm.symm }, schemePoint B S hS c.U c.representative, ?_⟩
  have hsymm : (pointsEquivScheme B S hS c.U).symm (schemePoint B S hS c.U c.representative) =
      c.representative.class B S hS (yoneda.obj c.U) :=
    (Equiv.symm_apply_eq _).mpr (pointsToScheme_class B S hS c.U c.representative).symm
  exact (congrArg (pointsMap B S hS (yoneda.obj c.U) c.a) hsymm).trans c.maps_to

/-! ### The chartwise hypotheses -/

/-- The restriction of a module on an algebraic space to an étale scheme chart, read as a
module on that scheme. -/
noncomputable abbrev chartModule (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) (U : SmallEtale B S hS X) :
    (etaleChartScheme B S hS U).Modules :=
  restrictToChart B S hS hX F U

/-- A module on an algebraic space is *quasi-coherent on charts* when its restriction to every
étale scheme chart is a quasi-coherent module on that scheme. -/
abbrev IsQuasicoherentOnCharts (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) : Prop :=
  ∀ U : SmallEtale B S hS X, (chartModule B S hS hX F U).IsQuasicoherent

/-- A module on an algebraic space is *of finite type on charts* when its restriction to every
étale scheme chart is a module of finite type on that scheme. -/
abbrev IsFiniteTypeOnCharts (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) : Prop :=
  ∀ U : SmallEtale B S hS X, (chartModule B S hS hX F U).IsFiniteType

/-- An algebraic space has *locally finite weakly associated points on charts* when the weakly
associated points of every étale scheme chart form a locally finite subset of that scheme. -/
abbrev HasLocallyFiniteWeaklyAssociatedPointsOnCharts
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (V : SmallEtale B S hS Y) (v : etaleChartScheme B S hS V),
    ∃ W : (etaleChartScheme B S hS V).Opens, v ∈ W ∧
      (schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V) ∩
        (W : Set (etaleChartScheme B S hS V))).Finite

/-! ### The flat locus -/

/-- The relative flat locus of a module on one commuting square of étale scheme charts: the
set of points of the source chart at which the restricted module is flat over the target
chart. -/
noncomputable abbrev chartFlatLocus (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f) :
    Set (etaleChartScheme B S hS d.U) :=
  _root_.AlgebraicGeometry.flatLocus ((BigFppfOver.toScheme B S hS).map d.g)
    (chartModule B S hS hX F d.U)

/-- Flatness over the target on a commuting square of étale scheme charts is flatness at every
point of the source chart. -/
theorem isFlatOverOnChartDiagram_iff (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f) :
    IsFlatOverOnChartDiagram B S hS hX F d ↔
      ∀ u : etaleChartScheme B S hS d.U, u ∈ chartFlatLocus B S hS hX F d :=
  Iff.rfl

/-- The scheme morphism of a commuting square of étale scheme charts of a morphism locally of
finite presentation is locally of finite presentation. -/
theorem locallyOfFinitePresentation_chartDiagram {f : X ⟶ Y}
    (hf : IsLocallyOfFinitePresentation B S hS f) (d : ChartDiagram B S hS X Y f) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map d.g) :=
  hf d.U.obj.left d.V.obj.left d.U.obj.hom d.V.obj.hom d.g d.U.property d.V.property
    d.comm.symm

/-- On a commuting square of étale scheme charts of a morphism locally of finite presentation,
the relative flat locus of a module which is quasi-coherent of finite type on charts is open,
provided the weakly associated points of the target are locally finite on charts. -/
theorem isOpen_chartFlatLocus (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y)
    (d : ChartDiagram B S hS X Y f) :
    IsOpen (chartFlatLocus B S hS hX F d) := by
  have := locallyOfFinitePresentation_chartDiagram B S hS hf d
  have := hqc d.U
  have := hft d.U
  exact _root_.AlgebraicGeometry.isOpen_flatLocus
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS hX F d.U) (hwa d.V)

/-- The relative flat locus of a module on an algebraic space: the set of points `x` of the
source such that some commuting square of étale scheme charts through `x` witnesses flatness of
the restricted module over the target chart. -/
@[stacks 0DLR "the locus U of the statement: the points of the source at which the module is \
flat over the target, which is Tag 05VV (1), i.e. clause (1) of Tag 05VU"]
noncomputable def flatLocus (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) : Set (points B S hS X) :=
  {x | ∃ (d : ChartDiagram B S hS X Y f) (u : etaleChartScheme B S hS d.U),
    pointOfEtaleChart B S hS d.U u = x ∧ u ∈ chartFlatLocus B S hS hX F d}

/-- The relative flat locus is the union, over the commuting squares of étale scheme charts, of
the images of their flat loci. -/
theorem flatLocus_eq_iUnion_image (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) :
    flatLocus B S hS hX f F =
      ⋃ d : ChartDiagram B S hS X Y f,
        pointOfEtaleChart B S hS d.U '' chartFlatLocus B S hS hX F d := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · rintro ⟨d, u, rfl, hu⟩
    exact Set.mem_iUnion.mpr ⟨d, u, hu, rfl⟩
  · intro hx
    obtain ⟨d, u, hu, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨d, u, rfl, hu⟩

/-- The flat locus of a chart is carried into the relative flat locus. -/
theorem chartFlatLocus_subset_preimage_flatLocus (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f) :
    chartFlatLocus B S hS hX F d ⊆
      pointOfEtaleChart B S hS d.U ⁻¹' flatLocus B S hS hX f F :=
  fun u hu => ⟨d, u, rfl, hu⟩

/-- For a morphism of algebraic spaces locally of finite presentation and a module which is
quasi-coherent of finite type on charts, the relative flat locus is open in the point space of
the source, provided the weakly associated points of the target are locally finite on charts. -/
theorem isOpen_flatLocus (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y) :
    IsOpen (flatLocus B S hS hX f F) := by
  rw [flatLocus_eq_iUnion_image]
  exact isOpen_iUnion fun d => isOpen_image_pointOfEtaleChart B S hS d.U
    (isOpen_chartFlatLocus B S hS hX F hf hqc hft hwa d)

/-- The subfunctor of the source cut out by the relative flat locus. -/
noncomputable def flatLocusOpenSubspace (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) : Subfunctor X :=
  openSubspaceOfPoints B S hS X (flatLocus B S hS hX f F)

/-- Under the hypotheses of `AlgebraicGeometry.Space.isOpen_flatLocus`, the relative flat locus
cuts out an open subspace of the source, in the sense of Tag 03BZ. -/
theorem isOpenSubspace_flatLocusOpenSubspace (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y) :
    IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS hX f F) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX _
    (isOpen_flatLocus B S hS hX f F hf hqc hft hwa)

/-- The point set of the open subspace cut out by the relative flat locus is that locus. -/
theorem range_pointsMap_flatLocusOpenSubspace (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) :
    Set.range (pointsMap B S hS (flatLocusOpenSubspace B S hS hX f F).toFunctor
      (flatLocusOpenSubspace B S hS hX f F).ι) = flatLocus B S hS hX f F :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-! ### The module on the flat locus -/

/-- On every commuting square of étale scheme charts, the restriction of the module to the
relative flat locus of that square is of finite presentation. -/
theorem isFinitePresentation_restrict_chartFlatLocus (hX : IsAlgebraicSpace B S hS X)
    {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y)
    (d : ChartDiagram B S hS X Y f) :
    letI Z : (etaleChartScheme B S hS d.U).Opens :=
      ⟨chartFlatLocus B S hS hX F d, isOpen_chartFlatLocus B S hS hX F hf hqc hft hwa d⟩
    ((chartModule B S hS hX F d.U).restrict Z.ι).IsFinitePresentation := by
  have := locallyOfFinitePresentation_chartDiagram B S hS hf d
  have := hqc d.U
  have := hft d.U
  exact _root_.AlgebraicGeometry.isFinitePresentation_restrict_of_subset_flatLocus
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS hX F d.U) (hwa d.V)
    _ Set.Subset.rfl

/-- On every commuting square of étale scheme charts, the restriction of the module to the
relative flat locus of that square is flat over the target chart. -/
theorem isFlatOver_restrict_chartFlatLocus (hX : IsAlgebraicSpace B S hS X)
    {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y)
    (d : ChartDiagram B S hS X Y f) :
    letI Z : (etaleChartScheme B S hS d.U).Opens :=
      ⟨chartFlatLocus B S hS hX F d, isOpen_chartFlatLocus B S hS hX F hf hqc hft hwa d⟩
    _root_.AlgebraicGeometry.IsFlatOver
      (Z.ι ≫ (BigFppfOver.toScheme B S hS).map d.g).toLRSHom.toShHom
      ((chartModule B S hS hX F d.U).restrict Z.ι) :=
  _root_.AlgebraicGeometry.isFlatOver_restrict_of_subset_flatLocus
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS hX F d.U) _ Set.Subset.rfl

end AlgebraicGeometry.Space

end
