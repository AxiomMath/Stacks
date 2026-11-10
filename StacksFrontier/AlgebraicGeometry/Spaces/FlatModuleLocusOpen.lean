module
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Openness of the flat locus of a module of finite presentation

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation and let `F` be an `𝒪_X`-module which is quasi-coherent and of
finite presentation on every étale scheme chart. Then the set of points of `|X|` at which `F` is
flat over `Y` is open.

The flat locus is `AlgebraicGeometry.Space.flatLocus`, the union over the commuting squares of
étale scheme charts of `f` of the images of the flat loci of the source charts. A point lies in
it exactly when the geometric stalk of `F` at a geometric point over it is flat over the étale
local ring of the target, so the locus does not depend on the charts used to test it. On a
single commuting square of charts the flat locus is open by
`AlgebraicGeometry.isOpen_setOf_flatOverAt`, and an étale chart is an open map on points.

## Main definitions

* `AlgebraicGeometry.Space.IsFinitePresentationOnCharts`: a module on an algebraic space whose
  restriction to every étale scheme chart is of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts`: the flat locus is
  open.
* `AlgebraicGeometry.Space.isOpen_setOf_forall_isFlatOverAtGeometricPoint`: the set of points
  over which every geometric point has flat geometric stalk is open.
* `AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint` and
  `AlgebraicGeometry.Space.flatLocus_eq_setOf_forall_isFlatOverAtGeometricPoint`: the flat locus
  is the set of points over which the geometric stalks are flat.
* `AlgebraicGeometry.Space.isOpen_chartFlatLocus_of_isFinitePresentationOnCharts`: the flat
  locus on one commuting square of étale scheme charts is open.
* `AlgebraicGeometry.Space.chartPoint_iff_pointOfEtaleChart_eq`: a point of an étale scheme chart
  lies over a point of the space, in the sense of `AlgebraicGeometry.Space.ChartPoint`, exactly
  when the point of the space it determines is that point.

## References

* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Finite presentation on charts -/

/-- A module on an algebraic space is *of finite presentation on charts* when its restriction to
every étale scheme chart is a module of finite presentation on that scheme. -/
abbrev IsFinitePresentationOnCharts (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) : Prop :=
  ∀ U : SmallEtale B S hS X, (chartModule B S hS hX F U).IsFinitePresentation

/-! ### Openness of the flat locus -/

/-- On a commuting square of étale scheme charts of a morphism locally of finite presentation,
the flat locus of a module which is quasi-coherent of finite presentation on charts is open. -/
@[sga "3 VIB 1.3" "more general"]
theorem isOpen_chartFlatLocus_of_isFinitePresentationOnCharts
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hfp : IsFinitePresentationOnCharts B S hS hX F) (d : ChartDiagram B S hS X Y f) :
    IsOpen (chartFlatLocus B S hS hX F d) := by
  have := locallyOfFinitePresentation_chartDiagram B S hS hf d
  have := hqc d.U
  have := hfp d.U
  exact _root_.AlgebraicGeometry.isOpen_setOf_flatOverAt
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS hX F d.U)

/-- Membership of the flat locus, spelled out: a point of the source lies in it when some
commuting square of étale scheme charts has a point of its source chart above that point at
which the restricted module is flat over the target chart. -/
theorem mem_flatLocus_iff (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (x : points B S hS X) :
    x ∈ flatLocus B S hS hX f F ↔
      ∃ (d : ChartDiagram B S hS X Y f) (u : etaleChartScheme B S hS d.U),
        pointOfEtaleChart B S hS d.U u = x ∧ u ∈ chartFlatLocus B S hS hX F d :=
  Iff.rfl

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite
presentation and let `F` be an `𝒪_X`-module which is quasi-coherent of finite presentation on
charts. The set of points of `|X|` at which `F` is flat over `Y` is open. -/
@[stacks 05WV "openness of the flat locus; quasi-coherence and finite presentation of the \
module are read on the Zariski site of every etale scheme chart"]
theorem isOpen_flatLocus_of_isFinitePresentationOnCharts (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hfp : IsFinitePresentationOnCharts B S hS hX F) :
    IsOpen (flatLocus B S hS hX f F) := by
  rw [flatLocus_eq_iUnion_image]
  exact isOpen_iUnion fun d => isOpen_image_pointOfEtaleChart B S hS d.U
    (isOpen_chartFlatLocus_of_isFinitePresentationOnCharts B S hS hX F hf hqc hfp d)

/-! ### The locus through condition (2) of Stacks 05VU -/

/-- A point of an étale scheme chart lies over a point of the algebraic space, in the sense of
`AlgebraicGeometry.Space.ChartPoint`, exactly when the point of the space it determines is that
point. -/
theorem chartPoint_iff_pointOfEtaleChart_eq (U : SmallEtale B S hS X)
    (u : etaleChartScheme B S hS U) (x : points B S hS X) :
    ChartPoint B S hS U.obj.left U.obj.hom u x ↔ pointOfEtaleChart B S hS U u = x := by
  constructor
  · rintro ⟨p, hpu, hpx⟩
    have hsymm : (pointsEquivScheme B S hS U.obj.left).symm u =
        p.class B S hS (yoneda.obj U.obj.left) := by
      refine (Equiv.symm_apply_eq _).mpr ?_
      rw [← hpu]
      exact (pointsToScheme_class B S hS U.obj.left p).symm
    change pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
      ((pointsEquivScheme B S hS U.obj.left).symm u) = x
    rw [hsymm]
    exact hpx
  · rintro rfl
    have hu : pointsToScheme B S hS U.obj.left
        ((pointsEquivScheme B S hS U.obj.left).symm u) = u :=
      (pointsEquivScheme B S hS U.obj.left).apply_symm_apply u
    have hcp := chartPoint_pointsToScheme B S hS U.obj.left U.obj.hom
      ((pointsEquivScheme B S hS U.obj.left).symm u)
    rw [hu] at hcp
    exact hcp

variable {Xs Ys : AlgebraicSpaces B S hS}

/-- The image point of a geometric point lies in the flat locus exactly when the geometric stalk
of the module there is flat over the étale local ring of the target. -/
theorem mem_flatLocus_iff_isFlatOverAtGeometricPoint (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
    (xbar : GeometricPoint B S hS Xs.1) :
    xbar.image ∈ flatLocus B S hS Xs.2 f.hom F ↔
      IsFlatOverAtGeometricPoint B S hS f F xbar := by
  rw [mem_flatLocus_iff,
    ← isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint B S hS f F xbar]
  exact exists₂_congr fun d u =>
    and_congr_left' (chartPoint_iff_pointOfEtaleChart_eq B S hS d.U u xbar.image).symm

/-- The flat locus is the set of points of the source over which every geometric point has flat
geometric stalk. -/
theorem flatLocus_eq_setOf_forall_isFlatOverAtGeometricPoint (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite] :
    flatLocus B S hS Xs.2 f.hom F =
      {x : points B S hS Xs.1 | ∀ xbar : GeometricPoint B S hS Xs.1,
        xbar.image = x → IsFlatOverAtGeometricPoint B S hS f F xbar} := by
  refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · intro xbar hxbar
    subst hxbar
    exact (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F xbar).1 hx
  · obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS Xs.1 x
    exact (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F xbar).2 (hx xbar rfl)

/-- For a morphism of algebraic spaces locally of finite presentation and a quasi-coherent module
which is of finite presentation on charts, the set of points of the source over which the
geometric stalks of the module are flat over the étale local rings of the target is open. -/
@[stacks 05WV "openness of the flat locus, read through condition (2) of Stacks 05VU; \
finite presentation of the module is read on the Zariski site of every etale scheme chart"]
theorem isOpen_setOf_forall_isFlatOverAtGeometricPoint (f : Xs ⟶ Ys)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) [F.IsQuasicoherentOnSite]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hfp : IsFinitePresentationOnCharts B S hS Xs.2 F) :
    IsOpen {x : points B S hS Xs.1 | ∀ xbar : GeometricPoint B S hS Xs.1,
      xbar.image = x → IsFlatOverAtGeometricPoint B S hS f F xbar} := by
  rw [← flatLocus_eq_setOf_forall_isFlatOverAtGeometricPoint B S hS f F]
  exact isOpen_flatLocus_of_isFinitePresentationOnCharts B S hS Xs.2 f.hom F hf
    (fun U => isQuasicoherent_restrictToChart B S hS Xs F ‹_› U) hfp

end AlgebraicGeometry.Space

end
