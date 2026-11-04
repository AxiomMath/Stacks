module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeVanishingChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactSupportOfFiniteTypeModule

/-!
# A map of modules vanishes off the support of its source, and so does its base change

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B` and let `u : M ⟶ N` be a
map of `𝒪_X`-modules.  Where the source module has no nonzero sections the map is zero, and for
`M` of finite type that happens on a whole étale neighbourhood of every point outside the support
of `M` (Stacks 07TZ, through the scheme theoretic support of Stacks 07U1).  The same vanishing
then propagates to the base change of `u` along any morphism of algebraic spaces, read on the
sections over a diagram of affine étale charts.

## Main results

* `AlgebraicGeometry.Space.val_app_eq_zero_of_subsingleton`: a map of modules whose source has no
  nonzero sections over a chart vanishes on the sections over that chart.
* `AlgebraicGeometry.Space.exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf`: **off
  the support of a source module of finite type, `u` vanishes on an étale neighbourhood** — there
  is a chart whose image on points contains the given point and on which, and on every chart over
  which, `u` vanishes on sections.
* `AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_val_app_eq_zero`: **where `u`
  vanishes on the sections over an affine chart of the target of a chart diagram, its base change
  vanishes on the sections over the chart of the source.**

## Implementation notes

The support of a module is the set of points carrying a geometric point with nonvanishing stalk
(`AlgebraicGeometry.Space.supportOfSheaf`), so a point outside it has every geometric stalk over
it trivial, and `AlgebraicGeometry.Space.exists_zero_neighborhood_of_isFiniteTypeOnSite` — the
finite-type input of Stacks 07TZ — turns that into a chart over which the module has no nonzero
sections at all, together with every chart over it.  This is the same step by which
`AlgebraicGeometry.Space.supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport` identifies the
support with the points of the scheme theoretic support; what is added here is the conclusion for
the *map*, which needs nothing of the target module.

The base-change clause is `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartRing`, whose
right-hand side is an extension of scalars of the sections of `u` over the chart of the target,
read in the chart-space spelling; the sections of the chart restriction over the identity chart
are the sections over the chart
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_map_val_app_idEtaleChart`), so the
hypothesis makes that map zero and the extension of scalars of the zero map is zero.  No
cartesian-ness, no presentation and no flatness enters.

Together with `AlgebraicGeometry.Space.val_app_mem_span_range_chartRestrictLinear` this is what
lets a single ideal obtained at one affine chart of `X` serve at every chart in the
finite-presentation clause of Stacks 083K: the charts over the chosen one are handled by the
span statement, and the charts missing the support are handled here, where nothing has to be
transported at all.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Vanishing where the source module has no sections -/

/-- **A map of modules whose source has no nonzero sections over a chart vanishes on the sections
over that chart.** -/
theorem val_app_eq_zero_of_subsingleton {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {M N : Modules.{u, m} B S hS F hF} (u : M ⟶ N)
    (W : SmallEtale B S hS F) (h : Subsingleton (M.val.obj (op W))) :
    u.val.app (op W) = 0 := by
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  rw [Subsingleton.elim x 0]
  simp

/-! ### Vanishing off the support of the source module -/

variable (X : AlgebraicSpaces B S hS)

attribute [local instance] pointTopology

/-- **Off the support of a source module of finite type, a map of modules vanishes on an étale
neighbourhood.**

A point outside the support carries a geometric point, whose stalk is then trivial, and
`AlgebraicGeometry.Space.exists_zero_neighborhood_of_isFiniteTypeOnSite` produces a chart whose
image contains the point over which — and over every chart over which — the source module has no
nonzero sections; so `u` vanishes there by
`AlgebraicGeometry.Space.val_app_eq_zero_of_subsingleton`. -/
theorem exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf
    {M N : Modules.{u, u} B S hS X.1 X.2} (hMft : SheafOfModules.IsFiniteTypeOnSite M)
    (u : M ⟶ N) {x : points B S hS X.1}
    (hx : x ∉ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) :
    ∃ W : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom) ∧
        ∀ (V : SmallEtale B S hS X.1), (V ⟶ W) → u.val.app (op V) = 0 := by
  have := hMft
  obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS X.1 x
  have hsub : Subsingleton (stalkSet p
      (((SheafOfModules.toSheaf _).obj M).obj ⋙ forget AddCommGrpCat.{u})) := by
    by_contra hc
    exact hx ⟨p, hp, hc⟩
  obtain ⟨W, hW⟩ :=
    exists_zero_neighborhood_of_isFiniteTypeOnSite B S hS X.1 X.2 (𝟙 M) p hsub
  exact ⟨W.chart,
    ⟨(neighborhoodPoint B S hS X.1 W).image,
      (neighborhoodPoint_image B S hS X.1 W).trans hp⟩,
    fun V g => val_app_eq_zero_of_subsingleton B S hS u V (hW V g)⟩

/-! ### The base change of a map vanishing on the sections over a chart -/

/-- **Where a map of quasi-coherent modules vanishes on the sections over the affine chart of the
target of a diagram of affine étale charts, its base change vanishes on the sections over the
chart of the source.**

This is `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartRing`: the map whose extension
of scalars appears on its right-hand side is the map on sections over the chart of the target
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_map_val_app_idEtaleChart`), which is
zero by hypothesis, and the extension of scalars of the zero map is zero. -/
theorem modulePullback_map_val_app_eq_zero_of_val_app_eq_zero {X' Y : AlgebraicSpaces B S hS}
    (f : X' ⟶ Y) {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (u : M ⟶ N)
    (d : ChartDiagram B S hS X'.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (h : u.val.app (op d.V) = 0) :
    ((modulePullback B S hS f).map u).val.app (op d.U) = 0 := by
  let : Algebra
      (chartRing B S hS (chartSpace B S hS Y d.V).1 (chartSpace B S hS Y d.V).2
        (chartSpaceIdChartDiagram B S hS f d).V)
      (chartRing B S hS X'.1 X'.2 d.U) := chartDiagramAlgebra B S hS f d
  have key : ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
      (op (chartSpaceIdChartDiagram B S hS f d).V) = 0 :=
    (etaleModulePullback_chartToSpace_map_val_app_idEtaleChart B S hS u d.V).trans h
  have hhom : (((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
      (op (chartSpaceIdChartDiagram B S hS f d).V)).hom = 0 := by
    rw [key]; rfl
  refine (val_app_eq_zero_iff_lTensor_chartRing B S hS f hM hN u d hU hV).2 ?_
  refine Eq.trans (congrArg (fun φ => LinearMap.lTensor
    (chartRing B S hS X'.1 X'.2 d.U) φ) hhom) ?_
  exact LinearMap.lTensor_zero _

end AlgebraicGeometry.Space

end
