module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetModuleFMapRestriction

/-!
# The comparison of a pullback of an étale restriction with the pullback along the composite

Let `a : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let `p : Y ⟶ Z` be an étale, relatively representable morphism.  For an `𝒪_Z`-module `M` there
is a canonical morphism

`a^*(M|_Y) ⟶ (a ≫ p)^*M`

of `𝒪_X`-modules: its chartwise transpose is the chart component of the unit of the Stacks 03D7
adjunction at `a ≫ p`, restricted to the chart diagrams over `a` by
`AlgebraicGeometry.Space.moduleFMapEtaleRestrict`.  This file constructs it and shows it is an
**isomorphism**, which needs no coherence of the comparisons of Stacks 03LU and 03LW: both sides
are pullbacks of modules, so a morphism out of either is a linear map of sections
(`AlgebraicGeometry.Space.modulePullbackFMapEquiv`), and composition with the comparison is
exactly the restriction of linear maps of sections, which is a bijection.

The consequence drawn here is a case of the chart bijectivity of Stacks 083K with **no
presentation hypothesis**: over a diagram of affine étale charts of `f : X ⟶ Y`, the canonical
base-change comparison of the pullback along the composite

`chartSpace X d.U ⟶ chartSpace Y d.V ⟶ Y`

at the diagram whose chart of the source is the identity chart and whose chart of `Y` is `d.V` is
bijective for every quasi-coherent `M`.  That composite is the structure morphism of the chart
`d.U` followed by `f` (`AlgebraicGeometry.Space.chartSpaceMapOver_comp_chartToSpace`), so what
separates this from the chart bijectivity at `(f, d)` itself is only the identification of the
sections of `(p_U ≫ f)^*M` over the identity chart with the sections of `f^*M` over `d.U` — the
compatibility of Stacks 03LU with Stacks 03LW, which this development does not have.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackEtaleTargetComparison`: the comparison
  `a^*(M|_Y) ⟶ (a ≫ p)^*M`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackEtaleTargetComparison_chartSection`: **the defining
  property** — the comparison carries the chart section of `a` at a diagram `e` to the chart
  section of `a ≫ p` at the diagram with the chart of `Y` postcomposed with `p`.
* `AlgebraicGeometry.Space.isIso_modulePullbackEtaleTargetComparison`: **the comparison is an
  isomorphism.**
* `AlgebraicGeometry.Space.modulePullbackEtaleTargetComparison_baseChange`: it carries the
  base-change comparison at `(a, e)` to the one at `(a ≫ p, e.postcompTarget)`.
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_postcompTarget`: so the latter
  is bijective as soon as the former is.
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_chartSpaceSource`: **the
  presentation-free chart bijectivity over the chart space of the source chart.**

## Implementation notes

The isomorphism is proved by the universal property alone: for every `𝒪_X`-module `N` the map
`u ↦ Θ ≫ u` is conjugate, by the two chartwise transposes, to the restriction of linear maps of
sections, which is bijective; so `Θ` has a right inverse by surjectivity at `N = a^*(M|_Y)` and
that right inverse is a left inverse by injectivity at `N = (a ≫ p)^*M`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

section Comparison

variable (a : X ⟶ Y) (p : Y ⟶ Z) (hp : IsEtale B S hS p.hom)
    (hrep : yoneda.relativelyRepresentable p.hom) (M : Modules.{u, u} B S hS Z.1 Z.2)

/-- **The comparison of the pullback of an étale restriction with the pullback along the
composite**: the morphism

`a^*(M|_Y) ⟶ (a ≫ p)^*M`

of `𝒪_X`-modules whose chartwise transpose is the restriction to the chart diagrams over `a` of
the chart component of the unit of the Stacks 03D7 adjunction at `a ≫ p`. -/
noncomputable def modulePullbackEtaleTargetComparison :
    (modulePullback B S hS a).obj ((etaleModulePullback B S hS p hp).obj M) ⟶
      (modulePullback B S hS (a ≫ p)).obj M :=
  (modulePullbackFMapEquiv B S hS a ((modulePullback B S hS (a ≫ p)).obj M)
      ((etaleModulePullback B S hS p hp).obj M)).symm
    (moduleFMapEtaleRestrict B S hS a p hp ((modulePullback B S hS (a ≫ p)).obj M) M
      (modulePullbackChartFMap B S hS (a ≫ p) M))

/-- The chartwise transpose of the comparison is the restricted chart component of the unit. -/
theorem modulePullbackHomFMap_modulePullbackEtaleTargetComparison :
    modulePullbackHomFMap B S hS a ((etaleModulePullback B S hS p hp).obj M)
        ((modulePullback B S hS (a ≫ p)).obj M)
        (modulePullbackEtaleTargetComparison B S hS a p hp M) =
      moduleFMapEtaleRestrict B S hS a p hp ((modulePullback B S hS (a ≫ p)).obj M) M
        (modulePullbackChartFMap B S hS (a ≫ p) M) :=
  (modulePullbackFMapEquiv B S hS a _ _).apply_symm_apply _

/-- **The defining property of the comparison: it carries the chart section of `a` to the chart
section of `a ≫ p`.** -/
theorem modulePullbackEtaleTargetComparison_chartSection
    (e : ChartDiagram B S hS X.1 Y.1 a.hom)
    (s : ((etaleModulePullback B S hS p hp).obj M).val.obj (op e.V)) :
    (modulePullbackEtaleTargetComparison B S hS a p hp M).val.app (op e.U)
        (modulePullbackChartSection B S hS a
          ((etaleModulePullback B S hS p hp).obj M) e s) =
      modulePullbackChartSection B S hS (a ≫ p) M (e.postcompTarget B S hS a p hp) s := by
  refine Eq.trans (congrArg
    (fun w ↦ (modulePullbackEtaleTargetComparison B S hS a p hp M).val.app (op e.U) w)
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS a
      ((etaleModulePullback B S hS p hp).obj M) e s).symm) ?_
  refine Eq.trans (modulePullbackHomFMap_app B S hS a
    ((etaleModulePullback B S hS p hp).obj M) ((modulePullback B S hS (a ≫ p)).obj M)
    (modulePullbackEtaleTargetComparison B S hS a p hp M) e s).symm ?_
  refine Eq.trans (congrArg (fun ξ ↦ ModuleFMap.app ξ e s)
    (modulePullbackHomFMap_modulePullbackEtaleTargetComparison B S hS a p hp M)) ?_
  exact modulePullbackChartFMap_app B S hS (a ≫ p) M (e.postcompTarget B S hS a p hp) s

/-- **Composition with the comparison is the restriction of linear maps of sections.**  Both
sides are read on a chart diagram over `a` through
`AlgebraicGeometry.Space.modulePullbackHomFMap_app`, and the defining property of the comparison
identifies them. -/
theorem modulePullbackFMapEquiv_comp_modulePullbackEtaleTargetComparison
    (N : Modules.{u, u} B S hS X.1 X.2) (u : (modulePullback B S hS (a ≫ p)).obj M ⟶ N) :
    modulePullbackFMapEquiv B S hS a N ((etaleModulePullback B S hS p hp).obj M)
        (modulePullbackEtaleTargetComparison B S hS a p hp M ≫ u) =
      moduleFMapEtaleRestrict B S hS a p hp N M
        (modulePullbackFMapEquiv B S hS (a ≫ p) N M u) := by
  refine ModuleFMap.ext B S hS (funext fun e ↦ funext fun s ↦ ?_)
  refine Eq.trans (modulePullbackHomFMap_app B S hS a
    ((etaleModulePullback B S hS p hp).obj M) N
    (modulePullbackEtaleTargetComparison B S hS a p hp M ≫ u) e s) ?_
  refine Eq.trans (comp_val_app_apply B S hS
    (modulePullbackEtaleTargetComparison B S hS a p hp M) u (op e.U)
    (modulePullbackUnitSection B S hS a ((etaleModulePullback B S hS p hp).obj M) e s)) ?_
  have hchart : (modulePullbackEtaleTargetComparison B S hS a p hp M).val.app (op e.U)
        (modulePullbackUnitSection B S hS a ((etaleModulePullback B S hS p hp).obj M) e s) =
      modulePullbackUnitSection B S hS (a ≫ p) M (e.postcompTarget B S hS a p hp) s := by
    rw [modulePullbackUnitSection_eq_modulePullbackChartSection]
    exact (modulePullbackEtaleTargetComparison_chartSection B S hS a p hp M e s).trans
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS (a ≫ p) M
        (e.postcompTarget B S hS a p hp) s).symm
  refine Eq.trans (congrArg (fun w ↦ u.val.app (op e.U) w) hchart) ?_
  exact (modulePullbackHomFMap_app B S hS (a ≫ p) M N u
    (e.postcompTarget B S hS a p hp) s).symm

include hrep in
/-- **Composition with the comparison is a bijection on morphisms out of it.**  It is conjugate,
by the two chartwise transposes of Stacks 03D7, to the restriction of linear maps of sections,
which is a bijection by
`AlgebraicGeometry.Space.bijective_moduleFMapEtaleRestrict`. -/
theorem bijective_comp_modulePullbackEtaleTargetComparison
    (N : Modules.{u, u} B S hS X.1 X.2) :
    Function.Bijective (fun u : (modulePullback B S hS (a ≫ p)).obj M ⟶ N ↦
      modulePullbackEtaleTargetComparison B S hS a p hp M ≫ u) := by
  have hR := bijective_moduleFMapEtaleRestrict B S hS a p hp hrep N M
  have key := modulePullbackFMapEquiv_comp_modulePullbackEtaleTargetComparison
    B S hS a p hp M N
  have hfun : (fun u : (modulePullback B S hS (a ≫ p)).obj M ⟶ N ↦
      modulePullbackEtaleTargetComparison B S hS a p hp M ≫ u) =
      (modulePullbackFMapEquiv B S hS a N ((etaleModulePullback B S hS p hp).obj M)).symm ∘
        moduleFMapEtaleRestrict B S hS a p hp N M ∘
          modulePullbackFMapEquiv B S hS (a ≫ p) N M :=
    funext fun u ↦ Equiv.eq_symm_apply _ |>.2 (key u)
  rw [hfun]
  exact ((Equiv.bijective _).comp hR).comp (Equiv.bijective _)

include hrep in
/-- **The comparison is an isomorphism.**  Composition with it is bijective on morphisms out of
it, so it has a right inverse, and that right inverse is a left inverse by injectivity of
composition with it. -/
theorem isIso_modulePullbackEtaleTargetComparison :
    IsIso (modulePullbackEtaleTargetComparison B S hS a p hp M) := by
  obtain ⟨v, hv⟩ := (bijective_comp_modulePullbackEtaleTargetComparison B S hS a p hp hrep M
    ((modulePullback B S hS a).obj ((etaleModulePullback B S hS p hp).obj M))).2 (𝟙 _)
  have hv' : modulePullbackEtaleTargetComparison B S hS a p hp M ≫ v = 𝟙 _ := hv
  refine ⟨v, hv', ?_⟩
  refine (bijective_comp_modulePullbackEtaleTargetComparison B S hS a p hp hrep M
    ((modulePullback B S hS (a ≫ p)).obj M)).1 ?_
  change modulePullbackEtaleTargetComparison B S hS a p hp M ≫ v ≫
      modulePullbackEtaleTargetComparison B S hS a p hp M =
    modulePullbackEtaleTargetComparison B S hS a p hp M ≫ 𝟙 _
  rw [← Category.assoc, hv', Category.id_comp, Category.comp_id]

include hrep in
/-- **The comparison is bijective on the sections over every chart.** -/
theorem bijective_modulePullbackEtaleTargetComparison_val_app
    (U : SmallEtale B S hS X.1) :
    Function.Bijective
      ((modulePullbackEtaleTargetComparison B S hS a p hp M).val.app (op U)) :=
  have := isIso_modulePullbackEtaleTargetComparison B S hS a p hp hrep M
  SheafOfModules.bijective_iso_hom_val_app
    (asIso (modulePullbackEtaleTargetComparison B S hS a p hp M)) (op U)

/-- **The comparison carries the base-change comparison at `(a, e)` to the base-change comparison
at `(a ≫ p, e.postcompTarget)`.**  Both are the `𝒪_X(e.U)`-linear extension of a chart section,
and the comparison is linear on sections, so this is the defining property
`AlgebraicGeometry.Space.modulePullbackEtaleTargetComparison_chartSection` spread over the tensor
product.  The two tensor products are the same: postcomposing the chart of `Y` with `p` changes
neither the structure rings, nor the algebra structure, nor the sections of the module. -/
theorem modulePullbackEtaleTargetComparison_baseChange
    (e : ChartDiagram B S hS X.1 Y.1 a.hom) :
    letI := chartDiagramAlgebra B S hS a e
    ∀ z : TensorProduct (chartRing B S hS Y.1 Y.2 e.V) (chartRing B S hS X.1 X.2 e.U)
        (((etaleModulePullback B S hS p hp).obj M).val.obj (op e.V)),
      (modulePullbackEtaleTargetComparison B S hS a p hp M).val.app (op e.U)
          (modulePullbackChartBaseChange B S hS a
            ((etaleModulePullback B S hS p hp).obj M) e z) =
        modulePullbackChartBaseChange B S hS (a ≫ p) M (e.postcompTarget B S hS a p hp) z := by
  let _ := chartDiagramAlgebra B S hS a e
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b s =>
    refine Eq.trans ?_ (modulePullbackChartBaseChange_tmul B S hS (a ≫ p) M
      (e.postcompTarget B S hS a p hp) b s).symm
    rw [modulePullbackChartBaseChange_tmul,
      ((modulePullbackEtaleTargetComparison B S hS a p hp M).val.app (op e.U)).hom.map_smul]
    exact congrArg (fun y ↦ b • y)
      (modulePullbackEtaleTargetComparison_chartSection B S hS a p hp M e s)
  | add z w hz hw =>
    simp only [map_add, hz, hw]
    exact (map_add _ z w).symm

include hrep in
/-- **The base-change comparison at the diagram with the chart of `Y` postcomposed with `p` is
bijective as soon as the one at the given diagram is.**  The first is a factor of the second
through `AlgebraicGeometry.Space.modulePullbackEtaleTargetComparison_baseChange`, and the
comparison is bijective on sections. -/
theorem bijective_modulePullbackChartBaseChange_postcompTarget
    (e : ChartDiagram B S hS X.1 Y.1 a.hom)
    (hb : letI := chartDiagramAlgebra B S hS a e
      Function.Bijective (modulePullbackChartBaseChange B S hS a
        ((etaleModulePullback B S hS p hp).obj M) e)) :
    letI := chartDiagramAlgebra B S hS (a ≫ p) (e.postcompTarget B S hS a p hp)
    Function.Bijective (modulePullbackChartBaseChange B S hS (a ≫ p) M
      (e.postcompTarget B S hS a p hp)) := by
  let _ := chartDiagramAlgebra B S hS a e
  have hcomp := bijective_modulePullbackEtaleTargetComparison_val_app B S hS a p hp hrep M e.U
  have key := modulePullbackEtaleTargetComparison_baseChange B S hS a p hp M e
  refine ⟨fun z w hzw ↦ hb.1 (hcomp.1 ((key z).trans (hzw.trans (key w).symm))), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hcomp.2 y
  obtain ⟨z, hz⟩ := hb.2 x
  refine ⟨z, ?_⟩
  rw [← key z, hz, hx]

end Comparison

/-! ### The presentation-free chart bijectivity over the chart space of the source chart -/

/-- **The canonical base-change comparison of the pullback along
`chartSpace X d.U ⟶ chartSpace Y d.V ⟶ Y` is bijective at a quasi-coherent module over the
diagram of the identity chart and `d.V`.**

No presentation of `M` is assumed.  The restriction of `M` to the chart space of `d.V` carries a
presentation which is right exact on the sections over its identity chart
(`AlgebraicGeometry.Space.exists_presentation_rightExact_app_idEtaleChart`), so
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange` applies to the morphism of
chart spaces, and
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_postcompTarget` carries that
across the comparison, which is an isomorphism.

The morphism this is stated for is the structure morphism of the chart `d.U` followed by `f`, by
`AlgebraicGeometry.Space.chartSpaceMapOver_comp_chartToSpace`. -/
theorem bijective_modulePullbackChartBaseChange_chartSpaceSource {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebra B S hS
      (chartSpaceMapOver B S hS d.g ≫ chartToSpace B S hS Y d.V)
      ((chartSpaceIdChartDiagram B S hS f d).postcompTarget B S hS
        (chartSpaceMapOver B S hS d.g) (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V))
    Function.Bijective (modulePullbackChartBaseChange B S hS
      (chartSpaceMapOver B S hS d.g ≫ chartToSpace B S hS Y d.V) M
      ((chartSpaceIdChartDiagram B S hS f d).postcompTarget B S hS
        (chartSpaceMapOver B S hS d.g) (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V))) := by
  obtain ⟨P, hgen, -, hex⟩ :=
    exists_presentation_rightExact_app_idEtaleChart B S hS Y M hM d.V hV
  exact bijective_modulePullbackChartBaseChange_postcompTarget B S hS
    (chartSpaceMapOver B S hS d.g) (chartToSpace B S hS Y d.V)
    (isEtale_chartToSpace B S hS Y d.V)
    (Functor.relativelyRepresentable.of_diag Y.2.diagonal_representable
      (chartToSpace B S hS Y d.V).hom) M (chartSpaceIdChartDiagram B S hS f d)
    (bijective_modulePullbackChartBaseChange B S hS (chartSpaceMapOver B S hS d.g)
      ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V)).obj M)
      (isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
        (isEtale_chartToSpace B S hS Y d.V) M hM)
      P (chartSpaceIdChartDiagram B S hS f d) hU hV hgen hex)

end AlgebraicGeometry.Space

end
