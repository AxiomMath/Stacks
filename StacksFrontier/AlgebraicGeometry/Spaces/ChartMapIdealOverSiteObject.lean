module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAffineTest
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOverSpecQuotient

/-!
# An ideal of an object of the site killing a map of modules kills its base change on a chart

Let `B` be a big fppf site over a scheme `S` and let `X` be an algebraic space over an **object**
`Y₀` of the big fppf category over `S`, as in Stacks 083F with target the algebraic space of
`Y₀`. This file proves, with scalars in `Γ(Y₀, ⊤)`:

* the scalar towers over `Γ(Y₀, ⊤)` on the sections of a module over an étale chart and on the
  ring of functions of the chart of the source of a diagram of étale charts;
* the vanishing of the base change of a map of quasi-coherent modules over such a chart, given
  an ideal `J ⊆ Γ(Y₀, ⊤)` which kills the values of the map over the chart of the target and acts
  by zero on the functions of the chart of the source;
* that `J` acts by zero on the functions of every étale chart of a base change `X ×_{Y₀} T` when
  `J` dies in `Γ(T, ⊤)`.

## Main results

* `AlgebraicGeometry.Space.isScalarTower_chartRing_sections_site`: the tower on the sections of a
  module over a chart of an algebraic space over `Y₀`.
* `AlgebraicGeometry.Space.isScalarTower_chartDiagram_site`: the tower on the ring of functions of
  the chart of the source of a diagram of étale charts.
* `AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_site`: the
  chart-wise vanishing of the base change, with both hypotheses in the **chart-space spelling**
  of `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace`.
* `AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_site_chart`:
  the same with both hypotheses in the geometric spelling.
* `AlgebraicGeometry.Space.ModuleMapSituation.chartDiagram_g_comp_eq_chartToTest`: the structure
  morphism to `Y₀` of a chart of `X ×_{Y₀} T` above a chart of `X` factors through `T`.
* `AlgebraicGeometry.Space.ModuleMapSituation.smul_chartRing_baseChangeSpace_site_eq_zero`: an
  ideal of `Γ(Y₀, ⊤)` dying in `Γ(T, ⊤)` acts by zero on the ring of functions of every étale
  chart of `X ×_{Y₀} T`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The two actions on the sections of a module over a chart of an algebraic space over an
object `Y₀` of the site form a scalar tower**, the `Γ(Y₀, ⊤)`-action being restriction of
scalars along the pullback of functions by the morphism `α` from the chart to `Y₀`. -/
theorem isScalarTower_chartRing_sections_site (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, m} B S hS X.1 X.2) (A : SmallEtale B S hS X.1)
    {Y₀ : BigFppfOver B S hS} (α : chartFppfObject B S hS X A ⟶ Y₀) :
    letI := chartSiteAlgebra B S hS X A α
    letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u) (M.val.obj (op A)) :=
      Module.compHom _ (chartToSiteRingHom B S hS X A α)
    IsScalarTower (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS X.1 X.2 A) (M.val.obj (op A)) := by
  let := chartSiteAlgebra B S hS X A α
  let : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u) (M.val.obj (op A)) :=
    Module.compHom _ (chartToSiteRingHom B S hS X A α)
  exact ⟨fun r a x => mul_smul (chartToSiteRingHom B S hS X A α r) a x⟩

variable {X Y : AlgebraicSpaces B S hS}

/-- Pulling back global functions along a composite in the site is pulling back twice. -/
private theorem appTop_map_comp_site {P Q R : BigFppfOver B S hS} (g : P ⟶ Q) (α : Q ⟶ R)
    (r : Γ((BigFppfOver.toScheme B S hS).obj R, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (g ≫ α)).appTop.hom r =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom
        (((BigFppfOver.toScheme B S hS).map α).appTop.hom r) := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- **The two actions on the ring of functions of the chart of the source of a diagram of étale
charts form a scalar tower over the functions on an object `Y₀` of the site**, the chart of the
source being given the morphism `d.g ≫ α` to `Y₀`. -/
theorem isScalarTower_chartDiagram_site (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {Y₀ : BigFppfOver B S hS} (α : chartFppfObject B S hS Y d.V ⟶ Y₀) :
    letI := chartSiteAlgebra B S hS Y d.V α
    letI := chartSiteAlgebra B S hS X d.U (d.g ≫ α)
    letI := chartDiagramAlgebra B S hS f d
    IsScalarTower (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U) := by
  let := chartSiteAlgebra B S hS Y d.V α
  let := chartSiteAlgebra B S hS X d.U (d.g ≫ α)
  let := chartDiagramAlgebra B S hS f d
  refine ⟨fun r a c => ?_⟩
  have hcomp : chartDiagramRestrict B S hS f d (chartToSiteRingHom B S hS Y d.V α r) =
      chartToSiteRingHom B S hS X d.U (d.g ≫ α) r := by
    exact (appTop_map_comp_site B S hS d.g α r).symm
  change chartDiagramRestrict B S hS f d (chartToSiteRingHom B S hS Y d.V α r * a) * c =
    chartToSiteRingHom B S hS X d.U (d.g ≫ α) r * (chartDiagramRestrict B S hS f d a * c)
  rw [map_mul, hcomp, mul_assoc]

/-- **An ideal of the functions on an object `Y₀` of the site which kills the values of a map of
quasi-coherent modules over the affine chart of the target of a diagram of affine étale charts,
and which acts by zero on the functions of the chart of the source, kills the base change of the
map on the sections over that chart.**

The scalars act on the sections over the chart `d.V` of `Y` through the pullback of functions
along the given morphism `α : d.V ⟶ Y₀`, and on the functions of the chart `d.U` of `X` through
the pullback along `d.g ≫ α`. Both hypotheses are in the chart-space spelling of
`AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace`. -/
theorem modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_site (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (u : M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    {Y₀ : BigFppfOver B S hS}
    (α : chartFppfObject B S hS (chartSpace B S hS Y d.V)
      (chartSpaceIdChartDiagram B S hS f d).V ⟶ Y₀)
    (J : Ideal (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)) :
    letI := chartSiteAlgebra B S hS (chartSpace B S hS Y d.V)
      (chartSpaceIdChartDiagram B S hS f d).V α
    letI := chartSiteAlgebra B S hS (chartSpace B S hS X d.U)
      (chartSpaceIdChartDiagram B S hS f d).U ((chartSpaceIdChartDiagram B S hS f d).g ≫ α)
    letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (chartSpaceIdSections B S hS f N d) :=
      Module.compHom _ (chartToSiteRingHom B S hS (chartSpace B S hS Y d.V)
        (chartSpaceIdChartDiagram B S hS f d).V α)
    (∀ m : chartSpaceIdSections B S hS f M d,
        ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
            (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
          (op (chartSpaceIdChartDiagram B S hS f d).V) m ∈
        J • (⊤ : Submodule (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (chartSpaceIdSections B S hS f N d))) →
      (∀ a ∈ J, ∀ c : chartSpaceIdRing B S hS f d, a • c = 0) →
        ((modulePullback B S hS f).map u).val.app (op d.U) = 0 := by
  let := chartSiteAlgebra B S hS (chartSpace B S hS Y d.V)
    (chartSpaceIdChartDiagram B S hS f d).V α
  let := chartSiteAlgebra B S hS (chartSpace B S hS X d.U)
    (chartSpaceIdChartDiagram B S hS f d).U ((chartSpaceIdChartDiagram B S hS f d).g ≫ α)
  let : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartSpaceIdSections B S hS f M d) :=
    Module.compHom _ (chartToSiteRingHom B S hS (chartSpace B S hS Y d.V)
      (chartSpaceIdChartDiagram B S hS f d).V α)
  let : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartSpaceIdSections B S hS f N d) :=
    Module.compHom _ (chartToSiteRingHom B S hS (chartSpace B S hS Y d.V)
      (chartSpaceIdChartDiagram B S hS f d).V α)
  let := chartDiagramAlgebra B S hS (chartSpaceMapOver B S hS d.g)
    (chartSpaceIdChartDiagram B S hS f d)
  have := isScalarTower_chartRing_sections_site B S hS (chartSpace B S hS Y d.V)
    ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).obj M) (chartSpaceIdChartDiagram B S hS f d).V α
  have := isScalarTower_chartRing_sections_site B S hS (chartSpace B S hS Y d.V)
    ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).obj N) (chartSpaceIdChartDiagram B S hS f d).V α
  have := isScalarTower_chartDiagram_site B S hS (chartSpaceMapOver B S hS d.g)
    (chartSpaceIdChartDiagram B S hS f d) α
  intro hmem hC
  refine (val_app_eq_zero_iff_lTensor_chartSpace B S hS f hM hN u d hU hV).2 ?_
  exact Stacks.Flattening.lTensor_eq_zero_of_forall_mem_smul_top
    (((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
      (op (chartSpaceIdChartDiagram B S hS f d).V)).hom hmem
    (chartSpaceIdRing B S hS f d) hC

/-- **The same vanishing with both hypotheses in the geometric spelling**: the values of `u` over
the chart `d.V` of `Y`, and the ideal acting on the global functions of the scheme of the chart
`d.U` of `X` through the pullback along `d.g ≫ α`. -/
theorem modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_site_chart (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (u : M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    {Y₀ : BigFppfOver B S hS} (α : chartFppfObject B S hS Y d.V ⟶ Y₀)
    (J : Ideal (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)) :
    letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (N.val.obj (op d.V) : Type u) :=
      Module.compHom _ (chartToSiteRingHom B S hS Y d.V α)
    letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (Γ(chartScheme d.U, ⊤) : Type u) :=
      Module.compHom _ ((BigFppfOver.toScheme B S hS).map (d.g ≫ α)).appTop.hom
    (∀ x : M.val.obj (op d.V), u.val.app (op d.V) x ∈
        J • (⊤ : Submodule (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
          (N.val.obj (op d.V) : Type u))) →
      (∀ a ∈ J, ∀ c : (Γ(chartScheme d.U, ⊤) : Type u), a • c = 0) →
        ((modulePullback B S hS f).map u).val.app (op d.U) = 0 :=
  modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_site B S hS f hM hN u d hU hV α J

namespace ModuleMapSituation

/-- **The structure morphism to `Y₀` of a chart of `X ×_{Y₀} T` above a chart of `X` factors
through the test scheme.** -/
theorem chartDiagram_g_comp_eq_chartToTest (D : ModuleMapSituation.{u, u} B S hS)
    {Y₀ : BigFppfOver B S hS} (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver)
    (k : T.left ⟶ Y₀) (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k)
    (d : ChartDiagram B S hS (D.baseChangeSpace T).1 D.X.1 (D.baseChangeProjection T).hom)
    (α : chartFppfObject B S hS D.X d.V ⟶ Y₀)
    (hα : (d.V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α) :
    d.g ≫ α = chartToTest B S hS D T d.U ≫ k := by
  have hpre : d.U.1.hom ≫ (D.baseChangeInclusion T).hom =
      yoneda.map (chartToTest B S hS D T d.U) := (Functor.map_preimage _ _).symm
  have hsq := (isPullback_hom_baseChangeSpace B S hS D T).w
  apply yoneda.map_injective
  rw [yoneda.map_comp, yoneda.map_comp, ← hpre, ← hk, ← hα]
  have := congrArg (· ≫ (D.f.hom ≫ (eqToHom hDY).hom)) d.comm
  simp only [Category.assoc, reassoc_of% hsq] at this
  exact this.symm.trans (Category.assoc _ _ _).symm

/-- **An ideal of the functions on `Y₀` which dies in the functions on the test scheme acts by
zero on the ring of functions of every étale scheme chart of `X ×_{Y₀} T`**, the scalars acting
through the pullback of functions along the structure morphism `d.g ≫ α` of the chart to `Y₀`. -/
theorem smul_chartRing_baseChangeSpace_site_eq_zero (D : ModuleMapSituation.{u, u} B S hS)
    {Y₀ : BigFppfOver B S hS} (hDY : D.Y = schemeSpace Y₀) (T : D.SchemesOver)
    (k : T.left ⟶ Y₀) (hk : T.hom.hom ≫ (eqToHom hDY).hom = yoneda.map k)
    (d : ChartDiagram B S hS (D.baseChangeSpace T).1 D.X.1 (D.baseChangeProjection T).hom)
    (α : chartFppfObject B S hS D.X d.V ⟶ Y₀)
    (hα : (d.V.1.hom ≫ D.f.hom) ≫ (eqToHom hDY).hom = yoneda.map α)
    (J : Ideal (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u))
    (hJ : J ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom) :
    letI : Module (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
        (Γ(chartScheme d.U, ⊤) : Type u) :=
      Module.compHom _ ((BigFppfOver.toScheme B S hS).map (d.g ≫ α)).appTop.hom
    ∀ a ∈ J, ∀ c : (Γ(chartScheme d.U, ⊤) : Type u), a • c = 0 := by
  intro a ha c
  have hzero : ((BigFppfOver.toScheme B S hS).map (d.g ≫ α)).appTop.hom a = 0 := by
    rw [chartDiagram_g_comp_eq_chartToTest B S hS D hDY T k hk d α hα,
      appTop_map_comp_site B S hS]
    change ((BigFppfOver.toScheme B S hS).map (chartToTest B S hS D T d.U)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map k).appTop.hom a) = 0
    rw [show ((BigFppfOver.toScheme B S hS).map k).appTop.hom a = 0 from hJ ha, map_zero]
  change ((BigFppfOver.toScheme B S hS).map (d.g ≫ α)).appTop.hom a * c = 0
  rw [hzero, zero_mul]

end ModuleMapSituation

end AlgebraicGeometry.Space

end
