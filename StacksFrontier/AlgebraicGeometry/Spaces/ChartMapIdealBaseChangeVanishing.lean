module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeVanishingQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartScalarTowerOverBase
public import StacksFrontier.RingTheory.Flat.MakeMapZeroIdeal

/-!
# An ideal of the base killing a map of modules kills its base change on a chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let
`u : M ⟶ N` be a map of quasi-coherent `𝒪_Y`-modules, and let `d` be a commuting square of
affine étale charts over `f` — a chart `d.U` of `X` above a chart `d.V` of `Y`.  Let `J` be an
ideal of `Γ(S, ⊤)`.  If every value of `u` over `d.V` lies in `J · N(d.V)` and `J` acts by zero
on the ring of functions of `d.U`, then the base change `f^*u` vanishes on the sections over
`d.U`.

This is the chartwise form of the vanishing clause of Stacks 083K: there `Y = X`, `X` is
`X ×_S Z` for the closed subscheme `Z = \Spec(Γ(S, ⊤)/J)` cut out by the ideal, the first
hypothesis is what the ideal was built to satisfy, and the second is
`AlgebraicGeometry.Space.smul_chartRing_baseChangeSpace_eq_zero`.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top`: the
  vanishing, with both hypotheses taken in the **chart-space spelling** of
  `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace`.
* `AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_chart`: the
  same vanishing, with both hypotheses in the geometric spelling.

## Implementation notes

The two inputs are `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace`, which turns
the vanishing of the base change on the sections over `d.U` into the vanishing of an extension of
scalars of the sections of `u`, and
`Stacks.Flattening.lTensor_eq_zero_of_forall_mem_smul_top`, which proves exactly such an
extension of scalars zero from the two hypotheses.  The scalar towers they need are
`AlgebraicGeometry.Space.isScalarTower_chartRing_sections` on the sections of the two modules and
`AlgebraicGeometry.Space.isScalarTower_chartDiagram` on the ring of functions of the chart of the
source.

**Why the chart-space spelling.**  The tensor product on the right-hand side of
`AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace` is taken over the ring of the
identity chart of the chart space of `d.V`, not over `𝒪_Y(d.V)`.  So the main theorem states
everything — the map whose values are constrained, the module its values lie in, and the ring
the ideal acts on — in the spelling that criterion uses, in which the tensor product needs no
conversion and the two towers are available at the chart space.  The two hypotheses themselves
are definitionally the same in the `𝒪_Y(d.V)` and `Γ(chartScheme d.U, ⊤)` spellings, in which a
geometric consumer has them, and
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_chart` is the
statement in those spellings.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The chart restriction of an `𝒪_Y`-module to the chart space of the chart of the target of a
diagram of étale charts, read on its sections over the identity chart of that chart space.  This
is the spelling in which `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace` states
the sections of the module over the chart. -/
abbrev chartSpaceIdSections (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) : Type u :=
  (((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).obj M).val.obj
    (op (chartSpaceIdChartDiagram B S hS f d).V) : Type u)

/-- The ring of functions of the identity chart of the chart space of the chart of the source of
a diagram of étale charts, in the spelling of
`AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace`. -/
abbrev chartSpaceIdRing (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) : Type u :=
  chartRing B S hS (chartSpace B S hS X d.U).1 (chartSpace B S hS X d.U).2
    (chartSpaceIdChartDiagram B S hS f d).U

/-- **An ideal of the functions on the base which kills the values of a map of quasi-coherent
modules over the affine chart of the target of a diagram of affine étale charts, and which acts
by zero on the functions of the chart of the source, kills the base change of the map on the
sections over that chart.**

Both hypotheses are in the chart-space spelling of
`AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace`; see the implementation notes of
this file. -/
theorem modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (u : M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (J : Ideal Γ(S, ⊤)) :
    letI := chartBaseAlgebra B S hS (chartSpace B S hS Y d.V)
      (chartSpaceIdChartDiagram B S hS f d).V
    letI := chartBaseAlgebra B S hS (chartSpace B S hS X d.U)
      (chartSpaceIdChartDiagram B S hS f d).U
    letI : Module Γ(S, ⊤) (chartSpaceIdSections B S hS f N d) :=
      Module.compHom _ (chartToBaseRingHom B S hS (chartSpace B S hS Y d.V)
        (chartSpaceIdChartDiagram B S hS f d).V)
    (∀ m : chartSpaceIdSections B S hS f M d,
        ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
            (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
          (op (chartSpaceIdChartDiagram B S hS f d).V) m ∈
        J • (⊤ : Submodule Γ(S, ⊤) (chartSpaceIdSections B S hS f N d))) →
      (∀ a ∈ J, ∀ c : chartSpaceIdRing B S hS f d, a • c = 0) →
        ((modulePullback B S hS f).map u).val.app (op d.U) = 0 := by
  let := chartBaseAlgebra B S hS (chartSpace B S hS Y d.V)
    (chartSpaceIdChartDiagram B S hS f d).V
  let := chartBaseAlgebra B S hS (chartSpace B S hS X d.U)
    (chartSpaceIdChartDiagram B S hS f d).U
  let : Module Γ(S, ⊤) (chartSpaceIdSections B S hS f M d) :=
    Module.compHom _ (chartToBaseRingHom B S hS (chartSpace B S hS Y d.V)
      (chartSpaceIdChartDiagram B S hS f d).V)
  let : Module Γ(S, ⊤) (chartSpaceIdSections B S hS f N d) :=
    Module.compHom _ (chartToBaseRingHom B S hS (chartSpace B S hS Y d.V)
      (chartSpaceIdChartDiagram B S hS f d).V)
  let := chartDiagramAlgebra B S hS (chartSpaceMapOver B S hS d.g)
    (chartSpaceIdChartDiagram B S hS f d)
  have := isScalarTower_chartRing_sections B S hS (chartSpace B S hS Y d.V)
    ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).obj M) (chartSpaceIdChartDiagram B S hS f d).V
  have := isScalarTower_chartRing_sections B S hS (chartSpace B S hS Y d.V)
    ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).obj N) (chartSpaceIdChartDiagram B S hS f d).V
  have := isScalarTower_chartDiagram B S hS (chartSpaceMapOver B S hS d.g)
    (chartSpaceIdChartDiagram B S hS f d)
  intro hmem hC
  refine (val_app_eq_zero_iff_lTensor_chartSpace B S hS f hM hN u d hU hV).2 ?_
  exact Stacks.Flattening.lTensor_eq_zero_of_forall_mem_smul_top
    (((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
      (op (chartSpaceIdChartDiagram B S hS f d).V)).hom hmem
    (chartSpaceIdRing B S hS f d) hC

/-- **The same vanishing with both hypotheses in the geometric spelling**: the values of `u` over
the chart `d.V` of `Y`, and the ideal acting on the global functions of the scheme of the chart
`d.U` of `X` through its structure morphism to the base.

This is the form in which a consumer has the two hypotheses:
`AlgebraicGeometry.Space.val_app_mem_smul_top_of_forall_mem_smul_top` supplies the first and
`AlgebraicGeometry.Space.smul_chartRing_baseChangeSpace_eq_zero` the second. -/
theorem modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_chart (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (u : M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (J : Ideal Γ(S, ⊤)) :
    letI : Module Γ(S, ⊤) (N.val.obj (op d.V) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS Y d.V)
    letI : Module Γ(S, ⊤) (Γ(chartScheme d.U, ⊤) : Type u) :=
      Module.compHom _ (chartToBase B S hS X d.U).appTop.hom
    (∀ x : M.val.obj (op d.V), u.val.app (op d.V) x ∈
        J • (⊤ : Submodule Γ(S, ⊤) (N.val.obj (op d.V) : Type u))) →
      (∀ a ∈ J, ∀ c : (Γ(chartScheme d.U, ⊤) : Type u), a • c = 0) →
        ((modulePullback B S hS f).map u).val.app (op d.U) = 0 :=
  modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top B S hS f hM hN u d hU hV J

end AlgebraicGeometry.Space

end
