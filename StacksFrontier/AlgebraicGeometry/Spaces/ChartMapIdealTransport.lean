module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapImageSpan
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartScalarTowerOverBase
public import StacksFrontier.RingTheory.Flat.MakeMapZeroIdeal

/-!
# Transporting an ideal of the base along a morphism of affine charts

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `u : M ⟶ N` be a map
of `𝒪_X`-modules with `M` cartesian on affine charts, and let `J` be an ideal of the ring
`Γ(S, ⊤)` of functions on the base.  If every value of `u` over an affine étale chart `U` lies in
`J · N(U)`, then every value of `u` over any affine étale chart `V` *over* `U` lies in `J · N(V)`.

This is the mechanism by which one ideal, obtained by the commutative algebra of
`StacksFrontier/RingTheory/Flat/MakeMapZeroIdeal.lean` at a single affine chart, serves at every
chart over that one; it is the step the finite-presentation clause of Stacks 083K needs, because
there the ideal must be finitely generated and so cannot be recomputed chart by chart.

## Main results

* `AlgebraicGeometry.Space.chartToBase_comp_map`: the structure morphism to the base of the
  smaller of two charts factors through that of the larger.
* `AlgebraicGeometry.Space.chartRestrict_chartToBaseRingHom`: restriction of functions along a
  chart morphism carries the pullback of a function on the base to the pullback of that same
  function.
* `AlgebraicGeometry.Space.chartRestrictLinear_smul_base`: restriction of sections along a chart
  morphism is `Γ(S, ⊤)`-linear.
* `AlgebraicGeometry.Space.chartRestrictLinear_mem_smul_top`: it carries `J · M(U)` into
  `J · M(V)`.
* `AlgebraicGeometry.Space.val_app_mem_smul_top_of_forall_mem_smul_top`: **an ideal of the base
  annihilating the image of `u` over an affine chart annihilates it over every affine chart over
  that one.**

## Implementation notes

The `Γ(S, ⊤)`-action on the sections over a chart is restriction of scalars along the pullback of
functions by the structure morphism of the chart
(`AlgebraicGeometry.Space.chartToBaseRingHom`), as in
`AlgebraicGeometry.Space.flat_sections_of_isFlatOver`, so `Γ(S, ⊤)`-linearity of restriction is
the statement that the two routes from `Γ(S, ⊤)` to the functions of the smaller chart agree.
That is the triangle of the big fppf category over `S` — `CategoryTheory.Over.w` — exactly as in
`AlgebraicGeometry.Space.isScalarTower_chartDiagram`, here for the vertical morphism of a
morphism of charts of one space rather than of a diagram of charts over a morphism of spaces.

The transport itself is `AlgebraicGeometry.Space.val_app_mem_span_range_chartRestrictLinear`
together with `Stacks.Flattening.smulTopOfTower`: the values of `u` over `V` lie in the
`𝒪_X(V)`-span of the restrictions of the values over `U`, those restrictions lie in `J · N(V)`,
and `J · N(V)` is an `𝒪_X(V)`-submodule because the two scalar actions commute — which is the
scalar tower `AlgebraicGeometry.Space.isScalarTower_chartRing_sections`.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ### The structure morphisms of two charts over each other -/

/-- **The structure morphism to the base of the smaller of two étale charts factors through that
of the larger.**  A morphism of charts is a morphism of the big fppf category over `S`, hence a
morphism over `S`. -/
theorem chartToBase_comp_map {U V : SmallEtale B S hS X.1} (φ : V ⟶ U) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map φ) ≫
        chartToBase B S hS X U = chartToBase B S hS X V := by
  rw [chartToBase_eq, chartToBase_eq]
  exact (Functor.map_comp B.inclusion ((SmallEtale.toOver B S hS X.1).map φ).left
      (chartFppfObject B S hS X U).hom).symm.trans
    (congrArg B.inclusion.map (Over.w ((SmallEtale.toOver B S hS X.1).map φ)))

/-- **Restriction of functions along a morphism of étale charts carries the pullback of a
function on the base to the pullback of that same function.** -/
theorem chartRestrict_chartToBaseRingHom {U V : SmallEtale B S hS X.1} (φ : V ⟶ U)
    (r : Γ(S, ⊤)) :
    chartRestrict (hF := X.2) φ (chartToBaseRingHom B S hS X U r) =
      chartToBaseRingHom B S hS X V r := by
  have h2 := congrArg (fun k : chartScheme V ⟶ S => k.appTop.hom r)
    (chartToBase_comp_map B S hS X φ)
  change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map φ)).appTop.hom
      ((chartToBase B S hS X U).appTop.hom r) = (chartToBase B S hS X V).appTop.hom r
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h2

/-! ### Restriction of sections is linear over the functions on the base -/

/-- **Restriction of sections along a morphism of étale charts is `Γ(S, ⊤)`-linear**, for the
actions by restriction of scalars along the structure morphisms of the two charts. -/
theorem chartRestrictLinear_smul_base (M : Modules.{u, m} B S hS X.1 X.2)
    {U V : SmallEtale B S hS X.1} (φ : V ⟶ U) (r : Γ(S, ⊤)) (x : M.val.obj (op U)) :
    letI : Module Γ(S, ⊤) (M.val.obj (op U) : Type m) :=
      Module.compHom _ (chartToBaseRingHom B S hS X U)
    letI : Module Γ(S, ⊤) (M.val.obj (op V) : Type m) :=
      Module.compHom _ (chartToBaseRingHom B S hS X V)
    chartRestrictLinear M φ (r • x) = r • chartRestrictLinear M φ x := by
  let : Module Γ(S, ⊤) (M.val.obj (op U) : Type m) :=
    Module.compHom _ (chartToBaseRingHom B S hS X U)
  let : Module Γ(S, ⊤) (M.val.obj (op V) : Type m) :=
    Module.compHom _ (chartToBaseRingHom B S hS X V)
  change chartRestrictLinear M φ (chartToBaseRingHom B S hS X U r • x) =
    chartToBaseRingHom B S hS X V r • chartRestrictLinear M φ x
  rw [← chartRestrict_chartToBaseRingHom B S hS X φ r]
  exact M.val.map_smul φ.op _ x

/-- **Restriction of sections along a morphism of étale charts carries `J · M(U)` into
`J · M(V)`**, for an ideal `J` of the functions on the base. -/
theorem chartRestrictLinear_mem_smul_top (M : Modules.{u, m} B S hS X.1 X.2)
    {U V : SmallEtale B S hS X.1} (φ : V ⟶ U) (J : Ideal Γ(S, ⊤)) :
    letI : Module Γ(S, ⊤) (M.val.obj (op U) : Type m) :=
      Module.compHom _ (chartToBaseRingHom B S hS X U)
    letI : Module Γ(S, ⊤) (M.val.obj (op V) : Type m) :=
      Module.compHom _ (chartToBaseRingHom B S hS X V)
    ∀ {x : M.val.obj (op U)},
      x ∈ J • (⊤ : Submodule Γ(S, ⊤) (M.val.obj (op U) : Type m)) →
        chartRestrictLinear M φ x ∈
          J • (⊤ : Submodule Γ(S, ⊤) (M.val.obj (op V) : Type m)) := by
  let : Module Γ(S, ⊤) (M.val.obj (op U) : Type m) :=
    Module.compHom _ (chartToBaseRingHom B S hS X U)
  let : Module Γ(S, ⊤) (M.val.obj (op V) : Type m) :=
    Module.compHom _ (chartToBaseRingHom B S hS X V)
  intro x hx
  refine Submodule.smul_induction_on
    (p := fun y => chartRestrictLinear M φ y ∈
      J • (⊤ : Submodule Γ(S, ⊤) (M.val.obj (op V) : Type m))) hx (fun a ha y _ => ?_)
    (fun y z hy hz => ?_)
  · rw [chartRestrictLinear_smul_base B S hS X M φ a y]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact add_mem hy hz

/-! ### The transport of the ideal -/

/-- **An ideal of the functions on the base which annihilates the image of a map of modules over
an affine étale chart annihilates it over every affine étale chart over that one.**

The values of `u` over the smaller chart lie in the `𝒪_X(V)`-span of the restrictions of the
values over the larger one
(`AlgebraicGeometry.Space.val_app_mem_span_range_chartRestrictLinear`, which is where
cartesian-ness of the source enters), those restrictions lie in `J · N(V)`
(`AlgebraicGeometry.Space.chartRestrictLinear_mem_smul_top`), and `J · N(V)` is an
`𝒪_X(V)`-submodule (`Stacks.Flattening.smulTopOfTower`). -/
theorem val_app_mem_smul_top_of_forall_mem_smul_top {M N : Modules.{u, m} B S hS X.1 X.2}
    (hM : IsCartesianOnAffineCharts M) (u : M ⟶ N) {U V : SmallEtale B S hS X.1}
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (φ : V ⟶ U) (J : Ideal Γ(S, ⊤)) :
    letI : Module Γ(S, ⊤) (N.val.obj (op U) : Type m) :=
      Module.compHom _ (chartToBaseRingHom B S hS X U)
    letI : Module Γ(S, ⊤) (N.val.obj (op V) : Type m) :=
      Module.compHom _ (chartToBaseRingHom B S hS X V)
    (∀ z : M.val.obj (op U), u.val.app (op U) z ∈
        J • (⊤ : Submodule Γ(S, ⊤) (N.val.obj (op U) : Type m))) →
      ∀ x : M.val.obj (op V), u.val.app (op V) x ∈
        J • (⊤ : Submodule Γ(S, ⊤) (N.val.obj (op V) : Type m)) := by
  let := chartBaseAlgebra B S hS X V
  let : Module Γ(S, ⊤) (N.val.obj (op U) : Type m) :=
    Module.compHom _ (chartToBaseRingHom B S hS X U)
  let : Module Γ(S, ⊤) (N.val.obj (op V) : Type m) :=
    Module.compHom _ (chartToBaseRingHom B S hS X V)
  have htow := isScalarTower_chartRing_sections B S hS X N V
  intro h x
  have hle : Submodule.span (chartRing B S hS X.1 X.2 V)
      (Set.range fun z : M.val.obj (op U) =>
        chartRestrictLinear N φ (u.val.app (op U) z)) ≤
      Stacks.Flattening.smulTopOfTower (A := chartRing B S hS X.1 X.2 V) J
        (N.val.obj (op V) : Type m) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨z, rfl⟩
    exact chartRestrictLinear_mem_smul_top B S hS X N φ J (h z)
  exact hle (val_app_mem_span_range_chartRestrictLinear hM u hU hV φ x)

end AlgebraicGeometry.Space

end
