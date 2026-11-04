module

public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections

/-!
# The scalar towers over the ring of functions of the base

Let `X` be an algebraic space over a scheme `S` in a big fppf site, let `A` be an étale scheme
chart of `X` and let `M` be an `𝒪_X`-module. The sections `M(A)` are a module over the ring
`𝒪_X(A)` of functions of the chart, and the chart has a structure morphism to `S`, so they are
also a module over `Γ(S, ⊤)` by restriction of scalars. These two actions form a scalar tower,
and so do the two actions on the ring of functions of the chart of the source of a diagram of
étale charts.

## Main definitions

* `AlgebraicGeometry.Space.chartToSiteRingHom` and `.chartSiteAlgebra`: pullback of functions
  along a morphism from an étale chart of `X` to an *object* `Y₀` of the big fppf category over
  `S`, and the `Γ(Y₀, ⊤)`-algebra structure it gives on the ring of functions of the chart.
  `AlgebraicGeometry.Space.chartToBaseRingHom` and `.chartBaseAlgebra` are these at the final
  object, where `Γ(Y₀, ⊤)` is `Γ(S, ⊤)`.

## Main results

* `AlgebraicGeometry.Space.isScalarTower_chartRing_sections`: the tower on the sections of a
  module over a chart.
* `AlgebraicGeometry.Space.isScalarTower_chartDiagram`: the tower on the ring of functions of
  the chart of the source of a diagram of étale charts, whose `𝒪_Y(d.V)`-action is
  `AlgebraicGeometry.Space.chartDiagramAlgebra`.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullback of functions along a morphism from an étale scheme chart of `X` to an object `Y₀` of
the big fppf category over `S`, as a ring map from the ring of functions of `Y₀` to the ring of
functions `AlgebraicGeometry.Space.chartRing` of the chart. -/
def chartToSiteRingHom (X : AlgebraicSpaces B S hS) {Y₀ : BigFppfOver B S hS}
    (A : SmallEtale B S hS X.1) (α : chartFppfObject B S hS X A ⟶ Y₀) :
    (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u) →+* chartRing B S hS X.1 X.2 A :=
  ((BigFppfOver.toScheme B S hS).map α).appTop.hom

/-- The `Γ(Y₀, ⊤)`-algebra structure on the ring of functions of an étale scheme chart equipped
with a morphism to an object `Y₀` of the site. -/
@[instance_reducible]
def chartSiteAlgebra (X : AlgebraicSpaces B S hS) {Y₀ : BigFppfOver B S hS}
    (A : SmallEtale B S hS X.1) (α : chartFppfObject B S hS X A ⟶ Y₀) :
    Algebra (Γ((BigFppfOver.toScheme B S hS).obj Y₀, ⊤) : Type u)
      (chartRing B S hS X.1 X.2 A) :=
  (chartToSiteRingHom B S hS X A α).toAlgebra

/-- Pullback of functions along the structure morphism of an étale scheme chart to the base:
`AlgebraicGeometry.Space.chartToSiteRingHom` along the vertical morphism of
`AlgebraicGeometry.Space.baseChartDiagram`. -/
def chartToBaseRingHom (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1) :
    Γ(S, ⊤) →+* chartRing B S hS X.1 X.2 A :=
  chartToSiteRingHom B S hS X A (baseChartDiagram B S hS X A).g

/-- The `Γ(S, ⊤)`-algebra structure on the ring of functions of an étale scheme chart, given by
the structure morphism of the chart to the base. -/
@[instance_reducible]
def chartBaseAlgebra (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1) :
    Algebra Γ(S, ⊤) (chartRing B S hS X.1 X.2 A) :=
  (chartToBaseRingHom B S hS X A).toAlgebra

/-- The actions of `Γ(S, ⊤)` and of the ring of functions of a chart on the sections of a module
over that chart form a scalar tower. -/
theorem isScalarTower_chartRing_sections (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, m} B S hS X.1 X.2) (A : SmallEtale B S hS X.1) :
    letI := chartBaseAlgebra B S hS X A
    letI : Module Γ(S, ⊤) (M.val.obj (op A)) :=
      Module.compHom _ (chartToBaseRingHom B S hS X A)
    IsScalarTower Γ(S, ⊤) (chartRing B S hS X.1 X.2 A) (M.val.obj (op A)) := by
  let := chartBaseAlgebra B S hS X A
  let : Module Γ(S, ⊤) (M.val.obj (op A)) :=
    Module.compHom _ (chartToBaseRingHom B S hS X A)
  exact ⟨fun r a x ↦ mul_smul (chartToBaseRingHom B S hS X A r) a x⟩

variable {X Y : AlgebraicSpaces B S hS}

/-- The vertical morphism of a diagram of étale charts is a morphism over the base: the
structure morphism of the chart of the source to the base factors through that of the chart of
the target. -/
theorem chartToBase_comp_chartDiagram (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (BigFppfOver.toScheme B S hS).map d.g ≫ chartToBase B S hS Y d.V =
      chartToBase B S hS X d.U := by
  rw [chartToBase_eq, chartToBase_eq]
  exact (Functor.map_comp B.inclusion d.g.left (chartFppfObject B S hS Y d.V).hom).symm.trans
    (congrArg B.inclusion.map (Over.w d.g))

/-- Pullback of functions along the vertical morphism of a diagram of étale charts is pullback
of functions along the underlying morphism of schemes. -/
theorem chartDiagramRestrict_apply (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (a : chartRing B S hS Y.1 Y.2 d.V) :
    chartDiagramRestrict B S hS f d a =
      ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom a := rfl

/-- The actions of `Γ(S, ⊤)` and of the ring of functions of the chart of the target on the ring
of functions of the chart of the source of a diagram of étale charts form a scalar tower. -/
theorem isScalarTower_chartDiagram (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartBaseAlgebra B S hS Y d.V
    letI := chartBaseAlgebra B S hS X d.U
    letI := chartDiagramAlgebra B S hS f d
    IsScalarTower Γ(S, ⊤) (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS X.1 X.2 d.U) := by
  let := chartBaseAlgebra B S hS Y d.V
  let := chartBaseAlgebra B S hS X d.U
  let := chartDiagramAlgebra B S hS f d
  refine ⟨fun r a c ↦ ?_⟩
  have hcomp : chartDiagramRestrict B S hS f d (chartToBaseRingHom B S hS Y d.V r) =
      chartToBaseRingHom B S hS X d.U r := by
    have h := chartToBase_comp_chartDiagram B S hS f d
    have h2 := congrArg (fun k : chartScheme d.U ⟶ S => k.appTop.hom r) h
    show ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom
      ((chartToBase B S hS Y d.V).appTop.hom r) = (chartToBase B S hS X d.U).appTop.hom r
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h2
  show chartDiagramRestrict B S hS f d (chartToBaseRingHom B S hS Y d.V r * a) * c =
    chartToBaseRingHom B S hS X d.U r * (chartDiagramRestrict B S hS f d a * c)
  rw [map_mul, hcomp, mul_assoc]

end AlgebraicGeometry.Space

end
