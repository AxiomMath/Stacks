module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGraphLift

/-!
# The morphism into a relative spectrum over a chart is natural in the scheme over the chart

`AlgebraicGeometry.Space.chartOverRelativeSpecLift` turns a scheme object `T` of the big fppf
category, presented over a chart `V` of `X` and over a space `Z` representable over `X`, into a
morphism `T ⟶ \underline{Spec}_{V}(A|_V)` over the chart. This file proves that the whole
construction is **natural in `T`**: precomposing the presentation with a morphism `u : T' ⟶ T` of
the site precomposes the morphism into the relative spectrum with `u`.

## Main results

* `AlgebraicGeometry.Space.chartGraphHom_comp`: **the graph morphism is natural in the scheme over
  the chart.**
* `AlgebraicGeometry.Space.chartGraphAlgebraMap_comp` and
  `AlgebraicGeometry.Space.chartOverAlgebraMap_comp`: the algebra maps the graph and an algebra
  over the base determine are natural in the same sense, the direct-image map of `u` appearing on
  the other side.
* `AlgebraicGeometry.Space.comp_chartRelativeSpecLift`: **the universal morphism into the relative
  spectrum over a chart is natural in the scheme over the chart**, for an arbitrary algebra map:
  the lift of `φ`, precomposed with a morphism `w` of schemes over the chart, is the lift of `φ`
  followed by the direct-image map of `w`.
* `AlgebraicGeometry.Space.chartOverRelativeSpecLift_comp_hom`: the two combined.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Naturality of the graph morphism -/

section Graph

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS} (p : Z ⟶ X)
    (hp : yoneda.relativelyRepresentable p.hom) (V : SmallEtale B S hS X.1)
    {T T' : BigFppfOver B S hS} (t : T ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (z : yoneda.obj T ⟶ Z.1)
    (hz : z ≫ p.hom = yoneda.map t ≫ V.obj.hom) (u : T' ⟶ T)

include hz in
/-- The presentation of `T'` over the chart and over `Z` obtained by precomposing the one of `T`
with a morphism `u : T' ⟶ T` of the site is again compatible over `X`. -/
theorem comp_hz : (yoneda.map u ≫ z) ≫ p.hom =
    yoneda.map (u ≫ t) ≫ V.obj.hom :=
  by rw [Category.assoc, hz, ← Category.assoc, ← yoneda.map_comp]

/-- **The graph morphism is natural in the scheme over the chart.**

For a morphism `u : T' ⟶ T` of the site the graph of the precomposed presentation of `T'` is `u`
followed by the graph of `T`. -/
theorem chartGraphHom_comp :
    chartGraphHom B S hS p hp V T' (u ≫ t) (yoneda.map u ≫ z)
        (comp_hz B S hS p V t z hz u) =
      u ≫ chartGraphHom B S hS p hp V T t z hz := by
  refine hp.hom_ext (g := V.obj.hom) ?_ ?_
  · refine (hp.lift_fst (yoneda.map u ≫ z) (u ≫ t) (comp_hz B S hS p V t z hz u)).trans ?_
    refine Eq.symm ?_
    refine ((congrArg (fun m ↦ m ≫ hp.fst V.obj.hom)
      (yoneda.map_comp u (chartGraphHom B S hS p hp V T t z hz))).trans
        (Category.assoc _ _ _)).trans ?_
    exact congrArg (fun m ↦ yoneda.map u ≫ m) (hp.lift_fst z t hz)
  · refine (hp.lift_snd (yoneda.map u ≫ z) (u ≫ t) (comp_hz B S hS p V t z hz u)).trans ?_
    exact Eq.symm ((Category.assoc _ _ _).trans
      (congrArg (fun m ↦ u ≫ m) (hp.lift_snd z t hz)))

/-- The scheme morphism underlying the graph is natural in the scheme over the chart. -/
theorem chartGraphSchemeHom_comp :
    chartGraphSchemeHom B S hS p hp V T' (u ≫ t) (yoneda.map u ≫ z)
        (comp_hz B S hS p V t z hz u) =
      (BigFppfOver.toScheme B S hS).map u ≫
        chartGraphSchemeHom B S hS p hp V T t z hz :=
  (congrArg (BigFppfOver.toScheme B S hS).map
      (chartGraphHom_comp B S hS p hp V t z hz u)).trans
    ((BigFppfOver.toScheme B S hS).map_comp u (chartGraphHom B S hS p hp V T t z hz))

/-- The morphism of schemes over the chart which a morphism `u : T' ⟶ T` of the site induces on
the presentations over the chart. -/
def chartOverSchemeHom :
    (Over.mk ((BigFppfOver.toScheme B S hS).map (u ≫ t)) : Over (chartScheme V)) ⟶
      Over.mk ((BigFppfOver.toScheme B S hS).map t) :=
  Over.homMk ((BigFppfOver.toScheme B S hS).map u)
    ((BigFppfOver.toScheme B S hS).map_comp u t).symm

/-- **The direct-image map of `AlgebraicGeometry.Space.chartOverSchemeHom`**, from the pushforward
algebra of `T` on the chart to that of `T'`. -/
def chartOverSchemePushforwardMap :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        ((BigFppfOver.toScheme B S hS).map t) ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        ((BigFppfOver.toScheme B S hS).map (u ≫ t)) :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
    (X := Over.mk ((BigFppfOver.toScheme B S hS).map (u ≫ t)))
    (Y := Over.mk ((BigFppfOver.toScheme B S hS).map t))
    (chartOverSchemeHom B S hS V t u)

/-- The graph, read as a morphism of schemes over the chart, is natural in the scheme over the
chart. -/
theorem chartGraphOverHom_comp :
    chartGraphOverHom B S hS p hp V T' (u ≫ t) (yoneda.map u ≫ z)
        (comp_hz B S hS p V t z hz u) =
      chartOverSchemeHom B S hS V t u ≫ chartGraphOverHom B S hS p hp V T t z hz :=
  Over.OverMorphism.ext (chartGraphSchemeHom_comp B S hS p hp V t z hz u)

/-- **The direct-image map of the graph is natural in the scheme over the chart**, the direct-image
map of `u` appearing on the other side. -/
theorem chartGraphPushforwardMap_comp :
    chartGraphPushforwardMap B S hS p hp V T' (u ≫ t) (yoneda.map u ≫ z)
        (comp_hz B S hS p V t z hz u) =
      chartGraphPushforwardMap B S hS p hp V T t z hz ≫
        chartOverSchemePushforwardMap B S hS V t u :=
  (congrArg (fun k : (Over.mk ((BigFppfOver.toScheme B S hS).map (u ≫ t)) :
        Over (chartScheme V)) ⟶
      Over.mk (smallBaseChangeSchemeProjection B S hS p hp V) ↦
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
      (X := Over.mk ((BigFppfOver.toScheme B S hS).map (u ≫ t)))
      (Y := Over.mk (smallBaseChangeSchemeProjection B S hS p hp V)) k)
      (chartGraphOverHom_comp B S hS p hp V t z hz u)).trans
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_comp
      (chartOverSchemeHom B S hS V t u) (chartGraphOverHom B S hS p hp V T t z hz))

/-- **The algebra map the graph carries is natural in the scheme over the chart.** -/
theorem chartGraphAlgebraMap_comp :
    chartGraphAlgebraMap B S hS p hp V T' (u ≫ t) (yoneda.map u ≫ z)
        (comp_hz B S hS p V t z hz u) =
      chartGraphAlgebraMap B S hS p hp V T t z hz ≫
        chartOverSchemePushforwardMap B S hS V t u :=
  by unfold chartGraphAlgebraMap; rw [chartGraphPushforwardMap_comp, Category.assoc]

end Graph

/-! ### Naturality of the universal morphism into the relative spectrum -/

section Lift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (V : SmallEtale B S hS X.1)
    {T T' : Scheme.{u}} (g : T ⟶ chartScheme V) (g' : T' ⟶ chartScheme V)
    (w : (Over.mk g' : Over (chartScheme V)) ⟶ Over.mk g)
    (φ : chartSchemeAlgebra B S hS X A V ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra g)

/-- **The universal morphism into the relative spectrum over a chart is natural in the scheme over
the chart.**

For a morphism `w : T' ⟶ T` of schemes over `chartScheme V` and a map
`φ : A|_{chartScheme V} ⟶ g_* 𝒪_T` of algebras on the chart, the morphism `T' ⟶ T` followed by
the lift of `φ` is the lift of `φ` followed by the direct-image map of `w`. -/
theorem comp_chartRelativeSpecLift :
    w ≫ chartRelativeSpecLift B S hS X A hA V g φ =
      chartRelativeSpecLift B S hS X A hA V g'
        (φ ≫ Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap w) := by
  refine chartRelativeSpecLift_ext B S hS X A hA V g' ?_
  refine (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_comp w
    (chartRelativeSpecLift B S hS X A hA V g φ)).trans ?_
  refine Eq.trans (congrArg
    (fun m ↦ m ≫ Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap w)
    (pushforwardAlgebraMap_chartRelativeSpecLift B S hS X A hA V g φ)) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (pushforwardAlgebraMap_chartRelativeSpecLift B S hS X A hA V g'
    (φ ≫ Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap w)).symm

end Lift

/-! ### Naturality of the morphism an algebra over the base determines -/

section Over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ X) (p : Z ⟶ X) (τ : Z ⟶ Y)
    (hτ : τ ≫ f = p) (hp : yoneda.relativelyRepresentable p.hom)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (ι : A ⟶ pushforwardAlgebra B S hS (Over.mk f))
    (V : SmallEtale B S hS X.1) {T T' : BigFppfOver B S hS}
    (t : T ⟶ (SmallEtale.toOver B S hS X.1).obj V) (z : yoneda.obj T ⟶ Z.1)
    (hz : z ≫ p.hom = yoneda.map t ≫ V.obj.hom) (u : T' ⟶ T)

/-- **The algebra map on the chart which an algebra over the base determines is natural in the
scheme over the chart.** -/
theorem chartOverAlgebraMap_comp :
    chartOverAlgebraMap B S hS f p τ hτ hp A ι V T' (u ≫ t) (yoneda.map u ≫ z)
        (comp_hz B S hS p V t z hz u) =
      chartOverAlgebraMap B S hS f p τ hτ hp A ι V T t z hz ≫
        chartOverSchemePushforwardMap B S hS V t u :=
  by
    unfold chartOverAlgebraMap
    rw [chartGraphAlgebraMap_comp B S hS p hp V t z hz u]
    exact (Category.assoc _ _ _).symm

variable (hA : A.IsQuasicoherent)

/-- **The morphism into the relative spectrum over a chart which an algebra over the base
determines is natural in the scheme over the chart.** -/
theorem chartOverRelativeSpecLift_comp_hom :
    chartOverSchemeHom B S hS V t u ≫
        chartOverRelativeSpecLift B S hS f p τ hτ hp A ι V T t z hz hA =
      chartOverRelativeSpecLift B S hS f p τ hτ hp A ι V T' (u ≫ t) (yoneda.map u ≫ z)
        (comp_hz B S hS p V t z hz u) hA :=
  (comp_chartRelativeSpecLift B S hS X A hA V
      ((BigFppfOver.toScheme B S hS).map t)
      ((BigFppfOver.toScheme B S hS).map (u ≫ t))
      (chartOverSchemeHom B S hS V t u)
      (chartOverAlgebraMap B S hS f p τ hτ hp A ι V T t z hz)).trans
    (congrArg (chartRelativeSpecLift B S hS X A hA V
        ((BigFppfOver.toScheme B S hS).map (u ≫ t)))
      (chartOverAlgebraMap_comp B S hS f p τ hτ hp A ι V t z hz u).symm)

end Over

end AlgebraicGeometry.Space

end
