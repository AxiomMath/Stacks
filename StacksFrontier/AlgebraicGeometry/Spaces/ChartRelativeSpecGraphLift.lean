module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecLiftChartChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeDirectImageAlgebraPushforward

/-!
# The morphism into a relative spectrum over a chart attached to an algebra over the base

Let `X` be an algebraic space over `S`, `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras
and `f : Y ⟶ X` a morphism of algebraic spaces together with a map `A ⟶ f_* 𝒪_Y` of algebras —
for the normalization of `X` in `Y` this is the inclusion `𝒪' ⊂ f_* 𝒪_Y` of the integral closure.
Clause (1) of Definition 0822 asks for a factorization of `f` through
`ν : X' = \underline{Spec}_X(A) ⟶ X`, and since `f` is not representable the morphism to `X'` has
to be built on a *scheme* `T` which is étale over `Y` and lies over an étale scheme chart `V` of
`X`.

This file performs that step: it builds the **graph morphism** and the algebra map it carries,
and feeds them to `AlgebraicGeometry.Space.chartRelativeSpecLift`.

## Main definitions

* `AlgebraicGeometry.Space.chartGraphHom`: for a representable `p : Z ⟶ X`, a scheme object `T`
  of the site over the chart `V` and a morphism `yoneda.obj T ⟶ Z.1` over `X`, the graph
  `T ⟶ V ×_X Z` over the chart.  It is the lift of the representability witness at the two legs
  the data provides, so the triangle
  `AlgebraicGeometry.Space.chartGraphSchemeHom_comp_smallBaseChangeSchemeProjection` is its
  defining property.
* `AlgebraicGeometry.Space.chartGraphAlgebraMap`: the resulting map of algebras on the chart
  `p_* 𝒪_Z|_{chartScheme V} ⟶ (T ⟶ chartScheme V)_* 𝒪_T`, namely
  `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso` — Stacks 03G8 for a
  representable morphism, read on the Zariski site of the chart — followed by the direct-image
  map of the graph.
* `AlgebraicGeometry.Space.chartOverAlgebraMap`: the composite an algebra over the base
  determines, `A|_{chartScheme V} ⟶ (T ⟶ chartScheme V)_* 𝒪_T`: the chart restriction of the
  given `A ⟶ f_* 𝒪_Y`, the chart restriction of the direct-image map of `T ⟶ Y` over `X`, and
  `AlgebraicGeometry.Space.chartGraphAlgebraMap`.
* `AlgebraicGeometry.Space.chartOverRelativeSpecLift`: the morphism
  `T ⟶ \underline{Spec}_{V}(A|_V)` over the chart which that algebra map induces.

## Main results

* `AlgebraicGeometry.Space.chartOverRelativeSpecLift_comp`: the morphism lies over the chart.
* `AlgebraicGeometry.Space.pushforwardAlgebraMap_chartOverRelativeSpecLift`: its algebra map is
  the one it was built from.
* `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_chartOverAlgebraMap`: **the chart change of
  the algebra map changes only its third factor.**  Along a morphism `h : V ⟶ V₂` of charts the
  first two factors come back unchanged as the chart restriction of the same map of algebra
  sheaves at `V₂`, by naturality of the chart comparison in the algebra sheaf
  (`AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_naturality`), and what is left is the chart
  change of `AlgebraicGeometry.Space.chartGraphAlgebraMap`.

## Implementation notes

**Why the graph morphism is needed.**
`AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso` identifies the chart
restriction of `p_* 𝒪_Z` with the direct image along the *cartesian projection*
`q : V ×_X Z ⟶ chartScheme V`, and `V ×_X Z` is not `T`: what the universal property of the
relative spectrum over the chart consumes is a map into `(T ⟶ chartScheme V)_* 𝒪_T`.  The two are
bridged by the graph of the data — `T` lies over `V` by `t` and over `Z` by `z`, so it lies over
the fibre product — and by `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap` of it.

**The graph is exhibited, not chosen.**  `CategoryTheory.Functor.relativelyRepresentable.lift`
produces it from the two legs, and
`CategoryTheory.Functor.relativelyRepresentable.lift_snd` is the triangle over the chart.  No
uniqueness is needed here: it is the *existence* of the morphism over the chart that the lift
consumes, and the uniqueness that matters later is the rigidity of the relative spectrum, which
is `AlgebraicGeometry.Space.chartRelativeSpecLift_ext`.

**`T` is a scheme of the site, and the space it spans is representable over `X`.**  The
hypothesis `hp` is representability of `p`, which for `p` out of a representable space is
`CategoryTheory.Functor.relativelyRepresentable.map` at `yoneda`.  It is kept as a hypothesis
rather than derived, so that the construction applies to any representable `p` and in
particular to `ν`.

The morphism built here lives on a chart of `Y`: to give clause (1) of Definition 0822 it is to
be descended both through the relation of that chart over `Y` and through the quotient defining
`X'`.

## References

* [Stacks Project, Tag 02W9](https://stacks.math.columbia.edu/tag/02W9)
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

section Graph

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS} (p : Z ⟶ X)
    (hp : yoneda.relativelyRepresentable p.hom) (V : SmallEtale B S hS X.1)
    (T : BigFppfOver B S hS) (t : T ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (z : yoneda.obj T ⟶ Z.1)
    (hz : z ≫ p.hom = yoneda.map t ≫ V.obj.hom)

/-- **The graph morphism `T ⟶ V ×_X Z`.**  The scheme object `T` of the site lies over the chart
`V` by `t` and over `Z` by `z`, and the two agree over `X`, so it lies over the fibre product
`V ×_X Z` — which is the base-changed chart
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2 (4). -/
def chartGraphHom : T ⟶ (SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS p hp).obj V) :=
  hp.lift z t hz

/-- The graph morphism, read on the underlying schemes. -/
def chartGraphSchemeHom :
    (BigFppfOver.toScheme B S hS).obj T ⟶
      chartScheme ((smallBaseChange B S hS p hp).obj V) :=
  (BigFppfOver.toScheme B S hS).map (chartGraphHom B S hS p hp V T t z hz)

/-- **The defining property of the graph: it lies over the chart.**  Composed with the cartesian
projection `V ×_X Z ⟶ V` it is the morphism `T ⟶ V` the data provides. -/
theorem chartGraphSchemeHom_comp_smallBaseChangeSchemeProjection :
    chartGraphSchemeHom B S hS p hp V T t z hz ≫
        smallBaseChangeSchemeProjection B S hS p hp V =
      (BigFppfOver.toScheme B S hS).map t :=
  Eq.trans ((BigFppfOver.toScheme B S hS).map_comp _ _).symm
    (congrArg (BigFppfOver.toScheme B S hS).map (hp.lift_snd z t hz))

/-- The graph morphism as a morphism of schemes over `chartScheme V`. -/
def chartGraphOverHom :
    (Over.mk ((BigFppfOver.toScheme B S hS).map t) : Over (chartScheme V)) ⟶
      Over.mk (smallBaseChangeSchemeProjection B S hS p hp V) :=
  Over.homMk (chartGraphSchemeHom B S hS p hp V T t z hz)
    (chartGraphSchemeHom_comp_smallBaseChangeSchemeProjection B S hS p hp V T t z hz)

/-- **The direct-image map of the graph morphism**, with the spellings of its two ends fixed by
the type ascription.

`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap` writes its two ends through
`CategoryTheory.Over.mk` and the projection out of it, while
`AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso` writes the same object
directly.  The two objects over the chart are passed explicitly as `X` and `Y`: left to the
unifier, they would be solved from `?Y.hom =?= smallBaseChangeSchemeProjection …`, whose
unfolding descends through the `Classical.choice` inside the representability witness `hp.snd`. -/
def chartGraphPushforwardMap :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V) ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        ((BigFppfOver.toScheme B S hS).map t) :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
    (X := Over.mk ((BigFppfOver.toScheme B S hS).map t))
    (Y := Over.mk (smallBaseChangeSchemeProjection B S hS p hp V))
    (chartGraphOverHom B S hS p hp V T t z hz)

/-- **The algebra map the graph carries**: the chart restriction of `p_* 𝒪_Z` maps to the direct
image of `𝒪_T` along `T ⟶ chartScheme V`.

It is `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso` — Stacks 03G8 for the
representable `p`, read on the Zariski site of the chart, where the chart restriction of `p_* 𝒪_Z`
is the direct image along the cartesian projection `V ×_X Z ⟶ V` — followed by
`AlgebraicGeometry.Space.chartGraphPushforwardMap`. -/
def chartGraphAlgebraMap :
    chartSchemeDirectImageAlgebra B S hS X (Over.mk p) V ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        ((BigFppfOver.toScheme B S hS).map t) :=
  (chartSchemeDirectImageAlgebraPushforwardIso B S hS p hp V).hom ≫
    chartGraphPushforwardMap B S hS p hp V T t z hz

end Graph

section Over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ X) (p : Z ⟶ X) (τ : Z ⟶ Y)
    (hτ : τ ≫ f = p) (hp : yoneda.relativelyRepresentable p.hom)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (ι : A ⟶ pushforwardAlgebra B S hS (Over.mk f))
    (V : SmallEtale B S hS X.1) (T : BigFppfOver B S hS)
    (t : T ⟶ (SmallEtale.toOver B S hS X.1).obj V) (z : yoneda.obj T ⟶ Z.1)
    (hz : z ≫ p.hom = yoneda.map t ≫ V.obj.hom)

/-- The morphism `Z ⟶ Y` as a morphism of algebraic spaces over `X`. -/
def overHomOfFactorization : (Over.mk p : Over X) ⟶ Over.mk f :=
  Over.homMk τ hτ

/-- **The algebra map on the chart that an algebra over the base determines.**

For an algebra `A` on `X` with a map `ι : A ⟶ f_* 𝒪_Y`, a space `Z` over `X` factoring through
`Y`, and a scheme object `T` of the site presenting `Z` over the chart `V`, this is the composite
of three maps of algebras on the Zariski site of `chartScheme V`: the chart restriction of `ι`,
the chart restriction of the direct-image map of `Z ⟶ Y` over `X`, and
`AlgebraicGeometry.Space.chartGraphAlgebraMap`. -/
def chartOverAlgebraMap :
    chartSchemeAlgebra B S hS X A V ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        ((BigFppfOver.toScheme B S hS).map t) :=
  (chartSchemeAlgebraFunctor B S hS X V).map
      (ι ≫ pushforwardAlgebraMap B S hS
        (overHomOfFactorization B S hS f p τ hτ)) ≫
    chartGraphAlgebraMap B S hS p hp V T t z hz

/-- **The chart change of the algebra map an algebra over the base determines keeps its first
two factors and changes only the third.**

For a morphism `h : V ⟶ V₂` of étale scheme charts of `X`, the chart change
`AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap` of
`AlgebraicGeometry.Space.chartOverAlgebraMap` at `V` is the chart restriction at `V₂` of the same
map `A ⟶ p_* 𝒪_Z` of algebras on `X`, followed by the chart change of
`AlgebraicGeometry.Space.chartGraphAlgebraMap`.

This is `AlgebraicGeometry.Space.chartSchemeAlgebraLiftMap_naturality` at the algebra map
`ι ≫ (Z ⟶ Y)_*`, the chart restriction of `f_* 𝒪_Y` to a chart being the chart restriction of an
algebra sheaf on `X` and nothing else. -/
theorem chartSchemeAlgebraLiftMap_chartOverAlgebraMap {V₂ : SmallEtale B S hS X.1} (h : V ⟶ V₂) :
    chartSchemeAlgebraLiftMap B S hS X A h ((BigFppfOver.toScheme B S hS).map t)
        (chartOverAlgebraMap B S hS f p τ hτ hp A ι V T t z hz) =
      (chartSchemeAlgebraFunctor B S hS X V₂).map
          (ι ≫ pushforwardAlgebraMap B S hS (overHomOfFactorization B S hS f p τ hτ)) ≫
        chartSchemeAlgebraLiftMap B S hS X (pushforwardAlgebra B S hS (Over.mk p)) h
          ((BigFppfOver.toScheme B S hS).map t)
          (chartGraphAlgebraMap B S hS p hp V T t z hz) :=
  (chartSchemeAlgebraLiftMap_naturality B S hS X
    (ι ≫ pushforwardAlgebraMap B S hS (overHomOfFactorization B S hS f p τ hτ)) h
    ((BigFppfOver.toScheme B S hS).map t)
    (chartGraphAlgebraMap B S hS p hp V T t z hz)).symm

variable (hA : A.IsQuasicoherent)

/-- **The morphism `T ⟶ \underline{Spec}_{V}(A|_V)` over the chart which the algebra map
determines.**  This is Stacks 081X at a chart,
`AlgebraicGeometry.Space.chartRelativeSpecLift`, applied to
`AlgebraicGeometry.Space.chartOverAlgebraMap`. -/
def chartOverRelativeSpecLift :
    (Over.mk ((BigFppfOver.toScheme B S hS).map t) : Over (chartScheme V)) ⟶
      Over.mk (chartRelativeSpecToChart B S hS X A hA V) :=
  chartRelativeSpecLift B S hS X A hA V ((BigFppfOver.toScheme B S hS).map t)
    (chartOverAlgebraMap B S hS f p τ hτ hp A ι V T t z hz)

/-- The morphism into the relative spectrum over the chart lies over the chart. -/
theorem chartOverRelativeSpecLift_comp :
    (chartOverRelativeSpecLift B S hS f p τ hτ hp A ι V T t z hz hA).left ≫
        chartRelativeSpecToChart B S hS X A hA V =
      (BigFppfOver.toScheme B S hS).map t :=
  Over.w _

/-- The algebra map which the morphism of
`AlgebraicGeometry.Space.chartOverRelativeSpecLift` induces is the one it was built from, read
through the identification `AlgebraicGeometry.Space.chartRelativeSpecPushforwardIso`. -/
theorem pushforwardAlgebraMap_chartOverRelativeSpecLift :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (chartOverRelativeSpecLift B S hS f p τ hτ hp A ι V T t z hz hA) =
      (chartRelativeSpecPushforwardIso B S hS X A hA V).hom ≫
        chartOverAlgebraMap B S hS f p τ hτ hp A ι V T t z hz :=
  pushforwardAlgebraMap_chartRelativeSpecLift B S hS X A hA V _ _

end Over

end AlgebraicGeometry.Space

end
