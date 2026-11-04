module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAlgebraSheafDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotientChartIndependence

/-!
# The atlas of the relative spectrum over the charts over the base chart

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `ν : X' = \underline{Spec}_X(A) ⟶ X` be the
relative spectrum built, in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecQuotient`, as the quotient of the
relation of a pair `pr₁, pr₂ : V' ⟶ V₂` of étale charts with `V₂ ⟶ X` surjective.

`AlgebraicGeometry.Space.chartRelativeSpecQuotientChartAtlas` is the atlas of `X'` at a chart
`W` of `X` *together with* a morphism of charts `W ⟶ V₂`:
`\underline{Spec}_{W}(A|_{W}) ⟶ \underline{Spec}_{V₂}(A|_{V₂}) ⟶ X'`.  This file removes the
morphism from the data.  By
`AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp_quotientChart` any two morphisms
`W ⟶ V₂` give the same composite, so the atlas is attached to the *object* `W` of the full
subcategory `AlgebraicGeometry.Space.ChartOver` of charts admitting a morphism to `V₂` — which
is exactly the subcategory the descent of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartAlgebraSheafDescent` is performed over — and it is
then *functorial* on that subcategory.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecAtlasOver`: the atlas of `X'` at an object of
  `AlgebraicGeometry.Space.ChartOver`, with no morphism to `V₂` in the data.

## Main results

* `AlgebraicGeometry.Space.chartRelativeSpecAtlasOver_eq`: it is the atlas at *every* morphism
  of charts to `V₂`, so the choice made in its definition is immaterial.
* `AlgebraicGeometry.Space.isPullback_chartRelativeSpecAtlasOver`: **the cartesian square at a
  chart over `V₂`**, `\underline{Spec}_{W}(A|_{W}) = X' ×_X W`, choice-free.
* `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp_chartRelativeSpecAtlasOver`:
  **functoriality** — the atlas at `W` is the morphism of relative spectra over a morphism
  `W ⟶ W₂` of charts over `V₂` followed by the atlas at `W₂`.

## Implementation notes

**Why the choice is harmless, and why that is the whole content.**  The atlas at a morphism
`m : W ⟶ V₂` is `\underline{Spec}(m)` followed by the chart of the quotient sheaf, and the
quotient is formed by the relation of `pr₁, pr₂`, whose two projections the chart identifies.
Two morphisms `a, b : W ⟶ V₂` are morphisms *over `X`*, so the kernel-pair hypothesis `hsq`
factors the pair `(a, b)` through `V' = V₂ ×_X V₂`
(`AlgebraicGeometry.Space.chartRelationLift`), after which the two composites agree.  That is
`AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp_quotientChart`, which was already
available; the three statements here are its consequences for the full subcategory of charts
over `V₂`, and they carry no new geometry.

**What this is for.**  Clause (2) of Definition 0822 — that `ν_* 𝒪_{X'}` is `A` — is the
cartesian square read through `AlgebraicGeometry.Space.pushforwardAlgebraChartIso`, which
identifies the sections of `ν_* 𝒪_{X'}` over a chart `W` with the regular functions on
`W ×_X X'`.  The square supplies those for a chart over `V₂`, and
`StacksFrontier.AlgebraicGeometry.Spaces.ChartAlgebraSheafDescent` descends a morphism of sheaves
of algebras from the charts over `V₂` to the whole small étale site; what the descent consumes
is a *natural transformation* on that subcategory, and this file supplies the naturality of the
geometric half of it.  What is still owed before clause (2) follows is recorded in the
implementation notes of `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn`.

**No `stacks` attribute is carried.**  Nothing here is a clause of 081V or of 0822: the
relative spectrum, its affineness and the cartesian square are registered, or recorded as open,
where they are proved.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))
    (W : ChartOver B S hS X.1 V₂)
    (hW : B.Contains (chartRelativeSpec B S hS X A hA W.obj))

/-- **The atlas of `X' = \underline{Spec}_X(A)` at a chart over `V₂`.**  For an object `W` of
the full subcategory `AlgebraicGeometry.Space.ChartOver` of charts admitting a morphism to the
chart `V₂` the quotient was built at, this is the atlas
`AlgebraicGeometry.Space.chartRelativeSpecQuotientChartAtlas` at a chosen such morphism.

`AlgebraicGeometry.Space.chartRelativeSpecAtlasOver_eq` shows the choice is immaterial. -/
def chartRelativeSpecAtlasOver :
    yoneda.obj (chartRelativeSpecSite B S hS X A hA W.obj hW) ⟶
      chartRelativeSpecQuotientPresheaf B S hS X A hA pr₁ pr₂ hV' hV₂ :=
  chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW
    (chartOverBaseHom B S hS X.1 V₂ W)

include hsq in
/-- **The atlas at a chart over `V₂` is the atlas at every morphism of charts to `V₂`.**  This is
`AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp_quotientChart`: the relation the quotient
is taken by identifies any two morphisms `W ⟶ V₂`. -/
theorem chartRelativeSpecAtlasOver_eq (m : W.obj ⟶ V₂) :
    chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W hW =
      chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW m :=
  chartRelativeSpecSiteMap_comp_quotientChart B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hW
    (chartOverBaseHom B S hS X.1 V₂ W) m

include hsq hsurj hV'' in
/-- **The relative spectrum of `A` over a chart over `V₂` is the fibre product of `ν` and that
chart**: `\underline{Spec}_{W}(A|_{W}) = X' ×_X W`, with no choice of a morphism `W ⟶ V₂` in the
statement.

It is `AlgebraicGeometry.Space.isPullback_chartRelativeSpecQuotientChartAtlas` read through
`AlgebraicGeometry.Space.chartRelativeSpecAtlasOver_eq`. -/
theorem isPullback_chartRelativeSpecAtlasOver :
    IsPullback (chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W hW)
      (yoneda.map (chartRelativeSpecSiteToChart B S hS X A hA W.obj hW))
      (chartRelativeSpecQuotientHom B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'').hom
      W.obj.obj.hom := by
  exact isPullback_chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hsq hsurj hV' hV₂
    hV'' hW (chartOverBaseHom B S hS X.1 V₂ W)

include hsq in
/-- **The atlas of `X'` is functorial on the charts over `V₂`**: for a morphism `k : W ⟶ W₂` of
charts over `V₂`, the morphism of relative spectra over `k` followed by the atlas at `W₂` is the
atlas at `W`.

With `AlgebraicGeometry.Space.isPullback_chartRelativeSpecAtlasOver` this exhibits
`W ↦ \underline{Spec}_{W}(A|_{W})`, over the charts over `V₂`, as the base change of `ν` along
the chart — naturally in `W`, which is what a descent along the inclusion of that subcategory
consumes. -/
theorem chartRelativeSpecSiteMap_comp_chartRelativeSpecAtlasOver
    (W₂ : ChartOver B S hS X.1 V₂)
    (hW₂ : B.Contains (chartRelativeSpec B S hS X A hA W₂.obj)) (k : W ⟶ W₂) :
    yoneda.map (chartRelativeSpecSiteMap B S hS X A hA k.hom hW hW₂) ≫
        chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W₂ hW₂ =
      chartRelativeSpecAtlasOver B S hS X A hA pr₁ pr₂ hV' hV₂ W hW := by
  rw [chartRelativeSpecAtlasOver_eq B S hS X A hA pr₁ pr₂ hsq hV' hV₂ W hW
      (k.hom ≫ chartOverBaseHom B S hS X.1 V₂ W₂),
    show chartRelativeSpecQuotientChartAtlas B S hS X A hA pr₁ pr₂ hV' hV₂ hW
        (k.hom ≫ chartOverBaseHom B S hS X.1 V₂ W₂) =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
          (k.hom ≫ chartOverBaseHom B S hS X.1 V₂ W₂) hW hV₂) ≫
        Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (chartRelativeSpecSite B S hS X A hA V₂ hV₂)
          (relation B S hS (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
            (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) from rfl,
    chartRelativeSpecSiteMap_comp B S hS X A hA hW hW₂ hV₂ k.hom
      (chartOverBaseHom B S hS X.1 V₂ W₂), CategoryTheory.Functor.map_comp, Category.assoc,
    chartRelativeSpecAtlasOver_eq B S hS X A hA pr₁ pr₂ hsq hV' hV₂ W₂ hW₂
      (chartOverBaseHom B S hS X.1 V₂ W₂)]
  rfl

end AlgebraicGeometry.Space

end
