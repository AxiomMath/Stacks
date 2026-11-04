module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecMapIso
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebraRelativeSpec
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleBaseChangeIso

/-!
# Chart functoriality of the relative spectrum of an algebra on an algebraic space

Let `X` be an algebraic space, `A` a quasi-coherent sheaf of commutative `𝒪_X`-algebras on its
small étale site and `h : V' ⟶ V` a morphism of étale scheme charts of `X`.
`AlgebraicGeometry.Space.chartRelativeSpec` forms the scheme
`\underline{Spec}_{chartScheme V}(A|_V)` over each chart, and this file makes that construction
**functorial in the chart**: there is a canonical morphism of schemes

`\underline{Spec}_{V'}(A|_{V'}) ⟶ \underline{Spec}_{V}(A|_V)`

over `chartSchemeMap h`, and the resulting square is a fibre-product square.

These are the morphisms the atlas construction of Stacks 081V reads as an étale equivalence
relation: taking `U ⟶ X` a surjective étale scheme chart and `R = U ×_X U` with its two
projections `s, t : R ⟶ U`, the two morphisms
`\underline{Spec}_{R}(A|_R) ⟶ \underline{Spec}_{U}(A|_U)` built here are the source and target
of the relation whose quotient by Stacks 02WW is `\underline{Spec}_X(A)`.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecBaseChangeHom`: **the comparison, over
  `chartScheme V'`, of the relative spectrum over the smaller chart with the base change along
  `chartSchemeMap h` of the relative spectrum over the larger one.**  It carries no hypothesis
  beyond quasi-coherence of `A`.
* `AlgebraicGeometry.Space.chartRelativeSpecChartMap`: the induced morphism of schemes
  `\underline{Spec}_{V'}(A|_{V'}) ⟶ \underline{Spec}_{V}(A|_V)`.
* `AlgebraicGeometry.Space.chartRelativeSpecBaseChangeIso`: the comparison as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.chartRelativeSpecChartMap_comp_chartRelativeSpecToChart` and
  `AlgebraicGeometry.Space.commSq_chartRelativeSpecChartMap`: the square over `chartSchemeMap h`
  commutes.  Unconditional.
* `AlgebraicGeometry.Space.isIso_chartRelativeSpecBaseChangeHom`: the comparison is invertible.
* `AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap`: **the square is a fibre
  product** — the relative spectrum over the smaller chart is the base change along
  `chartSchemeMap h` of the relative spectrum over the larger one.
* `AlgebraicGeometry.Space.chartRelativeSpecChartMap_of_isStableUnderBaseChange`: consequently
  the induced morphism of relative spectra inherits every base-change-stable property of
  `chartSchemeMap h` — in particular it is étale, or surjective, whenever the morphism of chart
  schemes is.  This is the form the étale equivalence relation of Stacks 081V consumes.

## Implementation notes

**The morphism is unconditional; only the fibre-product property is not.**  The relative
spectrum is contravariant in the algebra, and
`AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom` is a morphism
`(chartSchemeMap h)^*(A|_V) ⟶ A|_{V'}` of algebras on `chartScheme V'`, so
`AlgebraicGeometry.relativeSpecMapOfAlgebraHom` turns it into a morphism of relative spectra
over `chartScheme V'` out of `\underline{Spec}_{V'}(A|_{V'})`; composing with the inverse of
Stacks 01LX (2), `Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`, lands it in the
base change.  No invertibility is needed for that, and none is needed for the commuting square,
which is `CategoryTheory.Over.w` of the comparison followed by the fibre-product condition.

**Where invertibility comes from.**  Every statement below is unconditional; the invertibility
the fibre-product property needs is
`AlgebraicGeometry.Space.isIso_chartSchemeAlgebraBaseChangeHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeModuleBaseChangeIso.lean`, which is Descent,
Proposition 03DX (2) in sheafified form and holds for every quasi-coherent `A` and every
morphism of charts.

**No `stacks` attribute is carried.**  What is built here is one step of the atlas construction
of Stacks 081V, not a numbered assertion of the source: Stacks 01LX (2) is registered where it
is proved, in
`StacksFrontier/AlgebraicGeometry/RelativeSpecOpenRestriction/RelativeSpecBaseChange.lean`, and the
chart restriction of an algebra on an algebraic space is untagged for the reasons recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeAlgebra.lean`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)

/-- **The comparison of the relative spectrum over a chart with the base change of the relative
spectrum over a larger chart.**

For a morphism `h : V' ⟶ V` of étale scheme charts of `X` this is the canonical morphism

`\underline{Spec}_{V'}(A|_{V'}) ⟶ \underline{Spec}_{V}(A|_V) ×_{chartScheme V} chartScheme V'`

over `chartScheme V'`.  It is the morphism of relative spectra over `chartScheme V'` that the
chart base-change comparison `AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom` of
algebras induces, followed by Stacks 01LX (2) identifying the relative spectrum of the base
change of the algebra with the base change of the relative spectrum.  Nothing beyond
quasi-coherence of `A` is assumed; invertibility of the algebra comparison is not used here, and
is what `AlgebraicGeometry.Space.isIso_chartRelativeSpecBaseChangeHom` adds. -/
def chartRelativeSpecBaseChangeHom :
    (Over.mk (chartRelativeSpecToChart B S hS X A hA V') : Over (chartScheme V')) ⟶
      (Over.pullback (chartSchemeMap h)).obj
        (Over.mk (chartRelativeSpecToChart B S hS X A hA V)) :=
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V'
  _root_.AlgebraicGeometry.relativeSpecMapOfAlgebraHom
      ((algebraPullback (chartSchemeMap h)).obj (chartSchemeAlgebra B S hS X A V))
      (chartSchemeAlgebra B S hS X A V')
      (chartSchemeAlgebraBaseChangeHom B S hS X A h) ≫
    (Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso (chartSchemeMap h)
      (chartSchemeAlgebra B S hS X A V)).inv

/-- **The morphism of relative spectra over a morphism of charts**,
`\underline{Spec}_{V'}(A|_{V'}) ⟶ \underline{Spec}_{V}(A|_V)`: the comparison with the base
change, followed by the projection of the fibre product.

This is the morphism of schemes that the atlas construction of Stacks 081V takes as the source
or target of its étale equivalence relation, according as `h` is the first or the second
projection of `R = U ×_X U`. -/
def chartRelativeSpecChartMap :
    chartRelativeSpec B S hS X A hA V' ⟶ chartRelativeSpec B S hS X A hA V :=
  (chartRelativeSpecBaseChangeHom B S hS X A hA h).left ≫
    pullback.fst (chartRelativeSpecToChart B S hS X A hA V) (chartSchemeMap h)

/-- **The square of the two relative spectra over the two chart schemes commutes.**
Unconditional: it is `CategoryTheory.Over.w` of
`AlgebraicGeometry.Space.chartRelativeSpecBaseChangeHom` followed by the fibre-product
condition. -/
theorem chartRelativeSpecChartMap_comp_chartRelativeSpecToChart :
    chartRelativeSpecChartMap B S hS X A hA h ≫ chartRelativeSpecToChart B S hS X A hA V =
      chartRelativeSpecToChart B S hS X A hA V' ≫ chartSchemeMap h := by
  have hw : (chartRelativeSpecBaseChangeHom B S hS X A hA h).left ≫
        pullback.snd (chartRelativeSpecToChart B S hS X A hA V) (chartSchemeMap h) =
      chartRelativeSpecToChart B S hS X A hA V' :=
    Over.w (chartRelativeSpecBaseChangeHom B S hS X A hA h)
  rw [chartRelativeSpecChartMap, Category.assoc, pullback.condition, ← Category.assoc, hw]

/-- The commuting square of `AlgebraicGeometry.Space.chartRelativeSpecChartMap` over
`chartSchemeMap h`, as a `CategoryTheory.CommSq`. -/
theorem commSq_chartRelativeSpecChartMap :
    CommSq (chartRelativeSpecChartMap B S hS X A hA h)
      (chartRelativeSpecToChart B S hS X A hA V')
      (chartRelativeSpecToChart B S hS X A hA V) (chartSchemeMap h) :=
  ⟨chartRelativeSpecChartMap_comp_chartRelativeSpecToChart B S hS X A hA h⟩

/-- The comparison of `AlgebraicGeometry.Space.chartRelativeSpecBaseChangeHom` as an
isomorphism over `chartScheme V'`.  **This is the descent datum the atlas construction of
Stacks 081V consumes**: it identifies the relative spectrum over the smaller chart with the base
change of the relative spectrum over the larger one.

The second factor is Stacks 01LX (2) and is always invertible; the first is the morphism of
relative spectra induced by `AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom`, and
`AlgebraicGeometry.isIso_relativeSpecMapOfAlgebraHom` turns invertibility of an algebra map into
invertibility of the induced morphism of relative spectra; that invertibility is Descent,
Proposition 03DX (2) in sheafified form at the morphism of charts `h`,
`AlgebraicGeometry.Space.isIso_chartSchemeAlgebraBaseChangeHom`. -/
theorem isIso_chartRelativeSpecBaseChangeHom :
    IsIso (chartRelativeSpecBaseChangeHom B S hS X A hA h) := by
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V'
  have := isIso_chartSchemeAlgebraBaseChangeHom B S hS X A h hA
  have h1 : IsIso (_root_.AlgebraicGeometry.relativeSpecMapOfAlgebraHom
      ((algebraPullback (chartSchemeMap h)).obj (chartSchemeAlgebra B S hS X A V))
      (chartSchemeAlgebra B S hS X A V')
      (chartSchemeAlgebraBaseChangeHom B S hS X A h)) :=
    _root_.AlgebraicGeometry.isIso_relativeSpecMapOfAlgebraHom _ _ _
  have h2 : IsIso (Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso (chartSchemeMap h)
      (chartSchemeAlgebra B S hS X A V)).inv := Iso.isIso_inv _
  change IsIso (_root_.AlgebraicGeometry.relativeSpecMapOfAlgebraHom
      ((algebraPullback (chartSchemeMap h)).obj (chartSchemeAlgebra B S hS X A V))
      (chartSchemeAlgebra B S hS X A V')
      (chartSchemeAlgebraBaseChangeHom B S hS X A h) ≫
    (Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso (chartSchemeMap h)
      (chartSchemeAlgebra B S hS X A V)).inv)
  exact IsIso.comp_isIso

/-- The comparison of `AlgebraicGeometry.Space.chartRelativeSpecBaseChangeHom` as an
isomorphism over `chartScheme V'`.  **This is the descent datum the atlas construction of
Stacks 081V consumes**: it identifies the relative spectrum over the smaller chart with the base
change of the relative spectrum over the larger one. -/
def chartRelativeSpecBaseChangeIso :
    (Over.mk (chartRelativeSpecToChart B S hS X A hA V') : Over (chartScheme V')) ≅
      (Over.pullback (chartSchemeMap h)).obj
        (Over.mk (chartRelativeSpecToChart B S hS X A hA V)) :=
  haveI := isIso_chartRelativeSpecBaseChangeHom B S hS X A hA h
  asIso (chartRelativeSpecBaseChangeHom B S hS X A hA h)

/-- The isomorphism is the comparison morphism: invertibility makes the same morphism
invertible, it does not replace it. -/
@[simp]
theorem chartRelativeSpecBaseChangeIso_hom :
    (chartRelativeSpecBaseChangeIso B S hS X A hA h).hom =
      chartRelativeSpecBaseChangeHom B S hS X A hA h :=
  rfl

/-- **The relative spectrum over a chart is the base change of the relative spectrum over a
larger chart**: the commuting square of
`AlgebraicGeometry.Space.chartRelativeSpecChartMap` over `chartSchemeMap h` is a fibre-product
square.

This is the statement the étale equivalence relation of Stacks 081V rests on: it is what makes
the induced morphisms of relative spectra base changes of the morphisms of chart schemes, hence
étale and surjective when those are. -/
theorem isPullback_chartRelativeSpecChartMap :
    IsPullback (chartRelativeSpecChartMap B S hS X A hA h)
      (chartRelativeSpecToChart B S hS X A hA V')
      (chartRelativeSpecToChart B S hS X A hA V) (chartSchemeMap h) := by
  have hi : ((Over.forget (chartScheme V')).mapIso
        (chartRelativeSpecBaseChangeIso B S hS X A hA h)).hom =
      (chartRelativeSpecBaseChangeHom B S hS X A hA h).left := rfl
  refine IsPullback.of_iso_pullback (commSq_chartRelativeSpecChartMap B S hS X A hA h)
    ((Over.forget (chartScheme V')).mapIso
      (chartRelativeSpecBaseChangeIso B S hS X A hA h)) ?_ ?_
  · rw [hi]
    rfl
  · rw [hi]
    exact Over.w (chartRelativeSpecBaseChangeHom B S hS X A hA h)

/-- **The induced morphism of relative spectra inherits every base-change-stable property of the
morphism of chart schemes**: it is a base change of `chartSchemeMap h`.

Applied to étaleness and to surjectivity this is what makes the pair of morphisms
`\underline{Spec}_{R}(A|_R) ⟶ \underline{Spec}_{U}(A|_U)` attached to `R = U ×_X U` an étale
equivalence relation. -/
theorem chartRelativeSpecChartMap_of_isStableUnderBaseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : P (chartSchemeMap h)) :
    P (chartRelativeSpecChartMap B S hS X A hA h) :=
  MorphismProperty.of_isPullback
    (isPullback_chartRelativeSpecChartMap B S hS X A hA h).flip hP

end AlgebraicGeometry.Space

end
