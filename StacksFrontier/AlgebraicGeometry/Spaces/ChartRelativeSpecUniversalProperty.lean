module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebraRelativeSpec
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The universal property of the relative spectrum of an algebra over a chart

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `V` be an étale scheme chart of `X`.
`AlgebraicGeometry.Space.chartRelativeSpec` is the scheme
`\underline{Spec}_{chartScheme V}(A|_{chartScheme V})` and
`AlgebraicGeometry.Space.chartRelativeSpecToChart` its structure morphism to the chart.  This
file records two properties of that structure morphism:

* its direct image recovers the algebra, `(ν_V)_* 𝒪 ≅ A|_{chartScheme V}`; and
* a morphism of schemes into it over the chart is the same thing as a map of
  `A|_{chartScheme V}` into the direct image of the structure sheaf of the source.

## Main definitions

* `AlgebraicGeometry.Space.chartRelativeSpecPushforwardIso`: **the direct image of the structure
  sheaf of the relative spectrum over a chart is the chart restriction of `A`.**
* `AlgebraicGeometry.Space.chartRelativeSpecLift`: **the morphism into the relative spectrum over
  a chart attached to a map of algebras**, as a morphism of schemes over the chart.

## Main results

* `AlgebraicGeometry.Space.chartRelativeSpecLift_comp`: the morphism lies over the chart.
* `AlgebraicGeometry.Space.pushforwardAlgebraMap_chartRelativeSpecLift`: the algebra map it
  induces is the one it was built from.
* `AlgebraicGeometry.Space.chartRelativeSpecLift_ext`: a morphism into the relative spectrum over
  the chart is determined by the algebra map it induces.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (V : SmallEtale B S hS X.1)

/-- **The direct image of the structure sheaf of the relative spectrum over a chart is the chart
restriction of the algebra.** -/
def chartRelativeSpecPushforwardIso :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (chartRelativeSpecToChart B S hS X A hA V) ≅
      chartSchemeAlgebra B S hS X A V :=
  haveI := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso (chartSchemeAlgebra B S hS X A V)

section Lift

variable {T : Scheme.{u}} (g : T ⟶ chartScheme V)
    (φ : chartSchemeAlgebra B S hS X A V ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra g)

/-- **The morphism into the relative spectrum over a chart attached to a map of algebras.**  For
a scheme `T` over the chart and a map `A|_{chartScheme V} ⟶ g_* 𝒪_T` of algebras on the chart,
this is the induced morphism `T ⟶ \underline{Spec}_{chartScheme V}(A|_{chartScheme V})` over the
chart. -/
@[sga "3 III 0.1.7" "0.1.7(a)"]
def chartRelativeSpecLift :
    Over.mk g ⟶ Over.mk (chartRelativeSpecToChart B S hS X A hA V) :=
  Stacks.AffineAlgebraEquivalence.overHomOfAlgebraHom
    ((chartRelativeSpecPushforwardIso B S hS X A hA V).hom ≫ φ)

/-- **The morphism of `AlgebraicGeometry.Space.chartRelativeSpecLift` lies over the chart**: it
composed with the structure morphism of the relative spectrum is the structure morphism of `T`. -/
theorem chartRelativeSpecLift_comp :
    (chartRelativeSpecLift B S hS X A hA V g φ).left ≫
        chartRelativeSpecToChart B S hS X A hA V = g :=
  Over.w _

/-- **The algebra map induced by `AlgebraicGeometry.Space.chartRelativeSpecLift` is the one it
was built from**, read through the identification
`AlgebraicGeometry.Space.chartRelativeSpecPushforwardIso`. -/
theorem pushforwardAlgebraMap_chartRelativeSpecLift :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap
        (chartRelativeSpecLift B S hS X A hA V g φ) =
      (chartRelativeSpecPushforwardIso B S hS X A hA V).hom ≫ φ :=
  Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_overHomOfAlgebraHom _

end Lift

/-- **A morphism of schemes over the chart into the relative spectrum is determined by the
algebra map it induces.** -/
@[sga "3 III 0.1.7" "0.1.7(a)"]
theorem chartRelativeSpecLift_ext {T : Scheme.{u}} (g : T ⟶ chartScheme V)
    {u v : Over.mk g ⟶ Over.mk (chartRelativeSpecToChart B S hS X A hA V)}
    (h : Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap u =
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap v) : u = v :=
  Stacks.AffineAlgebraEquivalence.eq_of_pushforwardAlgebraMap_eq h

end AlgebraicGeometry.Space

end
