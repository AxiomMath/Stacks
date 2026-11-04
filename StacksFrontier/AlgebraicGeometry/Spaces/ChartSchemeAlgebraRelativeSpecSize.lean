module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Size
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebraRelativeSpec
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite

/-!
# The size of the relative spectrum of a quasi-coherent algebra over a chart

Let `X` be an algebraic space in a big fppf site `B`, let `A` be a quasi-coherent sheaf of
commutative `𝒪_X`-algebras on its small étale site, and let `V` be an étale scheme chart of `X`.
`AlgebraicGeometry.Space.chartRelativeSpec` is the scheme `\underline{Spec}_{V}(A|_V)`. Its
`AlgebraicGeometry.Scheme.size` is bounded by any cardinal bounding the size of the chart's
scheme and the cardinalities of the sections of `A` over the étale charts of `X` that the
affine opens of the chart's scheme cut out, and it is an object of `B` when such a cardinal lies
below the cutoff.

## Main results

* `AlgebraicGeometry.Space.size_chartRelativeSpec_le`: the size bound.
* `AlgebraicGeometry.Space.contains_chartRelativeSpec_of_lt_cutoff`: the relative spectrum over
  a chart is an object of the site, given a cardinal below the cutoff bounding both the chart
  and the algebra's chart sections.
* `AlgebraicGeometry.Space.contains_chartRelativeSpec`: the same with the bound presented as
  `T.size ^ ℵ₀` for an object `T` of the site.
* `AlgebraicGeometry.Space.contains_chartRelativeSpec_of_le_chartScheme`: the same with `T` the
  chart's scheme.

## Implementation notes

`AlgebraicGeometry.Space.chartRelativeSpec` is by definition
`Stacks.AffineAlgebraEquivalence.relativeSpec` of `AlgebraicGeometry.Space.chartSchemeAlgebra`,
and the sections of the restricted algebra over a Zariski open `O` of the chart's scheme are by
definition (`AlgebraicGeometry.Space.chartSchemeAlgebra_sections`) the sections of `A` over
`AlgebraicGeometry.Space.openChart` at `O`, so the hypotheses are stated directly in terms of `A`.

## References

* [Stacks Project, Tag 000I](https://stacks.math.columbia.edu/tag/000I)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (V : SmallEtale B S hS X.1)

/-- If `size (chartScheme V) ≤ c` and `#A(openChart O) ≤ c` for every affine open `O` of the
chart's scheme, then `size (chartRelativeSpec A V) ≤ c`. -/
theorem size_chartRelativeSpec_le {c : Cardinal.{u}} (hc : (chartScheme V).size ≤ c)
    (hAc : ∀ O : (chartScheme V).affineOpens,
      #(A.right.obj.obj (op (openChart B S hS X.1 V (O : (chartScheme V).Opens)))) ≤ c) :
    (chartRelativeSpec B S hS X A hA V).size ≤ c :=
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  Stacks.AffineAlgebraEquivalence.size_relativeSpec_le
    (chartSchemeAlgebra B S hS X A V) hc hAc

/-- The relative spectrum of a quasi-coherent algebra over a chart is an object of the site,
given a single cardinal below the cutoff bounding both the chart's scheme and the sections of
`A` over the étale charts the affine opens of the chart's scheme cut out. -/
theorem contains_chartRelativeSpec_of_lt_cutoff {c : Cardinal.{u}} (hc : c < B.cutoff)
    (hcV : (chartScheme V).size ≤ c)
    (hAc : ∀ O : (chartScheme V).affineOpens,
      #(A.right.obj.obj (op (openChart B S hS X.1 V (O : (chartScheme V).Opens)))) ≤ c) :
    B.Contains (chartRelativeSpec B S hS X A hA V) :=
  (size_chartRelativeSpec_le B S hS X A hA V hcV hAc).trans_lt hc

/-- The relative spectrum of a quasi-coherent algebra over a chart is an object of the site,
given an object `T` of the site such that `T.size ^ ℵ₀` bounds both the size of the chart's
scheme and the sections of `A` over the étale charts the affine opens of the chart's scheme cut
out. -/
theorem contains_chartRelativeSpec {T : Scheme.{u}} (hT : B.Contains T)
    (hTS : (chartScheme V).size ≤ T.size ^ ℵ₀)
    (hAc : ∀ O : (chartScheme V).affineOpens,
      #(A.right.obj.obj (op (openChart B S hS X.1 V (O : (chartScheme V).Opens)))) ≤
        T.size ^ ℵ₀) :
    B.Contains (chartRelativeSpec B S hS X A hA V) :=
  contains_chartRelativeSpec_of_lt_cutoff B S hS X A hA V
    (power_aleph0_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hT)
    hTS hAc

/-- The relative spectrum of a quasi-coherent algebra over a chart is an object of the site as
soon as the sections of `A` over the étale charts the affine opens of the chart's scheme cut out
are bounded by `(chartScheme V).size ^ ℵ₀`. -/
theorem contains_chartRelativeSpec_of_le_chartScheme
    (hAc : ∀ O : (chartScheme V).affineOpens,
      #(A.right.obj.obj (op (openChart B S hS X.1 V (O : (chartScheme V).Opens)))) ≤
        (chartScheme V).size ^ ℵ₀) :
    B.Contains (chartRelativeSpec B S hS X A hA V) :=
  contains_chartRelativeSpec B S hS X A hA V (SmallEtale.contains_chartScheme B S hS X.1 V)
    (Cardinal.self_le_power _ one_le_aleph0) hAc

end AlgebraicGeometry.Space

end
