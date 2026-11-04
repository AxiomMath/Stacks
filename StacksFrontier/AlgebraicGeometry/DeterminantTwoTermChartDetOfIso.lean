module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDelta
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDetIso
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartNatural

/-!
# The determinant of an isomorphism on an affine chart

Let `X` be a scheme and `a : L ≅ K` an isomorphism of perfect objects of `D(𝒪_X)` of Tor-amplitude
in `[-1, 0]`. On each affine open `V` of `X` the restriction of `a` to the chart of `V` is an
isomorphism `AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso` of the chart complexes over
`Γ(X, V)`, its determinant is a linear equivalence of the determinant modules there, and
`AlgebraicGeometry.DeterminantTwoTerm.chartDetOfEquiv` turns that into an isomorphism of the
determinants of `L` and of `K` on `V`. This file names that isomorphism and proves it functorial
in `a`.

That functoriality is what makes the determinant of a two-term perfect complex on an arbitrary
scheme a functor: the determinant of `a` is glued from these, and the family of identities glues to
the identity while a family of composites glues to the composite.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetIso`: **the determinant of an isomorphism on an
  affine chart.**

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetIso_refl` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetIso_trans`: **the determinant of an isomorphism on
  an affine chart is functorial in the isomorphism.**
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecIso_chartDelta`: **the determinant of an
  isomorphism carries the canonical element on a chart to the canonical element.**

## Implementation notes

The three steps compose their own functorialities: the restriction of an isomorphism to a chart is
functorial by `AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso_refl` and
`chartComplexIso_trans`, the determinant of an isomorphism of perfect two-term objects is
functorial by `TwoTermDeterminant.detIsoEquiv_refl` and `detIsoEquiv_trans` — read through
`AlgebraicGeometry.DeterminantTwoTerm.detLinearEquivOfIso_eq_detIsoEquiv`, the two spellings being
the same — and passing from a linear equivalence to an isomorphism of sheaves on `V` is functorial
by `AlgebraicGeometry.DeterminantTwoTerm.chartDetOfEquiv_refl` and `chartDetOfEquiv_trans`.

The two statements are therefore a `congrArg` of each middle step followed by the corresponding
outer step. They are written with `congrArg` and `Eq.trans` rather than with `rw`: the determinant
module of a chart complex has a long unfolding through `TwoTermDeterminant.det`,
`CategoryTheory.Core.inclusion` and `CategoryTheory.ObjectProperty.ι`, and a goal that mentions
both spellings is type-correct only at default transparency, where `rw` does not operate.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **The determinant of an isomorphism on an affine chart.** For an isomorphism `a : L ≅ K` of
perfect objects of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and an affine open `V` of `X`, the
determinant on `V` of `L` is identified with the determinant on `V` of `K` by the determinant of
the restriction of `a` to the chart of `V`. -/
def chartDetIso {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj) (V : X.affineOpens) :
    chartDet L V ≅ chartDet K V :=
  chartDetOfEquiv V (detLinearEquivOfIso (chartComplexIso a V))

/-- **The determinant of the identity isomorphism on an affine chart is the identity.** -/
theorem chartDetIso_refl (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    chartDetIso (Iso.refl L.obj) V = Iso.refl _ :=
  (congrArg (chartDetOfEquiv V)
      ((congrArg detLinearEquivOfIso (chartComplexIso_refl L V)).trans detIsoEquiv_refl)).trans
    (chartDetOfEquiv_refl L V)

/-- **The determinant of a composite of isomorphisms on an affine chart is the composite of the
determinants.** -/
theorem chartDetIso_trans {L K M : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    (b : K.obj ≅ M.obj) (V : X.affineOpens) :
    chartDetIso (a ≪≫ b) V = chartDetIso a V ≪≫ chartDetIso b V :=
  (congrArg (chartDetOfEquiv V)
      ((congrArg detLinearEquivOfIso (chartComplexIso_trans a b V)).trans
        (detIsoEquiv_trans (chartComplexIso a V) (chartComplexIso b V)))).trans
    (chartDetOfEquiv_trans V (detLinearEquivOfIso (chartComplexIso a V))
      (detLinearEquivOfIso (chartComplexIso b V)))

/-! ### The canonical element on a chart -/

/-- **The determinant of an isomorphism carries the canonical element on a chart to the canonical
element.** For an isomorphism `a : L ≅ K` of rank-zero perfect objects of `D(𝒪_X)` of Tor-amplitude
in `[-1, 0]` and an affine open `V` of `X`, the determinant of the restriction of `a` to the chart
of `V` carries the canonical global section of the determinant of `L` on `Spec Γ(X, V)` to that of
`K`.

Over the rings this is `AlgebraicGeometry.DeterminantTwoTerm.detLinearEquivOfIso_delta`, the
determinant of an isomorphism of perfect two-term objects carrying `δ` to `δ`; passing to global
sections of the associated sheaves is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecOfEquiv_chartDelta`. -/
theorem chartDetSpecIso_chartDelta {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    (hL : IsRankZeroOn L) (hK : IsRankZeroOn K) (V : X.affineOpens) :
    Scheme.Modules.Hom.app
        (chartDetSpecOfEquiv V (detLinearEquivOfIso (chartComplexIso a V))).hom ⊤
        (chartDelta hL V) = chartDelta hK V :=
  chartDetSpecOfEquiv_chartDelta hL hK V (detLinearEquivOfIso (chartComplexIso a V))
    (detLinearEquivOfIso_delta (chartComplexIso a V) (hL V) (hK V))

end AlgebraicGeometry.DeterminantTwoTerm

end
