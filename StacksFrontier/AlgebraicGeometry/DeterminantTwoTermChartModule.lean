module

public import StacksFrontier.AlgebraicGeometry.AffineOpensDirectedGlue
public import StacksFrontier.AlgebraicGeometry.AffineOpensRestrictionFlat
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermAffine

/-!
# The determinant of a two-term perfect complex on an affine chart of a scheme

Let `X` be a scheme and let `L` be a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`.
Every affine open `V` of `X` carries the chart `Spec Γ(X, V) ⟶ X` of
`AlgebraicGeometry.IsAffineOpen.fromSpec`, the derived pullback of `L` along it is a perfect
object of `D(𝒪_{Spec Γ(X, V)})` of Tor-amplitude in `[-1, 0]`, and the determinant of
Stacks 0FJX for an affine scheme applies to it. This file packages the resulting invertible
module on the open subscheme `V`, which is the member of the family the determinant on an
arbitrary scheme is glued from, together with the rank-zero condition and the canonical section
on a chart.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartObj`: the derived pullback of `L` to the chart of an
  affine open, as an object of the source groupoid there.
* `AlgebraicGeometry.DeterminantTwoTerm.chartComplex`: the complex of `Γ(X, V)`-modules
  corresponding to it under the affine derived equivalence.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpec` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartDet`: **the determinant of `L` on the chart of an
  affine open**, on `Spec Γ(X, V)` and transported to the open subscheme `V`.
* `AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroOn`: rank zero for a perfect object of
  `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` on an arbitrary scheme — rank zero on every affine
  chart.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDelta`: the canonical global section of the
  determinant on a chart, for a rank-zero object.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.isInvertibleModule_chartDetSpec` and
  `AlgebraicGeometry.DeterminantTwoTerm.isInvertibleModule_chartDet`: the determinant on a chart
  is an invertible module.
* `AlgebraicGeometry.DeterminantTwoTerm.isRankZeroSpec_chartObj`: on a chart, the rank-zero
  condition of this file is the one `AlgebraicGeometry.DeterminantTwoTerm.specDelta` consumes.

## Implementation notes

The chart of an affine open `V` is `AlgebraicGeometry.IsAffineOpen.fromSpec`, an open immersion
`Spec Γ(X, V) ⟶ X` with range `V`; it is the composite of
`AlgebraicGeometry.IsAffineOpen.isoSpec.inv` with the inclusion of the open subscheme, and
`AlgebraicGeometry.IsAffineOpen.map_fromSpec` is what makes the charts of `V ≤ W` compatible.
The determinant is first taken on `Spec Γ(X, V)`, where
`AlgebraicGeometry.DeterminantTwoTerm.specDet` lives, and then pulled back along
`AlgebraicGeometry.IsAffineOpen.isoSpec` to the open subscheme, because the glueing datum of
`StacksFrontier.AlgebraicGeometry.AffineOpensDirectedGlue` is indexed by the affine opens and its
charts are the inclusions `V.ι`, which compose strictly with `AlgebraicGeometry.Scheme.homOfLE`.

Rank zero is read on the charts rather than postulated on `D(𝒪_X)`: for a perfect object of
Tor-amplitude in `[-1, 0]` that is what rank `0` means, and
`AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroSpec` is its affine form.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- The derived pullback of `L` to the chart `Spec Γ(X, V) ⟶ X` of an affine open `V`, as an
object of the source groupoid of the determinant there. -/
def chartObj (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    PerfectTwoTermAmplitude (Spec Γ(X, (V.1 : X.Opens))) :=
  derivedPullbackObj V.2.fromSpec L

/-- The perfect object of `D(Γ(X, V))` of Tor-amplitude in `[-1, 0]` corresponding to the
restriction of `L` to the chart of an affine open `V`. -/
def chartComplex (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    PerfectTwoTermComplex Γ(X, (V.1 : X.Opens)) :=
  sourceComplex Γ(X, (V.1 : X.Opens)) (chartObj L V)

/-- **The determinant of `L` on the chart of an affine open**, as an invertible module on
`Spec Γ(X, V)`. -/
def chartDetSpec (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    (Spec Γ(X, (V.1 : X.Opens))).Modules :=
  ((specDet Γ(X, (V.1 : X.Opens))).obj ⟨chartObj L V⟩).of.obj

/-- The determinant of `L` on a chart is an invertible module. -/
theorem isInvertibleModule_chartDetSpec (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    Stacks.Ample.IsInvertibleModule (Spec Γ(X, (V.1 : X.Opens))) (chartDetSpec L V) :=
  ((specDet Γ(X, (V.1 : X.Opens))).obj ⟨chartObj L V⟩).of.property

/-- **The determinant of `L` on an affine open**, transported from `Spec Γ(X, V)` to the open
subscheme `V` along `AlgebraicGeometry.IsAffineOpen.isoSpec`. This is the member of the family
the determinant on an arbitrary scheme is glued from. -/
def chartDet (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    ((V.1 : X.Opens) : Scheme.{u}).Modules :=
  (Scheme.Modules.pullback V.2.isoSpec.hom).obj (chartDetSpec L V)

/-- The determinant of `L` on an affine open is an invertible module: invertibility is preserved
by pullback, and it holds on `Spec Γ(X, V)`. -/
theorem isInvertibleModule_chartDet (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    Stacks.Ample.IsInvertibleModule ((V.1 : X.Opens) : Scheme.{u}) (chartDet L V) := by
  have : Stacks.Ample.IsInvertibleModule (Spec Γ(X, (V.1 : X.Opens))) (chartDetSpec L V) :=
    isInvertibleModule_chartDetSpec L V
  exact inferInstanceAs
    (Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback V.2.isoSpec.hom).obj _))

/-- **Rank zero for a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` on an arbitrary
scheme**: the complex of `Γ(X, V)`-modules it restricts to has rank zero on every affine open
`V`, that is, the two terms of a two-term finite-projective presentation of it have the same rank
at every prime. -/
def IsRankZeroOn (L : PerfectTwoTermAmplitude X) : Prop :=
  ∀ V : X.affineOpens, TwoTermDeterminant.IsRankZero (chartComplex L V).obj

/-- A rank-zero object restricts on every chart to an object that is rank zero in the sense
`AlgebraicGeometry.DeterminantTwoTerm.specDelta` consumes. -/
theorem isRankZeroSpec_chartObj {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) :
    IsRankZeroSpec Γ(X, (V.1 : X.Opens)) (chartObj L V) :=
  ⟨(chartComplex L V).obj,
    ⟨(IsPerfectTwoTermAmplitude (Spec Γ(X, (V.1 : X.Opens)))).ι.mapIso
      (tildeSourceComplexIso Γ(X, (V.1 : X.Opens)) (chartObj L V))⟩, hL V⟩

/-- The canonical global section of the determinant of `L` on the chart of an affine open, for a
rank-zero object: the canonical element of More on Algebra, Section 0FJI of the complex of
`Γ(X, V)`-modules there. -/
def chartDelta {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L) (V : X.affineOpens) :
    Γ(chartDetSpec L V, ⊤) :=
  specDelta Γ(X, (V.1 : X.Opens)) (chartObj L V) (isRankZeroSpec_chartObj hL V)

end AlgebraicGeometry.DeterminantTwoTerm

end
