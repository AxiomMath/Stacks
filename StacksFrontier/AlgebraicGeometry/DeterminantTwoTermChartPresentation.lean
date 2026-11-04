module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartModule

/-!
# The determinant on an affine chart is the determinant line of a presentation

Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and `V` an
affine open of `X`. The determinant `AlgebraicGeometry.DeterminantTwoTerm.chartDet` of `L` on `V`
is the sheaf associated with the determinant line of More on Algebra, Section 0FJI of *any*
two-term finite-projective presentation of the complex of `Γ(X, V)`-modules
`AlgebraicGeometry.DeterminantTwoTerm.chartComplex`, and if `L` has rank zero the canonical
element of the determinant on `V` is the determinant of the differential of that presentation.

This is the affine-local description of the determinant, read on an affine open of an arbitrary
scheme rather than on a scheme of the form `Spec R`: it is
`AlgebraicGeometry.DeterminantTwoTerm.specDetPresentationIso` and
`AlgebraicGeometry.DeterminantTwoTerm.specDetPresentationIso_specDelta` of
`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermAffine.lean`, transported to the open subscheme
`V` along `AlgebraicGeometry.IsAffineOpen.isoSpec`.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetPresentationIso`: **the determinant of `L` on an
  affine open is the determinant line of a presentation of the chart complex**, pulled back along
  `AlgebraicGeometry.IsAffineOpen.isoSpec`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPresentationIso`: the same comparison before
  that transport, on `Spec Γ(X, V)`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPresentationIso_chartDelta`: **the canonical
  element of the determinant on a chart is the canonical element of the presentation.**

## Implementation notes

The determinant on a chart is `AlgebraicGeometry.DeterminantTwoTerm.specDet` at the derived
pullback of `L` to the chart, and `chartComplex` is by definition the complex of `Γ(X, V)`-modules
that derived sheafification attaches to that pullback, so the comparison on `Spec Γ(X, V)` is
`specDetPresentationIso` with nothing interposed; the rank-zero hypothesis it consumes is
`AlgebraicGeometry.DeterminantTwoTerm.isRankZeroSpec_chartObj`, and
`AlgebraicGeometry.DeterminantTwoTerm.chartDelta` is `specDelta` by definition. The statement on
the open subscheme is the image of the comparison under
`AlgebraicGeometry.Scheme.Modules.pullback` along `isoSpec`, which is how
`AlgebraicGeometry.DeterminantTwoTerm.chartDet` is defined from `chartDetSpec`.

The four `letI`s carrying finiteness and projectivity of the two terms of the presentation are the
ones `TwoTermComplex.determinantLine` needs, and they are written in the statement exactly as
`specDetPresentationIso` writes them.

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

/-- **The determinant of `L` on the spectrum of an affine open is the determinant line of a
presentation of the chart complex.** For an affine open `V` of `X` and a two-term
finite-projective presentation `P` of the complex of `Γ(X, V)`-modules attached to `L` there, the
determinant of `L` on `Spec Γ(X, V)` is the sheaf associated with the determinant line of More on
Algebra, Section 0FJI of `P`.

This is `AlgebraicGeometry.DeterminantTwoTerm.specDetPresentationIso` at the derived pullback of
`L` to the chart of `V`. -/
def chartDetSpecPresentationIso (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    chartDetSpec L V ≅
      tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) :=
  specDetPresentationIso Γ(X, (V.1 : X.Opens)) (chartObj L V) P

/-- **The determinant of `L` on an affine open is the determinant line of a presentation of the
chart complex.** The comparison `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPresentationIso`,
transported from `Spec Γ(X, V)` to the open subscheme `V` along
`AlgebraicGeometry.IsAffineOpen.isoSpec`, which is how
`AlgebraicGeometry.DeterminantTwoTerm.chartDet` is obtained from `chartDetSpec`. -/
def chartDetPresentationIso (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    chartDet L V ≅
      (Scheme.Modules.pullback V.2.isoSpec.hom).obj
        (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom))) :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecPresentationIso L V P)

/-- **The canonical element of the determinant of `L` on a chart is the canonical element of a
presentation.** For a rank-zero `L` and a rank-zero two-term finite-projective presentation `P` of
the chart complex, the comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPresentationIso` carries
`AlgebraicGeometry.DeterminantTwoTerm.chartDelta` to the determinant of the differential of `P`,
read as a global section of the associated sheaf.

This is `AlgebraicGeometry.DeterminantTwoTerm.specDetPresentationIso_specDelta` at the derived
pullback of `L` to the chart of `V`. -/
theorem chartDetSpecPresentationIso_chartDelta {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) (hP : P.IsRankZero) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    Scheme.Modules.Hom.app (chartDetSpecPresentationIso L V P).hom ⊤ (chartDelta hL V) =
      (tilde.toOpen (ModuleCat.of Γ(X, (V.1 : X.Opens))
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤).hom
          (TwoTermComplex.delta (P.complex.d (-1) 0).hom hP) :=
  specDetPresentationIso_specDelta Γ(X, (V.1 : X.Opens)) (chartObj L V) P hP
    (isRankZeroSpec_chartObj hL V)

end AlgebraicGeometry.DeterminantTwoTerm

end
