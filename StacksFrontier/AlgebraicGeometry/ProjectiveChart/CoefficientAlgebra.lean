module

public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsLinear

/-!
# The chart identification is one of `R`-algebras

`Stacks.ProjectiveChart.chartRingEquiv` and `Stacks.ProjectiveChart.sectionsChartEquiv` identify
the `j`-th standard chart of `ℙⁿ_R` with the polynomial ring `R[Y₁, …, Yₙ]`, but only as rings.
Every statement about `ℙⁿ_R` *over* `R` — smoothness of a subscheme over `R`, the residue field
of a point as an extension of `R` — reads the chart through the structure morphism
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`, so the identification is of no use
there until it is known to carry the constants of `R[Y₁, …, Yₙ]` to the functions pulled back
from `Spec R`.  That is what this file proves.

## Main results

* `Stacks.ProjectiveChart.chartRingEquiv_C`: the chart identification carries `C r` to the image
  of `r` under the structure map of the chart ring as an `R`-algebra.
* `Stacks.ProjectiveChart.sectionsChartEquiv_C`: **the chart identification is `R`-linear** — it
  carries `C r` to the pullback of `r` along the structure morphism `ℙⁿ_R ⟶ Spec R`, restricted
  to the chart.

## Implementation notes

The `R`-algebra structure on the chart ring is `HomogeneousLocalization.instAlgebra`, whose
structure map is the composite `R → 𝒜₀ → HomogeneousLocalization`; `chartRingEquiv_C` is
therefore the statement that `Stacks.ProjectiveChart.degreeZeroEquiv` is `R`-linear, which it is
because `algebraMap R (MvPolynomial (Fin (n + 1)) R)` is `MvPolynomial.C`.

On sections the comparison is with the pullback of a coefficient, which
`Stacks.ProjectiveSpace.Cohomology.res_coeffToGlobalSections` already computes on an arbitrary
standard open: both sides have the constant value `C r / 1` in every fibre.  What is added here
is that the left-hand side of that computation is the restriction of the pullback along
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`, i.e. an
`AlgebraicGeometry.Scheme.Hom.appLE`, and that the right-hand side is the image of `C r` under
`sectionsChartEquiv`.

## References

* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.ProjectiveChart

universe u

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-zero identification is `R`-linear: the constant polynomial `C r`, viewed as a
degree-zero homogeneous polynomial, is the image of `r` under the structure map. -/
theorem degreeZeroEquiv_symm_eq_algebraMap {n : ℕ} (r : R) :
    (degreeZeroEquiv R n).symm r = algebraMap R (Deg0 R n) r := by
  apply Subtype.ext
  rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
  rfl

/-- **The chart identification carries constants to constants.**  The `j`-th chart ring of
`ℙⁿ_R` is an `R`-algebra through `HomogeneousLocalization.instAlgebra`, and
`Stacks.ProjectiveChart.chartRingEquiv` is a map of `R`-algebras. -/
theorem chartRingEquiv_C {n : ℕ} (j : Fin (n + 1)) (r : R) :
    chartRingEquiv R j (MvPolynomial.C r) = algebraMap R (ChartRing R n j) r := by
  rw [chartRingEquiv, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
  simp only [RingEquiv.coe_toRingHom, degreeZeroEquiv_symm_eq_algebraMap]
  change (chartHom R j) (MvPolynomial.C (algebraMap R (Deg0 R n) r)) = _
  exact MvPolynomial.aeval_C _ _

/-- **The chart identification is `R`-linear on sections.**  The section of `𝒪_{ℙⁿ_R}` over
`D₊(Tⱼ)` corresponding to the constant polynomial `C r` is the pullback of `r` along the
structure morphism `ℙⁿ_R ⟶ Spec R`.

This is what makes `Stacks.ProjectiveChart.sectionsChartEquiv` usable in a statement relative to
the base: it upgrades a ring isomorphism to an isomorphism of `R`-algebras. -/
theorem sectionsChartEquiv_C {n : ℕ} (j : Fin (n + 1)) (r : R) :
    sectionsChartEquiv R j (MvPolynomial.C r) =
      ((Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appLE ⊤
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.X j)) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
  rw [sectionsChartEquiv, RingEquiv.trans_apply, chartRingEquiv_C]
  exact (Stacks.ProjectiveSpace.Cohomology.res_coeffToGlobalSections
    (f := MvPolynomial.X j) r).symm

end Stacks.ProjectiveChart

end
