module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentGradedPiece
public import StacksFrontier.RingTheory.Cech.GradedSubcomplex
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular

/-!
# The middle-degree vanishing for the twists of the structure sheaf on projective space

The variables `T₀, …, Tₙ` of `R[T₀, …, Tₙ]` are a Koszul-regular sequence, so the extended
alternating Čech complex `Cech.cechComplex X R[T₀, …, Tₙ]` has cohomology only in its top degree
`n + 1` (`MvPolynomial.cechComplex_homology_X_isZero`). That complex is `ℤ`-graded — the terms are
localizations of `R[T₀, …, Tₙ]` at the homogeneous elements `∏_{i ∈ s} Tᵢ` and the differential
preserves the grading — and each term is the direct sum of its graded pieces
(`Cech.isInternal_gradedCechTerm`), the degree-`e` ones forming a subcomplex
`Cech.gradedCechComplex` which is a direct summand.

Hence **each degree-`e` subcomplex has cohomology only in degree `n + 1` as well**, for every
`e ∈ ℤ` at once and with no computation of the graded pieces whatsoever: that is
`Stacks.ProjectiveSpace.Cohomology.isZero_homology_gradedCechComplex_X` below. Since the extended
Čech complex of the standard cover `ℙⁿ_R = ⋃ᵢ D₊(Tᵢ)` is the Čech complex of that cover augmented
by the global sections, the content of this is the vanishing

$$ H^q(\mathbf{P}^n_R, \mathcal{O}(e)) = 0 \qquad (0 < q < n) $$

of [Stacks, Tag 01XT] in the middle degrees. The two extreme degrees `q = 0` and `q = n` are
genuinely graded statements and are computed separately, in the monomial model: the degree-`d`
graded pieces of the charts are free on the Laurent monomials
(`Stacks.ProjectiveSpace.Cohomology.twistSectionsBasis`,
`twistChartEquivTwistSections`), and the extreme-degree computations in that model are
`twistChartEmptyLinearEquiv` and
`Stacks.ProjectiveSpace.Cohomology.topCechDiff_range_eq_twistChart_univ` /
`negativeTwistPartLinearEquiv`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.isHomogeneous_X_mem` — the variables are homogeneous of
  degree one, as membership in the grading.
* `Stacks.ProjectiveSpace.Cohomology.isZero_homology_gradedCechComplex_X` — **the middle-degree
  vanishing**: the degree-`e` subcomplex of the extended Čech complex of the variables has zero
  cohomology in every degree other than `n + 1`.
* `Stacks.ProjectiveSpace.Cohomology.mem_gradedCechTerm_iff_mem_twistSections` — the terms of that
  subcomplex are the direct sums of the monomial charts.
* `Stacks.ProjectiveSpace.Cohomology.cechSign_compl_singleton` — the Čech sign at the top of the
  standard cover is the alternating sign `(-1) ^ i` used by
  `Stacks.ProjectiveSpace.Cohomology.topCechDiff`.

## Implementation notes

The grading on the polynomial ring is `MvPolynomial.homogeneousSubmodule`, extended to all integer
degrees by `AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading`; that is the family in which
the sections of `𝒪(e)` over a standard open `D₊(f)` are the degree-`e` graded piece of the single
localization `R[T₀, …, Tₙ][1/f]`, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroLocalization_twistGrading_eq`.

## What is not done

The passage from the Čech cohomology of the standard cover to the sheaf cohomology of `ℙⁿ_R` —
[Stacks, Tag 01XD] together with [Stacks, Tags 01FJ and 01FM], all three available in the library —
and the identification of the terms of the geometric Čech complex with the graded pieces of the
algebraic one via [Stacks, Tag 01M6], are not performed here, so no `@[stacks 01XT]` attribute is
attached. What this file supplies is the graded vanishing statement that the comparison would
transport.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The grading action of a non-negative ring degree on an integer module degree, as in every
file that needs it. -/
local instance instVAddNatIntTwistCohomology : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

namespace Stacks.ProjectiveSpace.Cohomology

/-- The variables of `R[T₀, …, Tₙ]` are homogeneous of degree one. -/
theorem isHomogeneous_X_mem (R : Type u) [CommRing R] (n : ℕ) :
    ∀ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R ((fun _ => 1 : Fin (n + 1) → ℕ) i) :=
  fun i => (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X R i)

/-- **The middle-degree vanishing of [Stacks, Tag 01XT].** For every `e ∈ ℤ` the degree-`e`
subcomplex of the extended alternating Čech complex of the variables `T₀, …, Tₙ` of
`R[T₀, …, Tₙ]` has zero cohomology in every degree other than the top one `n + 1`.

The input is `MvPolynomial.cechComplex_homology_X_isZero`, the concentration of the *ungraded*
complex in its top degree, which is Koszul-regularity of the variables. The grading is what turns
that one statement into a statement about each twist `𝒪(e)` separately, and it enters only through
`Cech.isZero_homology_gradedCechComplex`: the degree-`e` subcomplex is a direct summand, so its
cohomology is a summand of the cohomology computed there. No graded piece is computed. -/
theorem isZero_homology_gradedCechComplex_X (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)
    (e : ℤ) (p : ℕ) (hp : p + 1 ≠ n + 1) :
    IsZero ((Cech.gradedCechComplex (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
      (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
      (isHomogeneous_X_mem R n) e).homology (p + 1)) :=
  Cech.isZero_homology_gradedCechComplex _ _ _ (isHomogeneous_X_mem R n) e p
    (MvPolynomial.cechComplex_homology_X_isZero n (p + 1) hp)

/-- **The degree-`e` Čech cochains are the monomial sections.** A cochain of the extended Čech
complex of the variables is homogeneous of degree `e` exactly when each of its components is a
degree-`e` section of `𝒪(e)` over the corresponding chart `D₊(∏_{i ∈ s} Tᵢ)`, in the sense of
`Stacks.ProjectiveSpace.Cohomology.twistSections`. Composed with
`Stacks.ProjectiveSpace.Cohomology.twistChartEquivTwistSections` this exhibits each term of the
degree-`e` subcomplex as the direct sum, over the `p`-element sets `s` of indices, of the monomial
charts `Stacks.ProjectiveSpace.Cohomology.twistChart R n e s` of
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentCharts`.

The two sides are the *same* additive subgroup — `Cech.gradedCechTerm` is cut out by exactly the
condition `twistSections` is the carrier of — so this is a definitional identification, recorded
because it is what makes the monomial computations of `LaurentCharts` and `TopCech` computations
about the complex whose cohomology
`Stacks.ProjectiveSpace.Cohomology.isZero_homology_gradedCechComplex_X` controls. -/
theorem mem_gradedCechTerm_iff_mem_twistSections (R : Type u) [CommRing R] (n : ℕ) (e : ℤ)
    (p : ℕ) {z : Cech.cechTerm (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
      (MvPolynomial (Fin (n + 1)) R) p} :
    z ∈ Cech.gradedCechTerm (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
        (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) e p ↔
      ∀ s : {s : Finset (Fin (n + 1)) // s.card = p}, z s ∈ twistSections R n e s.1 :=
  Iff.rfl

/-- **The Čech sign at the top of the standard cover is the alternating sign.** The charts just
below the top one are the complements `{i}ᶜ` of the singletons, and the sign with which the
transition map out of `{i}ᶜ` enters the Čech differential — `(-1)` to the number of indices of
`{i}ᶜ` below `i` — is `(-1) ^ i`.

This is the compatibility that makes
`Stacks.ProjectiveSpace.Cohomology.topCechDiff`, whose signs are written `(-1) ^ i` directly, the
top differential of `Cech.gradedCechComplex` for the variables: no index below `i` is removed by
passing from `Finset.univ` to `{i}ᶜ`, so the two counts agree. -/
theorem cechSign_compl_singleton (n : ℕ) (i : Fin (n + 1)) :
    Cech.cechSign ({i}ᶜ : Finset (Fin (n + 1))) i = (-1) ^ (i : ℕ) := by
  classical
  have hfil : (({i}ᶜ : Finset (Fin (n + 1))).filter (· < i)) =
      Finset.univ.filter (fun k : Fin (n + 1) => k < i) := by
    ext k
    simpa using fun h : k < i => h.ne
  have hcard : (Finset.univ.filter (fun k : Fin (n + 1) => k < i)).card = (i : ℕ) := by
    rw [← Fin.card_Iio i]
    congr 1
    ext k
    simp
  rw [Cech.cechSign, hfil, hcard]

end Stacks.ProjectiveSpace.Cohomology

end
