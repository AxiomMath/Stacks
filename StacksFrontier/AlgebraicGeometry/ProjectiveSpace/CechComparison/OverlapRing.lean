module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Laurent
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjLocalizedRingMap
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.DegreeOneChart

/-!
# The overlap of the two standard charts of the projective line is a Laurent ring

Grade `R[X₀, X₁]` by total degree. The projective line `Proj R[X₀, X₁]` is covered by the two
standard opens `D₊(X₀)` and `D₊(X₁)`, and their intersection is `D₊(X₀X₁)`. The ring of functions
on that intersection is the degree-zero part of the localization of `R[X₀, X₁]` at `X₀X₁`, which
is spanned by the fractions `X₀^a X₁^{-a}` for `a : ℤ`: it is the Laurent ring `R[t, t⁻¹]` in the
single coordinate `t = X₁ / X₀`.

This file proves exactly that, as an isomorphism of `R`-algebras. The route is the one the
scheme-theoretic picture dictates, and it reuses two results rather than computing with fractions:
`ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap` exhibits the functions on `D₊(X₀X₁)` as
the localization of the functions on `D₊(X₀)` at the single element `X₁ / X₀`, because `D₊(X₀X₁)`
is the standard open of the affine chart `D₊(X₀)` cut out by that function; and
`Stacks.SymmetricAway.chartAlgEquiv` identifies the functions on `D₊(X₀)` with a polynomial ring
in one variable, sending `X₁ / X₀` to the variable. Inverting the variable in a one-variable
polynomial ring gives the Laurent ring, which is `LaurentPolynomial.isLocalization`, so the two
localizations are localizations of isomorphic rings at corresponding elements and the comparison
is `IsLocalization.ringEquivOfRingEquiv`.

Together with `Stacks.ProjectiveSpace.TwistSections.twistSectionsOverlapEquivAway` — the sections
of `𝒪(d)` over `D₊(X₀X₁)` are free of rank one over this ring — this computes the overlap term of
the Čech complex of the standard two-chart cover of `ℙ¹_R`, the one term of that complex which is
not a chart term.

## Main definitions

* `Stacks.ProjectiveSpace.CechComparison.overlapRing` — the ring of functions on `D₊(X₀X₁)`.
* `Stacks.ProjectiveSpace.CechComparison.overlapRestrict` — restriction of functions from the
  chart `D₊(X₀)` to the overlap `D₊(X₀X₁)`.
* `Stacks.ProjectiveSpace.CechComparison.overlapParam` — the function `X₁ / X₀` on `D₊(X₀)`,
  whose inversion cuts the overlap out of the chart.
* `Stacks.ProjectiveSpace.CechComparison.chartRingAlgEquivPolynomial` — the chart `D₊(X₀)` of the
  projective line is the affine line.

## Main results

* `Stacks.ProjectiveSpace.CechComparison.isLocalizationAway_overlapParam` — the functions on the
  overlap are the functions on the chart with `X₁ / X₀` inverted.
* `Stacks.ProjectiveSpace.CechComparison.overlapAlgEquivLaurent` — **the overlap ring is the
  Laurent ring `R[t, t⁻¹]`.**

## Implementation notes

`Stacks.ProjectiveSpace.CechComparison.algebraOverlapRing` makes `R` act on the overlap ring
through the degree-zero part of the grading, exactly as
`Stacks.SymmetricAway.algebraChartRing` does for a chart ring; the degree-zero map
`overlapRestrict` is a map of `𝒜 0`-algebras, so the two actions are compatible and
`overlapAlgEquivLaurent` is `R`-linear.

The comparison is built from `IsLocalization.ringEquivOfRingEquiv` and then upgraded by
`AlgEquiv.ofRingEquiv`, rather than taken from `IsLocalization.algEquivOfAlgEquiv` directly: the
latter asks for `IsScalarTower R (chartRing R 0) (overlapRing R)`, whose statement is phrased with
bare `SMul` instances, and `SMul R (HomogeneousLocalization 𝒜 x)` resolves to Mathlib's
`HomogeneousLocalization.instSMul` — scalar multiplication of numerators — rather than to the
`Algebra.toSMul` of the structure map. The two agree mathematically but not syntactically. Going
through `algebraMap` equations avoids the question; nothing below mentions `SMul`.

No `@[stacks]` attribute is attached: nothing here is one of the assertions of a Stacks tag. The
identification of the functions on a standard open of `Proj` as a degree-zero localization is part
of tag 01M4, carried by `ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap`; the computation
of the cohomology of `𝒪(d)` on `ℙⁿ` is tag 01XT, which also needs the Čech comparison 01XD.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization MvPolynomial Stacks.SymmetricAway

universe u

namespace Stacks.ProjectiveSpace.CechComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- On the projective line there is exactly one coordinate other than `X₀`. -/
@[instance_reducible]
def uniqueNeZeroFinTwo : Unique {j : Fin 2 // j ≠ (0 : Fin 2)} where
  default := ⟨1, by decide⟩
  uniq j := Subtype.ext (by
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact absurd rfl hj
    · rfl)

attribute [local instance] uniqueNeZeroFinTwo

/-- **The standard chart `D₊(X₀)` of the projective line is the affine line.** The degree-zero
part of the localization of `R[X₀, X₁]` at `X₀` is the polynomial ring on the single fraction
`X₁ / X₀`; this is `Stacks.SymmetricAway.chartAlgEquiv` for `σ = Fin 2`, read in one variable. -/
def chartRingAlgEquivPolynomial (R : Type u) [CommRing R] :
    chartRing R (0 : Fin 2) ≃ₐ[R] Polynomial R :=
  (chartAlgEquiv (R := R) (0 : Fin 2)).symm.trans
    (MvPolynomial.uniqueAlgEquiv R {j : Fin 2 // j ≠ (0 : Fin 2)})

/-- `X₀X₁` is homogeneous of degree two. -/
theorem mul_X_mem_homogeneousSubmodule_two (R : Type u) [CommRing R] :
    (X 0 * X 1 : MvPolynomial (Fin 2) R) ∈ homogeneousSubmodule (Fin 2) R 2 := by
  simpa using SetLike.mul_mem_graded (X_mem_homogeneousSubmodule_one (R := R) (0 : Fin 2))
    (X_mem_homogeneousSubmodule_one (R := R) (1 : Fin 2))

/-- The ring of functions on the overlap `D₊(X₀X₁)` of the two standard charts of the projective
line: the degree-zero part of the localization of `R[X₀, X₁]` at `X₀X₁`. -/
abbrev overlapRing (R : Type u) [CommRing R] :=
  Away (homogeneousSubmodule (Fin 2) R) (X 0 * X 1)

/-- The overlap is contained in the first standard chart. -/
theorem basicOpen_mul_X_le (R : Type u) [CommRing R] :
    ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin 2) R) (X 0 * X 1) ≤
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin 2) R) (X 0) :=
  ProjectiveSpectrum.basicOpen_mul_le_left _ _ _

/-- Restriction of functions from the standard chart `D₊(X₀)` of the projective line to the
overlap `D₊(X₀X₁)` of the two charts. -/
def overlapRestrict (R : Type u) [CommRing R] :
    chartRing R (0 : Fin 2) →ₐ[homogeneousSubmodule (Fin 2) R 0] overlapRing R :=
  ProjectiveSpectrum.degreeZeroRingMap (homogeneousSubmodule (Fin 2) R) (X 0) (X 0 * X 1)
    ⟨1, one_pos, X_mem_homogeneousSubmodule_one 0⟩
    ⟨2, two_pos, mul_X_mem_homogeneousSubmodule_two R⟩ (basicOpen_mul_X_le R)

/-- The overlap ring is an algebra over the chart ring, by restriction of functions. -/
instance algebraChartRingOverlapRing : Algebra (chartRing R (0 : Fin 2)) (overlapRing R) :=
  (overlapRestrict R).toRingHom.toAlgebra

/-- The coefficient ring acts on the overlap ring through the degree-zero part of the grading,
as it does on a chart ring by `Stacks.SymmetricAway.algebraChartRing`. -/
instance algebraOverlapRing : Algebra R (overlapRing R) :=
  ((algebraMap (homogeneousSubmodule (Fin 2) R 0) (overlapRing R)).comp
    (algebraMap R (homogeneousSubmodule (Fin 2) R 0))).toAlgebra

/-- Restriction of functions to the overlap fixes the constants. -/
theorem algebraMap_overlapRing_eq (r : R) :
    algebraMap R (overlapRing R) r =
      algebraMap (chartRing R (0 : Fin 2)) (overlapRing R)
        (algebraMap R (chartRing R (0 : Fin 2)) r) :=
  ((overlapRestrict R).commutes (algebraMap R (homogeneousSubmodule (Fin 2) R 0) r)).symm

/-- The function `X₁ / X₀` on the standard chart `D₊(X₀)` of the projective line. Inverting it
cuts the overlap `D₊(X₀X₁)` out of that chart. -/
def overlapParam (R : Type u) [CommRing R] : chartRing R (0 : Fin 2) :=
  mkChart (0 : Fin 2) 1 (X 1) (X_mem_homogeneousSubmodule_one 1)

/-- **The coordinate of the overlap is the coordinate of the chart.** Under the identification of
`D₊(X₀)` with the affine line, the function `X₁ / X₀` is the variable. -/
theorem chartRingAlgEquivPolynomial_overlapParam (R : Type u) [CommRing R] :
    chartRingAlgEquivPolynomial R (overlapParam R) = Polynomial.X := by
  have hX : chartAlgEquiv (R := R) (0 : Fin 2) (X ⟨1, by decide⟩) = overlapParam R := by
    rw [chartAlgEquiv_apply, toChart_X]
    rfl
  rw [chartRingAlgEquivPolynomial, AlgEquiv.trans_apply, ← hX, AlgEquiv.symm_apply_apply]
  exact MvPolynomial.eval₂_X _ _ _

/-- **The functions on the overlap are the functions on the chart with `X₁ / X₀` inverted.** This
is `ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap` for `f = X₀` and `g = X₀X₁`, whose
degrees are `1` and `2`, so that the element it inverts is `(X₀X₁) / X₀²`; that fraction is
`X₁ / X₀`. -/
theorem isLocalizationAway_overlapParam (R : Type u) [CommRing R] :
    IsLocalization.Away (overlapParam R) (overlapRing R) := by
  have h : Away.mk (homogeneousSubmodule (Fin 2) R)
        (X_mem_homogeneousSubmodule_one (0 : Fin 2)) 2 ((X 0 * X 1) ^ 1) (by
          simpa [mul_comm] using
            SetLike.pow_mem_graded 1 (mul_X_mem_homogeneousSubmodule_two R))
      = overlapParam R := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, overlapParam, val_mkChart, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, pow_one]; ring⟩
  rw [← h]
  exact ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap (homogeneousSubmodule (Fin 2) R)
    (X 0) (X 0 * X 1) 1 2 one_pos two_pos (X_mem_homogeneousSubmodule_one 0)
    (mul_X_mem_homogeneousSubmodule_two R) (basicOpen_mul_X_le R)

attribute [local instance] isLocalizationAway_overlapParam

/-- The comparison of the overlap ring with the Laurent ring, as a ring isomorphism: both are
localizations of isomorphic rings at corresponding elements. -/
def overlapRingEquivLaurent (R : Type u) [CommRing R] :
    overlapRing R ≃+* LaurentPolynomial R :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (overlapParam R))
    (T := Submonoid.powers (Polynomial.X : Polynomial R))
    (overlapRing R) (LaurentPolynomial R) (chartRingAlgEquivPolynomial R).toRingEquiv
    (by rw [Submonoid.map_powers]
        exact congrArg Submonoid.powers (chartRingAlgEquivPolynomial_overlapParam R))

/-- **The overlap of the two standard charts of the projective line is a Laurent ring.** The
degree-zero part of the localization of `R[X₀, X₁]` at `X₀X₁` is `R[t, t⁻¹]`, the coordinate `t`
being the fraction `X₁ / X₀`. -/
def overlapAlgEquivLaurent (R : Type u) [CommRing R] :
    overlapRing R ≃ₐ[R] LaurentPolynomial R :=
  AlgEquiv.ofRingEquiv (f := overlapRingEquivLaurent R) fun r => by
    rw [overlapRingEquivLaurent, algebraMap_overlapRing_eq,
      IsLocalization.ringEquivOfRingEquiv_eq, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
      Polynomial.algebraMap_eq, LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]
    rfl

end Stacks.ProjectiveSpace.CechComparison

end
