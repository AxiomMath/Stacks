module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Normality of polynomial rings

If `R` is a normal ring, then so is the polynomial ring `R[x]` (Stacks 00H1). The case of a
normal *domain*, Stacks 030A, is Mathlib's: `R[X]` is a domain and is integrally closed
whenever `R` is an integrally closed domain, and Mathlib's instance
`instIsIntegrallyClosedPolynomialOfIsDomain` already carries the `@[stacks 030A]` tag, so no tag
is recorded here.

## References

* [Stacks Project, Tag 00H1](https://stacks.math.columbia.edu/tag/00H1)
-/

@[expose] public section


open Polynomial

/-- Stacks Lemma 10.37.14: if `R` is a normal ring, then the polynomial ring
`R[x]` (`Polynomial R`) is a normal ring. -/
@[stacks 00H1]
theorem polynomial_ring_normal (R : Type*) [CommRing R] (hR : IsNormalRing R) :
    IsNormalRing (Polynomial R) := by
  intro q hq
  set p : Ideal R := q.comap (Polynomial.C : R →+* Polynomial R)
  have : p.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨_, _⟩ := hR p
  obtain ⟨_, _⟩ : IsDomain (Polynomial (Localization.AtPrime p)) ∧
      IsIntegrallyClosed (Polynomial (Localization.AtPrime p)) := ⟨inferInstance, inferInstance⟩
  let : Algebra (Polynomial R) (Polynomial (Localization.AtPrime p)) :=
    Polynomial.algebra R (Localization.AtPrime p)
  set M : Submonoid (Polynomial R) := (p.primeCompl).map (Polynomial.C : R →+* Polynomial R)
  have : IsLocalization M (Polynomial (Localization.AtPrime p)) :=
    Polynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hMN : M ≤ q.primeCompl := by
    rintro x ⟨r, hr, rfl⟩
    exact hr
  let : Algebra (Polynomial (Localization.AtPrime p)) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ M q.primeCompl hMN
  have : IsScalarTower (Polynomial R) (Polynomial (Localization.AtPrime p))
      (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ M q.primeCompl hMN
  have : IsLocalization
      (q.primeCompl.map (algebraMap (Polynomial R) (Polynomial (Localization.AtPrime p))))
      (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ M q.primeCompl hMN
  have : Nontrivial (Localization.AtPrime q) := nontrivial_of_invariantBasisNumber _
  have hle : q.primeCompl.map (algebraMap (Polynomial R) (Polynomial (Localization.AtPrime p)))
      ≤ nonZeroDivisors (Polynomial (Localization.AtPrime p)) := by
    rintro y ⟨x, hxN, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h =>
      not_isUnit_zero (M₀ := Localization.AtPrime q) ?_
    rw [← map_zero (algebraMap (Polynomial (Localization.AtPrime p)) (Localization.AtPrime q)),
      ← h, ← IsScalarTower.algebraMap_apply]
    exact IsLocalization.map_units _ (⟨x, hxN⟩ : q.primeCompl)
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime q) hle,
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q) _ hle⟩
