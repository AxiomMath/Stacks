module
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
@[expose] public section


open UniqueFactorizationMonoid

/-- The property that every nonzero ideal of `R` can be written as a product
of nonzero prime ideals, uniquely up to permutation. -/
@[stacks 034W]
def HasUniquePrimeIdealFactorization (R : Type*) [CommRing R] : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ →
    ∃! f : Multiset (Ideal R),
      (∀ P ∈ f, P.IsPrime ∧ P ≠ ⊥) ∧ f.prod = I

/-- A Dedekind domain `R` has the property that every nonzero ideal admits a
unique factorization (as a multiset) into nonzero prime ideals. -/
theorem hasUniquePrimeIdealFactorization_of_isDedekindDomain
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    HasUniquePrimeIdealFactorization R := by
  intro I hI
  refine ⟨normalizedFactors I, ⟨fun P hP =>
    have hPrime := prime_of_normalized_factor P hP
    ⟨Ideal.isPrime_of_prime hPrime, hPrime.ne_zero⟩,
    Ideal.prod_normalizedFactors_eq_self hI⟩, ?_⟩
  rintro f ⟨hPrime, hProd⟩
  -- Uniqueness from `prime_factors_unique`; for ideals `Associated` is equality.
  exact Multiset.rel_eq.mp <| (prime_factors_unique
    (fun P hP => Ideal.prime_of_isPrime (hPrime P hP).right (hPrime P hP).left)
    (fun P hP => prime_of_normalized_factor P hP)
    (by rw [hProd, Ideal.prod_normalizedFactors_eq_self hI]; exact Associated.rfl)).mono
    fun _ _ _ _ h => associated_iff_eq.mp h

