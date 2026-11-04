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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
# Almost integral elements and completely normal domains

For a domain `R`, an element `g` of the fraction field is almost integral over `R` when some
nonzero `r ∈ R` has `r • g ^ n ∈ R` for all `n`, and `R` is completely normal when every almost
integral element of its fraction field lies in `R`.

## Main definitions

* `IsCompletelyNormal`: every almost integral element of the fraction field lies in `R`.

## Main results

* `isAlmostIntegral_iff`: `IsAlmostIntegral R g` with the witness condition spelled `r ≠ 0`.
-/

@[expose] public section

/-- The `R[X]`-algebra structure on `K[X]` induced by an `R`-algebra structure on `K`. -/
noncomputable instance polynomialAlgebra (R K : Type*) [CommRing R] [CommRing K]
    [Algebra R K] : Algebra (Polynomial R) (Polynomial K) :=
  Polynomial.algebra R K

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDomain R]

/-- For a domain `R`, an element `g` of the fraction field is almost integral over `R` if and
only if there is a nonzero `r ∈ R` with `r • g ^ n` in the image of `R` for all `n`. -/
@[stacks 00GW "(1)"]
theorem isAlmostIntegral_iff (g : FractionRing R) :
    IsAlmostIntegral R g ↔
      ∃ r : R, r ≠ 0 ∧ ∀ n, r • g ^ n ∈ (algebraMap R (FractionRing R)).range := by
  simp_rw [IsAlmostIntegral, mem_nonZeroDivisors_iff_ne_zero]

/-- A domain `R` is *completely normal* if every almost integral element of its fraction field
lies in the image of `R`. -/
@[stacks 00GW "(2)"]
def IsCompletelyNormal (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ g : FractionRing R, IsAlmostIntegral R g → g ∈ (algebraMap R (FractionRing R)).range

end
