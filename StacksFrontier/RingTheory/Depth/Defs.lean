module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Regular.RegularSequence
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth of a module over a local ring

The depth of a module over a local ring, defined through regular sequences in the maximal ideal,
and the Krull dimension of the support of a module.

## Main definitions

* `moduleDepth R M`: the supremum of the lengths of the `M`-regular sequences contained in the
  maximal ideal of the local ring `R`.
* `ringDepth R`: the depth of the local ring `R` as a module over itself.
* `moduleSupportDim R M`: the Krull dimension of the support of `M` in `PrimeSpectrum R`.
-/

@[expose] public section

/-- The depth of a module `M` over a local commutative ring `R`: the supremum,
over all `M`-regular sequences contained in the maximal ideal of `R`, of the
length of the sequence. -/
@[ega "0 16.4.5" "partial", sga "2 III 2.8" "prof M for a local ring"]
noncomputable def moduleDepth (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  ⨆ (xs : List R)
    (_ : (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
         RingTheory.Sequence.IsRegular M xs),
    (xs.length : ℕ∞)

/-- The depth of a commutative local ring `R`, viewed as a module over itself. -/
@[ega "0 16.4.5" "special case", sga "2 III 2.8" "special case"]
noncomputable def ringDepth (R : Type*) [CommRing R] [IsLocalRing R] : ℕ∞ :=
  moduleDepth R R

/-- The Krull dimension of the support of `M` as a topological subspace of
`PrimeSpectrum R`. -/
@[ega "IV 5.1.12"]
noncomputable def moduleSupportDim (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] : WithBot ℕ∞ :=
  topologicalKrullDim (Module.support R M)
