module

public import Mathlib.Order.CompletePartialOrder
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
public import StacksCore.Tactic.StacksAttribute

/-!
# Stratifications of a topological space

A *stratification* of a topological space `X` is a partition `X = ∐_{i ∈ I} X_i` together with a
partial ordering on `I` such that for each `j ∈ I` we have `closure (X_j) ⊆ ⋃_{i ≤ j} X_i`. The
parts `X_i` are the *strata* of the stratification.

## Main definitions

* `Stratification`: a stratification of `X` indexed by a partially ordered type `I`.
-/

@[expose] public section

/-- A *stratification* of a topological space `X`, indexed by a partially ordered type `I`, is an
indexed family `strata : I → Set X` whose members are pairwise disjoint and cover `X` (a partition
`X = ∐_{i} X_i`), and such that the closure of each stratum is contained in the union of the
strata at lower or equal indices. -/
@[stacks_fixed 09Y1]
structure Stratification (X : Type*) [TopologicalSpace X]
    (I : Type*) [PartialOrder I] where
  /-- The stratum indexed by `i`. -/
  strata : I → Set X
  /-- The strata are pairwise disjoint as an indexed family. -/
  pairwiseDisjoint : Pairwise (Function.onFun Disjoint strata)
  /-- The strata cover `X`. -/
  iUnion_eq_univ : ⋃ i, strata i = Set.univ
  /-- The closure of each stratum is contained in the union of all strata with index `≤ j`. -/
  closure_subset_iUnion_le :
    ∀ j : I, closure (strata j) ⊆ ⋃ i ≤ j, strata i

