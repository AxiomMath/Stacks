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
public import Mathlib.SetTheory.ZFC.PSet
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
# Finite unions of nowhere dense sets

The union of a finite collection of nowhere dense subsets of a topological space is nowhere
dense, in binary, `Finset`-indexed and unindexed form.

## Main results

* `isNowhereDense_iff_interior_closure_eq_empty`: `IsNowhereDense A` is equivalent to
  `interior (closure A) = ∅`.
* `isNowhereDense_empty_union`: the empty set is nowhere dense.
* `isNowhereDense_union`: the union of two nowhere dense sets is nowhere dense.
* `isNowhereDense_finite_union`: `⋃ i ∈ s, A i` is nowhere dense for a `Finset` `s` when each
  `A i` is.
* `isNowhereDense_sUnion_of_finite`: `⋃₀ S` is nowhere dense for a finite family `S` of
  nowhere dense sets.
* `StacksLemmaCompactSubsetSpectral`: the three forms bundled together.
-/

@[expose] public section

/-- `IsNowhereDense A` unfolds to `interior (closure A) = ∅`. -/
theorem isNowhereDense_iff_interior_closure_eq_empty
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsNowhereDense A ↔ interior (closure A) = ∅ :=
  Iff.rfl

/-- The empty set is nowhere dense. -/
theorem isNowhereDense_empty_union {X : Type*} [TopologicalSpace X] :
    IsNowhereDense (∅ : Set X) := by
  simp [IsNowhereDense]

/-- The union of two nowhere dense sets is nowhere dense. -/
theorem isNowhereDense_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsNowhereDense A) (hB : IsNowhereDense B) :
    IsNowhereDense (A ∪ B) := by
  exact hA.union hB

/-- Indexed finite union: if each `A i` for `i ∈ s` is nowhere dense, then
`⋃ i ∈ s, A i` is nowhere dense. -/
theorem isNowhereDense_finite_union {X : Type*} [TopologicalSpace X]
    {ι : Type*} (s : Finset ι) (A : ι → Set X)
    (h : ∀ i ∈ s, IsNowhereDense (A i)) :
    IsNowhereDense (⋃ i ∈ s, A i) := by
  exact IsNowhereDense.biUnion h

/-- The union of a finite collection of nowhere dense subsets is nowhere dense. -/
theorem isNowhereDense_sUnion_of_finite {X : Type*} [TopologicalSpace X]
    {S : Set (Set X)} (hS : S.Finite) (h : ∀ A ∈ S, IsNowhereDense A) :
    IsNowhereDense (⋃₀ S) := by
  rw [show (⋃₀ S) = ⋃ A ∈ hS.toFinset, A by ext; simp]
  exact isNowhereDense_finite_union _ _ fun A hA ↦ h A ((Set.Finite.mem_toFinset _).mp hA)

/-- **Stacks 03HO**. The union of a finite collection of nowhere dense subsets of a topological
space is nowhere dense, stated for a binary union, for a `Finset`-indexed family, and for the
union of a `Set.Finite` family of subsets. -/
@[stacks 03HO]
theorem StacksLemmaCompactSubsetSpectral :
    (∀ {X : Type*} [TopologicalSpace X] {A B : Set X},
        IsNowhereDense A → IsNowhereDense B → IsNowhereDense (A ∪ B)) ∧
    (∀ {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι) (A : ι → Set X),
        (∀ i ∈ s, IsNowhereDense (A i)) → IsNowhereDense (⋃ i ∈ s, A i)) ∧
    (∀ {X : Type*} [TopologicalSpace X] {S : Set (Set X)},
        S.Finite → (∀ A ∈ S, IsNowhereDense A) → IsNowhereDense (⋃₀ S)) :=
  ⟨fun hA hB => isNowhereDense_union hA hB,
   fun s A h => isNowhereDense_finite_union s A h,
   fun hS h => isNowhereDense_sUnion_of_finite hS h⟩
