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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible subsets of a topological space are retrocompact

A subset `E ⊆ X` is *constructible* if it can be written as a finite union
`⋃ i, U i ∩ (V i)ᶜ` where each `U i` and `V i` is a retrocompact open subset of `X`, and a
subset `s` is *retrocompact* when `s ∩ U` is quasi-compact for every quasi-compact open `U`.
Every constructible subset is retrocompact.

## Main definitions

* `IsConstructibleViaCompactOpens`: a finite union `⋃ i, U i ∩ (V i)ᶜ` of differences of
  retrocompact open subsets.

## Main results

* `isRetrocompact_iff`: the defining characterization of `IsRetrocompact`.
* `isRetrocompact_of_isConstructible`: every constructible subset is retrocompact.
-/

@[expose] public section


variable {X : Type*} [TopologicalSpace X]

/-- A subset `E ⊆ X` is *constructible* if it can be written as a finite union
`⋃ i, U i ∩ (V i)ᶜ` where each `U i` and `V i` is an open subset of `X` which is
retrocompact in `X`. (Mathlib's `IsRetrocompact` is the standard definition: `s` is
retrocompact if for every compact open `U`, the intersection `s ∩ U` is compact.) -/
@[ega "IV 10.1.1", ega "IV 8.3.9", sga "3 VIB 3.7"]
def IsConstructibleViaCompactOpens (E : Set X) : Prop :=
  ∃ (n : ℕ) (U V : Fin n → Set X),
    (∀ i, IsOpen (U i) ∧ IsRetrocompact (U i)) ∧
    (∀ i, IsOpen (V i) ∧ IsRetrocompact (V i)) ∧
    E = ⋃ i, U i ∩ (V i)ᶜ

/-- A subset `E` of `X` is retrocompact exactly when `E ∩ U` is quasi-compact for every
quasi-compact open `U ⊆ X`. -/
@[sga "3 VIA 2.6.3" "more general", sga "3 VIB 3.7" "more general"]
theorem isRetrocompact_iff (E : Set X) :
    IsRetrocompact E ↔ ∀ ⦃U : Set X⦄, IsCompact U → IsOpen U → IsCompact (E ∩ U) :=
  Iff.rfl

/-- **Stacks 09YH**.
Every constructible subset of a topological space is retrocompact. -/
@[stacks 09YH,
  ega "0 9.1.4",
  ega "0 9.1.13" "globally constructible",
  ega "0 9.1.5" "necessity direction"]
theorem isRetrocompact_of_isConstructible {E : Set X} (h : IsConstructibleViaCompactOpens E) :
    IsRetrocompact E := by
  obtain ⟨n, U, V, hU, hV, rfl⟩ := h
  intro W hWcomp hWopen
  rw [Set.iUnion_inter]
  refine isCompact_iUnion fun i ↦ ?_
  rw [Set.inter_right_comm]
  exact ((hU i).2 hWcomp hWopen).inter_right (hV i).1.isClosed_compl

