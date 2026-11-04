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
# Codimension of an irreducible closed subset

The codimension of an irreducible closed subset `Y` of a topological space `X` is the coheight
of `Y` in the poset of irreducible closed subsets of `X` ordered by inclusion, equivalently the
supremum of the lengths of strict chains `Y = Y₀ ⊊ Y₁ ⊊ … ⊊ Y_e` of irreducible closed subsets
starting with `Y`.

## Main definitions

* `codimension`: the codimension of an irreducible closed subset, valued in `ℕ∞`.

## Main results

* `codimension_eq_coheight`: `codimension` agrees with `Order.coheight`.
* `codimension_iff_exists_chain`: `e ≤ codimension Y` exactly when there is a strict chain of
  irreducible closed subsets of length `e` starting at `Y`.
-/

@[expose] public section

open TopologicalSpace

/-- **Stacks 02I3**.
The codimension of an irreducible closed subset `Y` of a topological space `X`, defined as the
coheight of `Y` in the poset of irreducible closed subsets of `X` ordered by inclusion. This
equals the supremum of the lengths of strict chains `Y = Y₀ ⊊ Y₁ ⊊ … ⊊ Y_e` of irreducible
closed subsets starting with `Y`. -/
@[stacks 02I3, ega "0 14.2.1" "codim of irreducible Z", sga "1 II 5.9"]
noncomputable def codimension {X : Type*} [TopologicalSpace X]
    (Y : IrreducibleCloseds X) : ℕ∞ :=
  Order.coheight Y

/-- `codimension Y` is by definition the coheight of `Y` in the poset of irreducible closed
subsets. -/
theorem codimension_eq_coheight {X : Type*} [TopologicalSpace X]
    (Y : IrreducibleCloseds X) :
    codimension Y = Order.coheight Y := rfl

/-- `e ≤ codimension Y` exactly when there is a strict chain
`Y = Y₀ ⊊ Y₁ ⊊ … ⊊ Y_e` of irreducible closed subsets starting with `Y`. -/
@[ega "0 14.2.1"]
theorem codimension_iff_exists_chain {X : Type*} [TopologicalSpace X]
    (Y : IrreducibleCloseds X) (e : ℕ) :
    (e : ℕ∞) ≤ codimension Y ↔
      ∃ (p : LTSeries (IrreducibleCloseds X)), p.head = Y ∧ p.length = e :=
  ⟨Order.exists_series_of_le_coheight Y, fun ⟨_, hhead, hlen⟩ ↦
    hlen ▸ Order.length_le_coheight (hhead ▸ le_refl _)⟩

