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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The node ring `R = {f ∈ k[x] ∣ f(0) = f(1)}`

The Stacks example records the ring `R` cut out from `k[x]` by the affine
condition `f(0) = f(1)` and asserts a computation of its Grothendieck groups
`K₀(R) ≅ k^× ⊕ ℤ` and `K'₀(R) = ℤ`. Mathlib does not formalize `K₀` or `K'₀`
of a commutative ring, so the K-group statement is not yet expressible in
Lean. We record the ring data faithfully: the subring `R` itself together
with the membership characterization, and a concrete witness `x · (x - 1) ∈ R`
showing the subring properly contains the scalars.
-/

@[expose] public section


open Polynomial

/-- The "node" ring `R = {f ∈ k[x] ∣ f(0) = f(1)}`, the subring of polynomials
agreeing at `0` and `1`. -/
@[stacks 00JG, ega "IV 6.5.5"]
def nodeRing (k : Type*) [Field k] : Subring (Polynomial k) where
  carrier := {f | f.eval 0 = f.eval 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Polynomial.eval_mul] at *
    rw [ha, hb]
  one_mem' := by simp [Set.mem_ofPred_eq]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Polynomial.eval_add] at *
    rw [ha, hb]
  zero_mem' := by simp [Set.mem_ofPred_eq]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Polynomial.eval_neg] at *
    rw [ha]

/-- Membership in the node ring `R` unfolds to the defining condition
`f(0) = f(1)`. -/
lemma mem_nodeRing_iff {k : Type*} [Field k] (f : Polynomial k) :
    f ∈ nodeRing k ↔ f.eval 0 = f.eval 1 := Iff.rfl

/-- The polynomial `x · (x - 1)` lies in the node ring: it vanishes at both
`0` and `1`. This witnesses that `R` properly contains the scalar subring. -/
lemma X_mul_X_sub_one_mem_nodeRing (k : Type*) [Field k] :
    Polynomial.X * (Polynomial.X - 1) ∈ nodeRing k := by
  simp [mem_nodeRing_iff]

