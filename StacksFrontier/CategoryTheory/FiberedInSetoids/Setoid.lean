module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
# Setoids

Stacks 02XZ: a category is a *setoid* if it is a groupoid in which every object has exactly
one automorphism, the identity. Unfolded, this is the conjunction of "every morphism is an
isomorphism" and "every endomorphism `f : X ⟶ X` equals `𝟙 X`"; equivalently, it is a thin
groupoid, so a setoid is the same thing as a set with an equivalence relation on it.
-/

@[expose] public section

open CategoryTheory

/-- **Stacks 02XZ.** A category `C` is a *setoid* when every morphism of `C` is an
isomorphism and every endomorphism `f : X ⟶ X` is `𝟙 X`; equivalently `C` is a thin groupoid,
so a setoid is a set together with an equivalence relation on it. -/
@[stacks 02XZ, sga "4 I 6.5.1" "discrete category def"]
def IsSetoidCategory (C : Type*) [Category C] : Prop :=
  (∀ {X Y : C} (f : X ⟶ Y), IsIso f) ∧ (∀ (X : C) (f : X ⟶ X), f = 𝟙 X)

/-- A category is a setoid if and only if every morphism is an isomorphism and every
endomorphism is the identity. -/
theorem isSetoid_iff (C : Type*) [Category C] :
    IsSetoidCategory C ↔ (∀ {X Y : C} (f : X ⟶ Y), IsIso f) ∧ (∀ (X : C) (f : X ⟶ X), f = 𝟙 X) :=
  Iff.rfl
