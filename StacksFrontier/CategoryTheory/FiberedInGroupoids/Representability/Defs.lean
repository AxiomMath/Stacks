module
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
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
# Representable categories fibred in groupoids

Stacks 0046: a category fibred in groupoids `p : 𝒮 ⥤ 𝒞` is *representable* if there are an
object `X` of `𝒞` and an equivalence `j : 𝒮 ≌ 𝒞/X` in the 2-category of groupoids over `𝒞`,
that is, one whose forward functor composed with `Over.forget X` is isomorphic to `p`.
-/

@[expose] public section

open CategoryTheory Functor

/-- A category fibred in groupoids `p : 𝒮 ⥤ 𝒞` is *representable* if there exists
an object `X` of `𝒞` and an equivalence `j : 𝒮 ≌ Over X` over `𝒞`. -/
@[stacks_fixed 0046]
structure IsRepresentable {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) [IsFibered p] : Prop where
  exists_equiv : ∃ (X : 𝒞) (j : 𝒮 ≌ Over X),
    Nonempty (j.functor ⋙ Over.forget X ≅ p)

