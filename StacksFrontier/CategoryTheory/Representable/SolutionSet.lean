module

public import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
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

/-! # Corepresentability from a solution set

Stacks 0AHN: let `C` have all small limits and let `F : C ⥤ Type v` preserve them. If there is a
family `x : I → C` with elements `f i : F.obj (x i)` such that every `g : F.obj y` has the form
`F.map φ (f i)` for some `i` and some `φ : x i ⟶ y`, then `F` is corepresentable.

The solution set is a small weakly initial family in the category of elements `F.Elements`.
Mathlib supplies limits in this category, constructs an initial object from the weakly initial
family using products and wide equalizers, and turns that initial object into a corepresentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- **Stacks 0AHN** (solution-set criterion).

Let `C` be a category with all (small) limits and `F : C ⥤ Type v` a functor that
preserves limits. Suppose there is a family `{xᵢ}` of objects together with elements
`fᵢ ∈ F xᵢ` such that for every `y : C` and every `g ∈ F y` there exists an `i` and
a morphism `φ : xᵢ ⟶ y` with `F.map φ fᵢ = g`. Then `F` is corepresentable. -/
@[stacks 0AHN, sga "4 I 8.12.8.1" "Sufficiency direction"]
theorem isCorepresentable_of_solutionSet
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    {I : Type v} (x : I → C) (f : ∀ i, F.obj (x i))
    (hsurj : ∀ (y : C) (g : F.obj y), ∃ i, ∃ φ : x i ⟶ y, F.map φ (f i) = g) :
    F.IsCorepresentable := by
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts
    (C := F.Elements) (B := fun i => F.elementsMk (x i) (f i)) (by
      intro Y
      obtain ⟨i, φ, hφ⟩ := hsurj Y.obj Y.val
      exact ⟨i, ⟨⟨φ, hφ⟩⟩⟩)
  have : HasInitial F.Elements := hasInitial_of_weakly_initial_and_hasWideEqualizers hT
  exact Functor.Elements.isCorepresentable_of_hasInitial F

end CategoryTheory
