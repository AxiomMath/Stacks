module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Presheaf
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 006O — The underlying presheaf of sets

Stacks 006O names the following construction. Let `X` be a topological space, `C` a category,
`F : C ⥤ Sets` a faithful functor and `𝓕` a presheaf on `X` with values in `C`. The presheaf of
sets `U ↦ F(𝓕(U))` is the *underlying presheaf of sets* of `𝓕`.

It is `underlyingPresheafSets` here, the composite `𝓕 ⋙ F`, together with the two lemmas
computing its sections over an open `U` as `F(𝓕(U))` and its restriction maps as `F` applied to
the restriction morphisms of `𝓕`.
-/

@[expose] public section

universe v u

open CategoryTheory TopologicalSpace

/-- The underlying presheaf of sets of a presheaf `𝓕` with values in a category `C`,
obtained by post-composing with a faithful functor `F : C ⥤ Type`. Its value on an
open `U` is `F (𝓕 U)`. -/
@[stacks 006O, sga "4 II 6.3.0" "object assignment of ε^"]
def underlyingPresheafSets
    {X : TopCat.{u}} {C : Type u} [Category.{v} C]
    (F : C ⥤ Type u) [F.Faithful] (𝓕 : TopCat.Presheaf C X) :
    TopCat.Presheaf (Type u) X :=
  𝓕 ⋙ F

/-- The value of the underlying presheaf of sets on an open `U` is `F (𝓕.obj U)`. -/
theorem underlyingPresheafSets_obj
    {X : TopCat.{u}} {C : Type u} [Category.{v} C]
    (F : C ⥤ Type u) [F.Faithful] (𝓕 : TopCat.Presheaf C X)
    (U : (Opens X)ᵒᵖ) :
    (underlyingPresheafSets F 𝓕).obj U = F.obj (𝓕.obj U) :=
  rfl

/-- The action on morphisms is `F` applied to the restriction maps of `𝓕`. -/
theorem underlyingPresheafSets_map
    {X : TopCat.{u}} {C : Type u} [Category.{v} C]
    (F : C ⥤ Type u) [F.Faithful] (𝓕 : TopCat.Presheaf C X)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (underlyingPresheafSets F 𝓕).map f = F.map (𝓕.map f) :=
  rfl

