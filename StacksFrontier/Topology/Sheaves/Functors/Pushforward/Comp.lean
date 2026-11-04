module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Functors
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
# Pushforward along a composition of continuous maps

For continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z` of topological spaces, pushing forward along
`g ∘ f` is the same as pushing forward along `f` and then along `g`. The statement is recorded
twice: `pushforward_comp_presheaf` for the pushforward functors on presheaves, and
`pushforward_comp_sheaf` for the pushforward functors on sheaves valued in a concrete category
with enough limits and colimits.

## References

* [Stacks Project, Tag 008E](https://stacks.math.columbia.edu/tag/008E)
-/

@[expose] public section

open CategoryTheory TopCat

universe v u

variable (C : Type u) [Category.{v} C]
variable {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- For continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z` of topological spaces, the pushforward
functor `(g ∘ f)_*` on presheaves is equal to the composition `g_* ∘ f_*`. -/
@[stacks 008E, ega "0 3.4.3"]
theorem pushforward_comp_presheaf :
    TopCat.Presheaf.pushforward C (f ≫ g) =
      (TopCat.Presheaf.pushforward C f) ⋙ (TopCat.Presheaf.pushforward C g) :=
  rfl

/-- For continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z` of topological spaces, the pushforward
functor `(g ∘ f)_*` on sheaves is equal to the composition `g_* ∘ f_*`. -/
@[stacks 008E, ega "0 3.4.3" "special case"]
theorem pushforward_comp_sheaf
    {A : Type u} [Category.{v} A]
    {FA : A → A → Type*} {CA : A → Type v}
    [∀ X Y : A, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA]
    [Limits.HasColimits A] [Limits.HasLimits A]
    [Limits.PreservesLimits (forget A)]
    [Limits.PreservesFilteredColimits (forget A)]
    [(forget A).ReflectsIsomorphisms] :
    TopCat.Sheaf.pushforward A (f ≫ g) =
      (TopCat.Sheaf.pushforward A f) ⋙ (TopCat.Sheaf.pushforward A g) :=
  rfl
