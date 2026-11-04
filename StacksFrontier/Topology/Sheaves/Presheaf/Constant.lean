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
# Stacks 006F — The constant presheaf

Stacks 006F defines the constant presheaf with value a set `A` on a topological space `X`: it
assigns the set `A` to every open `U ⊆ X` and takes every restriction map to `id_A`.

It is realised here as `constantPresheaf`, Mathlib's constant functor `(Opens X)ᵒᵖ ⥤ Type` at
`A`, together with the two lemmas identifying its sections over every open with `A` and every
one of its restriction maps with the identity.
-/

@[expose] public section

/-- The constant presheaf on a topological space `X` with value the set `A`: the constant
functor `(Opens X)ᵒᵖ ⥤ Type` at `A`. -/
@[stacks 006F,
  ega "0 3.6.1",
  sga "4 IV 2.7.5" "special case",
  sga "4 IV 4.3.4" "special case",
  sga "4 IX 2.0" "partial"]
def constantPresheaf (X : TopCat) (A : Type) : TopCat.Presheaf Type X :=
  (CategoryTheory.Functor.const _).obj A

/-- The sections of the constant presheaf with value `A` over any open are `A` itself. -/
theorem constantPresheaf_obj (X : TopCat) (A : Type)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (constantPresheaf X A).obj U = A := rfl

/-- Every restriction map of the constant presheaf with value `A` is the identity of `A`. -/
theorem constantPresheaf_map (X : TopCat) (A : Type)
    (U V : (TopologicalSpace.Opens X)ᵒᵖ) (f : U ⟶ V) :
    (constantPresheaf X A).map f = CategoryTheory.CategoryStruct.id _ := rfl

