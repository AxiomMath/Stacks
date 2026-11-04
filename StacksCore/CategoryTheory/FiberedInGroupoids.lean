module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

/-! # Categories fibred in groupoids

The single canonical definition of a **category fibred in groupoids** (Stacks tag
`003S`), used throughout the Stacks formalization. A functor `p : 𝒮 ⥤ 𝒞` is fibred in
groupoids when every base morphism lifts (existence of lifts) and lifts satisfy the
existence-and-uniqueness of fill-ins.

The definition is phrased with Mathlib's `Functor.IsHomLift` (the idiomatic "`φ` lies
over `f`" predicate) rather than raw `eqToHom` bookkeeping. This is the *primitive*
form of the definition; the equivalent characterization "`p` is a fibred category and
every fibre is a groupoid" is Stacks `003V`.
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory

/-- A functor `p : 𝒮 ⥤ 𝒞` is *fibered in groupoids* (Stacks Project tag 003S). -/
structure IsFiberedInGroupoids {𝒮 𝒞 : Type*} [Category 𝒮] [Category 𝒞]
    (p : 𝒮 ⥤ 𝒞) : Prop where
  /-- Existence of lifts (Stacks 003S (a)): every base morphism `f : V ⟶ U` lifts to a
  morphism into any object `x` lying over `U` (the lift `φ : y ⟶ x` satisfies
  `p.IsHomLift f φ`, which also records that `y` lies over `V`). -/
  exists_lift : ∀ {V U : 𝒞} (f : V ⟶ U) (x : 𝒮), p.obj x = U →
    ∃ (y : 𝒮) (φ : y ⟶ x), p.IsHomLift f φ
  /-- Existence and uniqueness of fill-ins (Stacks 003S (b)): for every `φ : y ⟶ x`,
  `ψ : z ⟶ x` and every `f : p.obj z ⟶ p.obj y` with `f ≫ p.map φ = p.map ψ`, there is a
  unique `χ : z ⟶ y` with `p.map χ = f` and `χ ≫ φ = ψ`. -/
  unique_lift : ∀ {x y z : 𝒮} (φ : y ⟶ x) (ψ : z ⟶ x) (f : p.obj z ⟶ p.obj y),
    f ≫ p.map φ = p.map ψ → ∃! χ : z ⟶ y, p.map χ = f ∧ χ ≫ φ = ψ

end CategoryTheory.Functor
