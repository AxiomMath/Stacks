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

/-! # Stacks 003F: the interchange law for natural transformations

Horizontal composition `◫` and vertical composition `≫` of natural transformations commute:
for `t : F ⟶ F'`, `t' : F' ⟶ F''` in `A ⥤ B` and `s : G ⟶ G'`, `s' : G' ⟶ G''` in `B ⥤ C`,
`(t ≫ t') ◫ (s ≫ s') = (t ◫ s) ≫ (t' ◫ s')`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.NatTrans

/-- **Stacks 003F** (interchange law). The horizontal (`◫`) and vertical (`≫`)
compositions of natural transformations satisfy
`(t ≫ t') ◫ (s ≫ s') = (t ◫ s) ≫ (t' ◫ s')`. -/
@[stacks 003F]
theorem horiz_vert_interchange
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    {F F' F'' : A ⥤ B} {G G' G'' : B ⥤ C}
    (t : F ⟶ F') (t' : F' ⟶ F'')
    (s : G ⟶ G') (s' : G' ⟶ G'') :
    (t ≫ t') ◫ (s ≫ s') = (t ◫ s) ≫ (t' ◫ s') :=
  NatTrans.exchange t t' s s'

end CategoryTheory.NatTrans
