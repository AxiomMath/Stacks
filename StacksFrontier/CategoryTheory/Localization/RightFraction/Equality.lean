module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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

/-!
# When two right fractions define the same morphism of `S⁻¹𝒞`

Stacks 04VJ: let `S` be a right multiplicative system on `𝒞` and let `L : 𝒞 ⥤ D` be a
localization functor for `S`. Two right fractions `φ, ψ : X ⟶ Y` have the same image in the
localization if and only if they are `RightFractionRel`-related, i.e. if and only if they become
equal after precomposition with a suitable morphism of `S`.
-/

@[expose] public section

open CategoryTheory MorphismProperty

/-- **Stacks 04VJ.** For a right multiplicative system `W` on `C` and a localization functor
`L : C ⥤ D` at `W`, two right fractions `φ ψ : X ⟶ Y` have the same image in `D` if and only if
`RightFractionRel φ ψ`, i.e. if and only if they agree after precomposition with a suitable
morphism of `W`. -/
@[stacks 04VJ]
theorem map_eq_iff_rightFractionRel {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {W : MorphismProperty C} [W.HasRightCalculusOfFractions] [L.IsLocalization W]
    {X Y : C} (φ ψ : W.RightFraction X Y) :
    φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _ _) ↔
      RightFractionRel φ ψ := by
  have h_main : φ.map L (Localization.inverts _ _) = ψ.map L (Localization.inverts _
      _) ↔ RightFractionRel φ ψ := by grind only [RightFraction.map_eq_iff]
  grind
