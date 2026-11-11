module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
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

/-! # Representability of the diagonal: the 1-categorical analogue

This file records the 1-categorical analogue of Stacks 02YA, Mathlib's
`Functor.relativelyRepresentable.diag_iff`: for a full functor `F : C ⥤ D` preserving binary
products and pullbacks and an object `X` of `D`, the diagonal `X ⟶ X ⨯ X` is relatively
representable with respect to `F` if and only if every morphism `F.obj a ⟶ X` is.

For `F = yoneda` this is the statement for presheaves, that is, for categories fibred in setoids.
It is not Stacks 02YA itself, which is about a category fibred in groupoids, its diagonal into the
2-fibre product `𝒮 ×_𝒞 𝒮`, and representability up to equivalence over the base: strict
pullbacks in a 1-category do not compute 2-fibre products. Stacks 02YA is
`Stacks.RepresentableMorphism.isRepresentableMorphism_diagonal_iff` in
`StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalRepresentable`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.relativelyRepresentable

/-- The 1-categorical analogue of Stacks 02YA: the diagonal `X ⟶ X ⨯ X` is relatively
representable with respect to `F` iff every morphism `F.obj a ⟶ X` out of an object in the image
of `F` is. Here `F : C ⥤ D` is full and preserves binary products and pullbacks, and `C` has
products of pairs and fibre products. For `F = yoneda` this is the case of presheaves, i.e. of
categories fibred in setoids; Stacks 02YA for categories fibred in groupoids is
`Stacks.RepresentableMorphism.isRepresentableMorphism_diagonal_iff`. -/
theorem diagonal_representable_iff
    {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D) (X : D)
    [HasPullbacks C] [HasBinaryProducts C]
    [HasBinaryProducts D] [HasPullbacks D] [HasTerminal D]
    [F.Full] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape WalkingCospan F] :
    F.relativelyRepresentable (Limits.diag X) ↔
      ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g :=
  Functor.relativelyRepresentable.diag_iff

end CategoryTheory.Functor.relativelyRepresentable
