module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
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

/-!
# Sheafification of a constant presheaf and Mathlib's constant sheaf

Let `A` be an object of a category `D` admitting (weak) sheafification on a site `(C, J)`.
Mathlib *defines* the constant sheaf `(constantSheaf J D).obj A` as the sheafification of the
constant presheaf `(Functor.const Cᵒᵖ).obj A`, so `sheafifyConstantPresheafIso` is the identity
isomorphism between the two. It carries no mathematical content.

Stacks 0081 (Example 6.17.4) compares the sheafification of the constant presheaf with the sheaf
of locally constant maps (Stacks 006W); it is
`TopCat.isIso_sheafifyLift_constantPresheafToLocallyConstant` in
`StacksFrontier.Topology.Sheaves.Sheafify.LocallyConstant`.
-/

@[expose] public section

open CategoryTheory


universe v₁ v₂ u₁ u₂

/-- The sheafification of the constant presheaf `(Functor.const Cᵒᵖ).obj A` is Mathlib's
constant sheaf `(constantSheaf J D).obj A`. Mathlib *defines* the constant sheaf as this
sheafification, so this is the identity isomorphism. Stacks 0081, which compares the
sheafification with the sheaf of locally constant maps, is
`TopCat.isIso_sheafifyLift_constantPresheafToLocallyConstant`. -/
noncomputable def sheafifyConstantPresheafIso
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] [HasWeakSheafify J D] (A : D) :
    sheafify J ((Functor.const Cᵒᵖ).obj A) ≅ ((constantSheaf J D).obj A).obj :=
  Iso.refl _

/-- The isomorphism `sheafifyConstantPresheafIso` is induced (as a morphism of
presheaves) by the unit `toSheafify J _` of the sheafification adjunction at
the constant presheaf `(Functor.const Cᵒᵖ).obj A`: composing this unit with the
isomorphism gives back the unit. -/
lemma toSheafify_comp_sheafifyConstantPresheafIso_hom
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] [HasWeakSheafify J D] (A : D) :
    toSheafify J ((Functor.const Cᵒᵖ).obj A) ≫
        (sheafifyConstantPresheafIso J A).hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj A) :=
  Category.comp_id _
