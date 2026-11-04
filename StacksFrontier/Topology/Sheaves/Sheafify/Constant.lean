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
# Sheafification of a constant presheaf is the constant sheaf (Stacks tag 0081)

Let `A` be an object of a category `D` admitting (weak) sheafification on a site
`(C, J)`. Write `A_p := (Functor.const Cᵒᵖ).obj A` for the constant presheaf with
value `A`. By definition (`CategoryTheory.constantSheaf`), the constant sheaf
`A^♯ := (constantSheaf J D).obj A` is the sheafification of `A_p`. Hence the
canonical map `A_p ⟶ (constantSheaf J D).obj A` from the constant presheaf to the
underlying presheaf of the constant sheaf, namely the unit of the sheafification
adjunction, induces an isomorphism `sheafify J A_p ≅ ((constantSheaf J D).obj A).obj`
on sheafifications. In words: the sheafification of the constant presheaf with
value `A` is the constant sheaf with value `A`.

The Stacks tag is stated for presheaves of sets on a topological space; the
statement and proof go through verbatim for any site, with the topological case
recovered by taking `C := (Opens X)ᵒᵖ` with its canonical Grothendieck topology
and `D := Type _`.
-/

@[expose] public section

open CategoryTheory


universe v₁ v₂ u₁ u₂

/-- **Stacks tag 0081.** The sheafification of the constant presheaf with value
`A` is the constant sheaf with value `A`. Concretely, the underlying presheaf of
the constant sheaf `(constantSheaf J D).obj A` is, by definition, the
sheafification of the constant presheaf `(Functor.const Cᵒᵖ).obj A`, so the
canonical comparison map is the identity isomorphism. -/
@[stacks 0081]
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
