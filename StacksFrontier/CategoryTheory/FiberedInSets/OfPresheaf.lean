module

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
public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategoryIsCategory
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category fibred in sets attached to a presheaf

Stacks 04TM: a presheaf `F : 𝒞ᵒᵖ ⥤ Type*` gives a category `𝒮_F` over `𝒞` whose objects are
the pairs `(U, x)` with `x ∈ F(U)`, and whose morphisms `(V, y) ⟶ (U, x)` are the morphisms
`f : V ⟶ U` of `𝒞` with `f^* x = y`, composition being that of `𝒞`. The projection
`p_F : (U, x) ↦ U` is fibred in sets.

Mathlib's category of elements `F.Elements` has the same objects but the opposite arrows: a
morphism `(U, x) ⟶ (V, y)` of `F.Elements` is a morphism `op U ⟶ op V` of `𝒞ᵒᵖ`, that is an
`f : V ⟶ U` of `𝒞`, with `f^* x = y`. So `𝒮_F` is `(F.Elements)ᵒᵖ`, and `p_F` is
`(Functor.Elements.π F).leftOp`.

## Main definitions

* `CategoryTheory.Functor.presheafFiberedInSetsProjection`: the functor
  `p_F : (F.Elements)ᵒᵖ ⥤ 𝒞`, `(U, x) ↦ U`.

## Main results

* `CategoryTheory.Functor.isFiberedInSets_presheafFiberedInSetsProjection`: `p_F` is fibred in
  sets.

## References

* [Stacks Project, Tag 04TM](https://stacks.math.columbia.edu/tag/04TM)
-/

@[expose] public section

open CategoryTheory

/-- The category of elements `F.Elements` of a presheaf `F : Cᵒᵖ ⥤ Type*` (Mathlib's instance
on `Functor.Elements`): objects are the pairs `(U, x)` with `x ∈ F(U)`, and a morphism
`(U, x) ⟶ (V, y)` is a morphism `op U ⟶ op V` of `Cᵒᵖ`, that is an `f : V ⟶ U` of `C`, with
`f^* x = y`. Its arrows are opposite to those of the category `𝒮_F` of Stacks 04TM, which is
`(F.Elements)ᵒᵖ` (see `CategoryTheory.Functor.presheafFiberedInSetsProjection`). -/
@[reducible]
def elementsCategory {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type*) :
    Category F.Elements := inferInstance

namespace CategoryTheory.Functor

open Opposite

universe w v u

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)

/-- The functor `p_F : 𝒮_F ⥤ C`, `(U, x) ↦ U`, of Stacks 04TM, where `𝒮_F = (F.Elements)ᵒᵖ` has
the pairs `(U, x)` with `x ∈ F(U)` as objects and the `f : V ⟶ U` of `C` with `f^* x = y` as
morphisms `(V, y) ⟶ (U, x)`; it sends such a morphism to `f`. -/
abbrev presheafFiberedInSetsProjection : (F.Elements)ᵒᵖ ⥤ C :=
  (Elements.π F).leftOp

/-- **Stacks 04TM.** For a presheaf `F : Cᵒᵖ ⥤ Type*`, the category `𝒮_F = (F.Elements)ᵒᵖ`, whose
objects are the pairs `(U, x)` with `x ∈ F(U)` and whose morphisms `(V, y) ⟶ (U, x)` are the
`f : V ⟶ U` with `f^* x = y`, is fibred in sets over `C` by `p_F : (U, x) ↦ U`: a morphism
`f : V ⟶ U` and an object `(U, x)` have the unique lift `(V, f^* x) ⟶ (U, x)`. -/
@[stacks 04TM, sga "7 VI 1.1(a)" "set-valued F"]
instance isFiberedInSets_presheafFiberedInSetsProjection :
    (presheafFiberedInSetsProjection F).IsFiberedInSets where
  existsUnique_lift {U V} f x hx := by
    obtain ⟨@⟨⟨U'⟩, s⟩⟩ := x
    change U' = U at hx
    subst hx
    refine ⟨⟨op (F.elementsMk (op V) (F.map f.op s)), Quiver.Hom.op ⟨f.op, rfl⟩⟩,
      ⟨rfl, by simp⟩, ?_⟩
    rintro ⟨⟨@⟨⟨V'⟩, t⟩⟩, φ⟩ ⟨hy, hφ⟩
    change V' = V at hy
    subst hy
    have hf' : ((Elements.π F).map φ.unop).unop = f := by simpa using hφ
    have hf : φ.unop.hom = f.op := congrArg Quiver.Hom.op hf'
    have ht : t = F.map f.op s := by
      rw [← hf]
      exact φ.unop.map_val.symm
    subst ht
    congr
    exact Quiver.Hom.unop_inj (Elements.hom_ext hf)

end CategoryTheory.Functor
