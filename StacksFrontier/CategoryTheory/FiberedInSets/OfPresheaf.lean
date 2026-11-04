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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category fibred in sets attached to a presheaf

Stacks 04TM: a presheaf `F : 𝒞ᵒᵖ ⥤ Type*` gives a category `𝒮_F` over `𝒞` whose objects are
the pairs `(U, x)` with `x ∈ F(U)`, and whose morphisms `(V, y) ⟶ (U, x)` are the morphisms
`f : V ⟶ U` of `𝒞` with `f^* x = y`; the projection `(U, x) ↦ U` has discrete fibres `F(U)`,
so `𝒮_F` is fibred in sets. This is Mathlib's category of elements of `F`.
-/

@[expose] public section

open CategoryTheory

/-- **Stacks 04TM.** The category `𝒮_F` attached to a presheaf `F : Cᵒᵖ ⥤ Type*`: objects are
the pairs `(U, x)` with `x ∈ F(U)`, and a morphism `(V, y) ⟶ (U, x)` is an `f : V ⟶ U` of `C`
with `f^* x = y`. This is Mathlib's category of elements of `F`. -/
@[reducible, stacks 04TM, sga "7 VI 1.1(a)" "set-valued F"]
def elementsCategory {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type*) :
    Category F.Elements := categoryOfElements F
