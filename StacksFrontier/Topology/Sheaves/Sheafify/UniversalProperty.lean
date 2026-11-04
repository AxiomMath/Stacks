module

public import Mathlib.CategoryTheory.Sites.Sheafification
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal property of sheafification (Stacks tag 0080)

Let `F` be a presheaf on a site `(C, J)` and let `G` be a sheaf. Then any morphism
`η : F ⟶ G` factors uniquely as `F → F^# → G`, where `F → F^#` is the canonical
map from `F` to its sheafification. This is the universal property of the
sheafification, packaged here as an existence-and-uniqueness statement using
Mathlib's `CategoryTheory.sheafifyLift`, `CategoryTheory.toSheafify_sheafifyLift`,
and `CategoryTheory.sheafifyLift_unique`.

The Stacks tag is stated for presheaves of sets on a topological space, but the
statement and proof go through verbatim for any site `(C, J)` (whenever
sheafification is available); the topological case is recovered by taking `C` to
be `(Opens X)ᵒᵖ` with its canonical Grothendieck topology and `D := Type _`.
-/

@[expose] public section

open CategoryTheory


universe v₁ v₂ u₁ u₂

/-- **Stacks tag 0080.** Any morphism from a presheaf `F` to a sheaf `G`
factors uniquely as `F → F^# → G`, where `F → F^#` is the canonical
morphism from `F` to its sheafification. -/
@[stacks 0080, ega "0 3.5.3" "partial, special case", ega "0 3.5.6" "more general"]
theorem sheafify_universal_property
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] [HasWeakSheafify J D]
    {F G : Cᵒᵖ ⥤ D} (η : F ⟶ G) (hG : Presheaf.IsSheaf J G) :
    ∃! γ : sheafify J F ⟶ G, toSheafify J F ≫ γ = η :=
  ⟨sheafifyLift J η hG, toSheafify_sheafifyLift J η hG,
    fun γ h => sheafifyLift_unique J η hG γ h⟩
