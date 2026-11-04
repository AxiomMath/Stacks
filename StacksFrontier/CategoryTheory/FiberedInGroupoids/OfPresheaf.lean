module

import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Split
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category fibred in groupoids attached to a presheaf of groupoids

Let `𝒞` be a category and let `F : 𝒞ᵒᵖ ⥤ Grpd` be a functor to the category of groupoids
(Stacks 003N). Stacks 0049 is the analogue of Stacks 02XV for presheaves of *groupoids*: the
category `𝒮_F` built from `F` — objects the pairs `(U, x)` with `x` an object of `F(U)`, morphisms
`(V, y) ⟶ (U, x)` the pairs `(f, φ)` with `φ : y ⟶ f^* x` in `F(V)`, projection `(U, x) ↦ U` — is
fibred in groupoids over `𝒞`, and not merely a fibred category.

## Main results

* `CategoryTheory.isGroupoid_fiber_presheafOfGroupoids`: every fibre category of `𝒮_F` over `𝒞` is
  a groupoid, being equivalent to the groupoid `F(U)`;
* `CategoryTheory.isFiberedInGroupoids_presheafOfGroupoids`, Stacks 0049: `𝒮_F` is fibred in
  groupoids over `𝒞`.

## Implementation notes

The category `𝒮_F` and its projection are `CategoryTheory.presheafOfGroupoids`
(`StacksFrontier.CategoryTheory.FiberedInGroupoids.Split`), i.e. the category of Stacks 02XV
applied to the presheaf of categories `F ⋙ Grpd.forgetToCat` underlying `F`; that it is a
fibred category, with the source's cartesian lifts `(f, id_{f^* x})`, is Stacks 02XV, proved in
`StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf`. What Stacks 0049 adds — and what
Stacks 04TL flags as missing — is fibredness in *groupoids*, which is proved here.

The source proves the two clauses of Stacks 003T directly. We instead go through Stacks 003V
(`CategoryTheory.Functor.IsFiberedInGroupoids.mk'`), which is the route the source itself offers
first: `𝒮_F` is a fibred category by Stacks 02XV, and its fibre over `U` is equivalent to `F(U)` by
Mathlib's `HasFibers` structure on the Grothendieck construction, hence a groupoid. The existence
of lifts and the uniqueness of the fill-in `ν = (h^* φ)⁻¹ ∘ ψ` are then the two fields of
`CategoryTheory.Functor.IsFiberedInGroupoids`.
-/

@[expose] public section

namespace CategoryTheory

open Opposite Pseudofunctor Pseudofunctor.CoGrothendieck

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, u₂})

/-- The fibre category of `𝒮_F` over an object `U` of `𝒞` is a groupoid: it is equivalent to
`F(U)`, which is one. -/
theorem isGroupoid_fiber_presheafOfGroupoids (U : 𝒞) :
    IsGroupoid ((presheafOfGroupoids F).p.Fiber U) :=
  have : IsGroupoid ((F ⋙ Grpd.forgetToCat).toPseudofunctor'.obj ⟨op U⟩) :=
    inferInstanceAs (IsGroupoid (Grpd.forgetToCat.obj (F.obj (op U))))
  have key : IsGroupoid
      ((CoGrothendieck.forget (F ⋙ Grpd.forgetToCat).toPseudofunctor').Fiber U) :=
    isGroupoid_of_reflects_iso
      (Functor.Fiber.inducedFunctor
        (CoGrothendieck.comp_const (F ⋙ Grpd.forgetToCat).toPseudofunctor'
          U)).asEquivalence.inverse
  key

/-- **Stacks 0049.**
The category `𝒮_F` attached to a presheaf of groupoids `F : 𝒞ᵒᵖ ⥤ Grpd` is fibred in groupoids
over `𝒞`: every morphism of `𝒞` lifts, and every fill-in problem has a unique solution. -/
@[stacks 0049, sga "4 VI 6.1.3" "strict, groupoid fibers", sga "7 VI 1.1(a)" "groupoid-valued F"]
theorem isFiberedInGroupoids_presheafOfGroupoids :
    (presheafOfGroupoids F).p.IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.mk' (isGroupoid_fiber_presheafOfGroupoids F)

end CategoryTheory
