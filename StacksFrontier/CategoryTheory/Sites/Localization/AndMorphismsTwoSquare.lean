module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
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
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms

/-!
Isomorphisms of presheaves and sheaves induced by a two-square of functors.
-/

section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
open CategoryTheory Limits
open CategoryTheory Opposite

namespace Stacks.Sites.CocontinuousExchange

section Presheaf

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {A : Type u₅} [Category.{v₅} A] {u' : C' ⥤ D'}
  {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D}

variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
  [∀ F : C'ᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F]

/-- **Stacks 0FN1 for presheaves, for a Guitart exact `2`-square** `w : v' ⋙ u ⟶ u' ⋙ v`: right
Kan extension along `u.op` followed by restriction along `v.op` agrees with restriction along
`v'.op` followed by right Kan extension along `u'.op`, by the base change transformation of the
opposite square. -/
@[expose] public noncomputable def presheafIsoOfTwoSquareAndMorphismsTwoSquare
    (w : TwoSquare v' u' u v) [w.GuitartExact] :
    u.op.ran ⋙ (Functor.whiskeringLeft D'ᵒᵖ Dᵒᵖ A).obj v.op ≅
      (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ A).obj v'.op ⋙ u'.op.ran :=
  asIso w.op.ranBaseChange

/-- The comparison of `presheafIsoOfTwoSquareAndMorphismsTwoSquare` is the base change
transformation of the opposite square. -/
public theorem presheafIsoOfTwoSquare_hom_andMorphismsTwoSquare (w : TwoSquare v' u' u v)
    [w.GuitartExact] :
    (presheafIsoOfTwoSquareAndMorphismsTwoSquare (A := A) w).hom = w.op.ranBaseChange :=
  rfl

end Presheaf

section Sheaf

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (A : Type u₅) [Category.{v₅} A]
  (J' : GrothendieckTopology C') (J : GrothendieckTopology C) (K' : GrothendieckTopology D')
  (K : GrothendieckTopology D) {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D}
  [u.IsCocontinuous J K] [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v'.IsContinuous J' J]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
  [∀ F : C'ᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F]

/-- **The first conclusion of Stacks 0FN1, for a Guitart exact `2`-square** `w`:
`f'_* ∘ (g')⁻¹ ≅ g⁻¹ ∘ f_*`, obtained from `presheafIsoOfTwoSquareAndMorphismsTwoSquare` through
the fully faithful inclusion of sheaves into presheaves. -/
@[expose] public noncomputable def sheafIsoOfTwoSquareAndMorphismsTwoSquare
    (w : TwoSquare v' u' u v) [w.GuitartExact] :
    v'.sheafPushforwardContinuous A J' J ⋙ u'.sheafPushforwardCocontinuous A J' K' ≅
      u.sheafPushforwardCocontinuous A J K ⋙ v.sheafPushforwardContinuous A K' K :=
  ((fullyFaithfulSheafToPresheaf K' A).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (sheafToPresheaf J A)
      (presheafIsoOfTwoSquareAndMorphismsTwoSquare w).symm)

/-- On underlying presheaves, the inverse of `sheafIsoOfTwoSquareAndMorphismsTwoSquare` is the base
change transformation of the opposite square. -/
public theorem sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare (w : TwoSquare v' u' u v)
    [w.GuitartExact] (F : Sheaf J A) :
    ((sheafIsoOfTwoSquareAndMorphismsTwoSquare A J' J K' K w).inv.app F).hom =
      w.op.ranBaseChange.app F.obj :=
  rfl

end Sheaf

end Stacks.Sites.CocontinuousExchange

namespace CategoryTheory.Functor

@[expose] public section

end

end CategoryTheory.Functor

end

section

universe u
open CategoryTheory Limits
open CategoryTheory

namespace CategoryTheory.Functor

@[expose] public section

end

end CategoryTheory.Functor

end

section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
open CategoryTheory

namespace CategoryTheory.Functor

@[expose] public section

end

end CategoryTheory.Functor

end
