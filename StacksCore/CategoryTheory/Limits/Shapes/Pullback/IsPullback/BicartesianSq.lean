module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
public import StacksCore.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import StacksCore.Tactic.StacksAttribute

/-! ## Bicartesian squares and biproducts.

`IsPullback.biprod_lift`: a pullback square stays a pullback after pairing its top and bottom maps
with compatible maps into a monomorphism. It is `IsPullback.prod_lift` transported along
`biprod.isoProd`. -/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace IsPullback

/-- Pairing a pullback square with a compatible map into a monomorphism: if the square with sides
`fst, snd, ι, f` is a pullback, `ι'` is a monomorphism and `g' ≫ ι' = snd ≫ g`, then the square
with sides `(fst, g'), snd, ι ⊕ ι', (f, g)` is a pullback. This is `IsPullback.prod_lift`
transported along `biprod.isoProd`. -/
theorem biprod_lift {P X Y Z X' Z' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {ι : X ⟶ Z} {f : Y ⟶ Z}
    (h : IsPullback fst snd ι f) {ι' : X' ⟶ Z'} [Mono ι'] {g' : P ⟶ X'} {g : Y ⟶ Z'}
    (w : g' ≫ ι' = snd ≫ g) [HasBinaryBiproduct X X'] [HasBinaryBiproduct Z Z'] :
    IsPullback (biprod.lift fst g') snd (biprod.map ι ι') (biprod.lift f g) := by
  refine (h.prod_lift w).of_iso (Iso.refl _) (biprod.isoProd X X').symm (Iso.refl _)
    (biprod.isoProd Z Z').symm ?_ ?_ ?_ ?_
  · ext <;> simp
  · simp
  · ext <;> simp
  · ext <;> simp

end IsPullback

end CategoryTheory
