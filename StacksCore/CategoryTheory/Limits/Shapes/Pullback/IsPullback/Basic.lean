module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import StacksCore.Tactic.StacksAttribute

/-! ## Pullback squares.

`IsPullback.prod_lift`: a pullback square stays a pullback after pairing its top and bottom maps
with compatible maps into a monomorphism. No zero morphisms are needed; the biproduct form
`IsPullback.biprod_lift` in
`StacksCore.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq`
is its transport along `biprod.isoProd`. -/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

namespace IsPullback

/-- Pairing a pullback square with a compatible map into a monomorphism: if the square with sides
`fst, snd, ι, f` is a pullback, `ι'` is a monomorphism and `g' ≫ ι' = snd ≫ g`, then the square
with sides `(fst, g'), snd, ι × ι', (f, g)` is a pullback. -/
theorem prod_lift {P X Y Z X' Z' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {ι : X ⟶ Z} {f : Y ⟶ Z}
    (h : IsPullback fst snd ι f) {ι' : X' ⟶ Z'} [Mono ι'] {g' : P ⟶ X'} {g : Y ⟶ Z'}
    (w : g' ≫ ι' = snd ≫ g) [HasBinaryProduct X X'] [HasBinaryProduct Z Z'] :
    IsPullback (prod.lift fst g') snd (prod.map ι ι') (prod.lift f g) := by
  refine of_isLimit' ⟨by ext <;> simp [h.w, w]⟩ (PullbackCone.IsLimit.mk _
    (fun s => h.lift (s.fst ≫ prod.fst) s.snd (by simpa using s.condition =≫ prod.fst))
    (fun s => ?_) (fun s => by simp) (fun s m h₁ h₂ => h.hom_ext (by simp [← h₁]) (by simp [h₂])))
  ext
  · simp
  · rw [← cancel_mono ι']
    simpa [w] using (s.condition =≫ prod.snd).symm

end IsPullback

end CategoryTheory
