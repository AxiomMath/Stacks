module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# Cancelling a retraction off the right end of a composite

A morphism `g` with a retraction `g'` contributes nothing to the right end of a composite. The
two lemmas here differ only in how the part of the composite that survives is bracketed, which
is what makes each usable without a reassociation at the point of use. Every object is a
variable in both, so `exact`ing one at a composite whose objects are large semireducible terms
matches them at default transparency and unfolds none of them.

## Main results

* `CategoryTheory.comp_cancel_right`: cancelling the retraction off `(a ≫ g) ≫ g'`.
* `CategoryTheory.comp_comp_cancel_right`: the same with the surviving composite bracketed to
  the right, `(f ≫ g ≫ h) ≫ k`.
-/

@[expose] public section

namespace CategoryTheory

/-- `(a ≫ g) ≫ g' = a` for a `g` with a retraction `g'`. -/
lemma comp_cancel_right {D : Type*} [Category D] {X Y Z : D} (a : X ⟶ Y) {g : Y ⟶ Z}
    {g' : Z ⟶ Y} (h : g ≫ g' = 𝟙 Y) : (a ≫ g) ≫ g' = a := by
  rw [Category.assoc, h, Category.comp_id]

/-- `(f ≫ g ≫ h) ≫ k = f ≫ g` for an `h` with a retraction `k`: the same cancellation as
`CategoryTheory.comp_cancel_right`, with the surviving composite bracketed to the right. -/
lemma comp_comp_cancel_right {D : Type*} [Category D] {W₀ W₁ W₂ W₃ : D} (f : W₀ ⟶ W₁)
    (g : W₁ ⟶ W₂) (h : W₂ ⟶ W₃) (k : W₃ ⟶ W₂) (hk : h ≫ k = 𝟙 W₂) :
    (f ≫ g ≫ h) ≫ k = f ≫ g := by
  rw [← Category.assoc f g h]
  exact comp_cancel_right (f ≫ g) hk

end CategoryTheory

end
