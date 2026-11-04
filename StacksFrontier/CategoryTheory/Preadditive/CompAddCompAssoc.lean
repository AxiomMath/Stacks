module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Composing on both sides of a sum

In a preadditive category, composition is bilinear, so a sum sitting in the middle of a triple
composite distributes over the two outer factors. `Preadditive.add_comp` and
`Preadditive.comp_add` each handle one side; this file records the two-sided form, which is the
shape that arises whenever an additive map is built out of a conjugation `a ≫ - ≫ c` by a pair
of isomorphisms.

## Main results

* `CategoryTheory.Preadditive.comp_add_comp_assoc`: `a ≫ (f + g) ≫ c = a ≫ f ≫ c + a ≫ g ≫ c`.
-/

@[expose] public section

namespace CategoryTheory

namespace Preadditive

/-- Composing on both sides distributes over a sum in the middle. -/
public theorem comp_add_comp_assoc {C : Type*} [Category C] [Preadditive C] {W X Y Z : C}
    (a : W ⟶ X) (f g : X ⟶ Y) (c : Y ⟶ Z) :
    a ≫ (f + g) ≫ c = a ≫ f ≫ c + a ≫ g ≫ c := by
  rw [Preadditive.add_comp, Preadditive.comp_add]

end Preadditive

end CategoryTheory

end
