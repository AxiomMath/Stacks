module

public import Mathlib.CategoryTheory.CommSq

/-!
# Transposing a naturality square across its two vertical isomorphisms

A commuting square whose two vertical edges are isomorphisms stays commuting when both of them
are inverted. Mathlib has this as `CategoryTheory.CommSq.horiz_inv`, phrased with the square
packaged as a `CategoryTheory.CommSq`; the lemma here is the same fact as a bare equation
between composites, which is the form in which the naturality of a comparison isomorphism is
carried around and rewritten with.

## Main results

* `CategoryTheory.iso_inv_naturality`: from `f ≫ e'.hom = e.hom ≫ g` conclude
  `g ≫ e'.inv = e.inv ≫ f`.
-/

@[expose] public section

namespace CategoryTheory

/-- **Turning a naturality square for the forward directions into one for the inverses.**  Given
a commuting square with vertical isomorphisms `e : A ≅ B` and `e' : A' ≅ B'`, horizontal edges
`f : A ⟶ A'` and `g : B ⟶ B'`, the square with both isomorphisms inverted commutes as well.

This is `CategoryTheory.CommSq.horiz_inv` read as an equation between composites. -/
lemma iso_inv_naturality {C : Type*} [Category* C]
    {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f :=
  (CommSq.horiz_inv (f := e) (i := e') ⟨h.symm⟩).w.symm

end CategoryTheory

end
