module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Whiskering

/-!
# Conjugating a commuting square of functors by equivalences

A square of functors whose two horizontal edges are equivalences can be read with those edges
reversed. Given equivalences `e : A ≌ A'` and `e' : C ≌ C'`, functors `Q : A ⥤ C` and
`P : A' ⥤ C'` and an isomorphism `e.functor ⋙ P ≅ Q ⋙ e'.functor`, the square with the two
equivalences replaced by their inverses again commutes.

## Main definitions

* `CategoryTheory.Equivalence.conjugateSquare`: the resulting isomorphism
  `e.inverse ⋙ Q ≅ P ⋙ e'.inverse`.
-/

@[expose] public section

namespace CategoryTheory.Equivalence

variable {A : Type*} [Category A] {A' : Type*} [Category A']
  {C : Type*} [Category C] {C' : Type*} [Category C']

/-- **Conjugate a commuting square of functors by equivalences on its two horizontal sides.**
The inverse of an equivalence replaces it on both sides at once: the comparison is built from
the unit of `e'` and the counit of `e`. -/
def conjugateSquare (e : A ≌ A') (e' : C ≌ C') {P : A' ⥤ C'} {Q : A ⥤ C}
    (α : e.functor ⋙ P ≅ Q ⋙ e'.functor) : e.inverse ⋙ Q ≅ P ⋙ e'.inverse :=
  (Functor.rightUnitor (e.inverse ⋙ Q)).symm ≪≫
    Functor.isoWhiskerLeft (e.inverse ⋙ Q) e'.unitIso ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight α.symm e'.inverse) ≪≫
    Functor.isoWhiskerRight e.counitIso (P ⋙ e'.inverse) ≪≫
    Functor.leftUnitor (P ⋙ e'.inverse)

end CategoryTheory.Equivalence

end
