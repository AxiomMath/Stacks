module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of zero objects

A retract of a zero object is a zero object. The statement needs no zero morphisms: the
retraction data already exhibit an isomorphism once the two morphisms out of the zero
object are identified.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

/-- A retract of a zero object is a zero object. -/
lemma IsZero.of_retract {C : Type u} [Category.{v} C] {X Y : C} (hX : IsZero X)
    (r : Retract Y X) : IsZero Y :=
  hX.of_iso ⟨r.i, r.r, r.retract, hX.eq_of_src _ _⟩

end CategoryTheory.Limits
