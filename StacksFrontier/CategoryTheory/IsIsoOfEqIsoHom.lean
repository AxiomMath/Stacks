module

public import Mathlib.CategoryTheory.Iso

/-!
# A morphism equal to the forward map of an isomorphism

The forward map of an isomorphism is invertible, which Mathlib records as the instance
`CategoryTheory.Iso.isIso_hom`. A morphism that is only known to be *equal* to such a map is
invertible too, and that is the form stated here: instance synthesis sees the morphism, not the
equation, so it cannot reach the isomorphism on its own.

## Main results

* `CategoryTheory.isIso_of_eq_iso_hom`
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- A morphism equal to the forward map of an isomorphism is an isomorphism. -/
public theorem isIso_of_eq_iso_hom {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} (e : X ≅ Y)
    (h : f = e.hom) : IsIso f :=
  ⟨e.inv, (congrArg (fun g => g ≫ e.inv) h).trans e.hom_inv_id,
    (congrArg (fun g => e.inv ≫ g) h).trans e.inv_hom_id⟩

end CategoryTheory

end
