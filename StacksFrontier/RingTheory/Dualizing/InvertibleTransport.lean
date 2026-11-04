module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# Transport of invertibility along an isomorphism

Invertibility of an object of a monoidal category, `MonoidalCategory.IsInvertible`, depends only
on its isomorphism class: an object `X'` that is a two-sided tensor inverse of `X` is a two-sided
tensor inverse of any object isomorphic to `X`.

## Main results

* `Dualizing.isInvertible_of_iso`: invertibility transports along `e : X ≅ Y` from `X` to `Y`.
* `Dualizing.isInvertible_of_iso_symm`: the same statement read along `e.symm`, transporting
  invertibility from `Y` to `X`.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Dualizing

/-- Invertibility of an object of a monoidal category is a property of its isomorphism class: the
inverse of `X` is an inverse of `Y` for `e : X ≅ Y`, its two trivializations being those of `X`
tensored with `e.symm`. -/
theorem isInvertible_of_iso {C : Type*} [Category C] [MonoidalCategory C] {X Y : C}
    (e : X ≅ Y) (hX : MonoidalCategory.IsInvertible X) :
    MonoidalCategory.IsInvertible Y :=
  let ⟨h⟩ := hX
  ⟨{ inv := h.inv
     isoLeft := tensorIso e.symm (Iso.refl h.inv) ≪≫ h.isoLeft
     isoRight := tensorIso (Iso.refl h.inv) e.symm ≪≫ h.isoRight }⟩

/-- Invertibility transports backwards along an isomorphism as well: for `e : X ≅ Y` an inverse of
`Y` is an inverse of `X`. -/
theorem isInvertible_of_iso_symm {C : Type*} [Category C] [MonoidalCategory C] {X Y : C}
    (e : X ≅ Y) (hY : MonoidalCategory.IsInvertible Y) :
    MonoidalCategory.IsInvertible X :=
  isInvertible_of_iso e.symm hY

end Dualizing

end
