module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# A morphism of presheaves whose sheafification is invertible is locally surjective

Let `C` be a site and let `f : P ⟶ Q` be a morphism of presheaves of types on `C`. If the
sheafified morphism `J.sheafifyMap f` is an isomorphism, then `f` is already locally surjective.

This is the direction of `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso` which reads
information *back* from the sheafification, and it is what turns a hypothetical isomorphism of
sheafifications into a concrete local statement about sections.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_of_isIso_sheafifyMap`.

## Implementation notes

The unit `J.toSheafify P` is locally surjective and the sheafified morphism is locally
surjective because it is an isomorphism, so the composite
`J.toSheafify P ≫ J.sheafifyMap f` is locally surjective; by naturality of the unit that
composite is `f ≫ J.toSheafify Q`. The unit `J.toSheafify Q` is locally injective, so
`CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac`
strips it off and leaves `f`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **A morphism of presheaves of types whose sheafification is an isomorphism is locally
surjective.** -/
theorem isLocallySurjective_of_isIso_sheafifyMap {P Q : Cᵒᵖ ⥤ Type max u v} (f : P ⟶ Q)
    (hf : IsIso (J.sheafifyMap f)) : IsLocallySurjective J f := by
  have := hf
  have hcomp : IsLocallySurjective J (f ≫ J.toSheafify Q) := by
    rw [J.toSheafify_naturality f]
    infer_instance
  exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac J
    (f₁ := f) (f₂ := J.toSheafify Q) (f ≫ J.toSheafify Q) rfl

end CategoryTheory.Presheaf

end
