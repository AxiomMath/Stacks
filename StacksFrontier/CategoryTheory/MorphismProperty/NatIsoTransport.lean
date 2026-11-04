module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Transporting a morphism property along an isomorphism of functors

If a class `W` of morphisms respects isomorphisms and `Φ₁ ≅ Φ₂` are isomorphic functors, then
`Φ₁` carries a morphism into `W` exactly when `Φ₂` does: the naturality square of the
isomorphism is an isomorphism of arrows between the two images.

Mathlib has the corresponding statement for a single morphism being an isomorphism
(`CategoryTheory.NatIso.isIso_map_iff`) and for a whole class being inverted
(`CategoryTheory.MorphismProperty.IsInvertedBy.iff_of_iso`), but not this one.

## Main results

* `CategoryTheory.MorphismProperty.of_natIso_map`: the transport for a single morphism.
* `CategoryTheory.MorphismProperty.natIso_map_iff`: the same as an iff.
* `CategoryTheory.MorphismProperty.le_inverseImage_of_natIso`: the transport of a containment
  in an inverse image, which is the form in which preservation of a class of morphisms by a
  functor is usually stated.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

variable {C D : Type*} [Category* C] [Category* D] {W : MorphismProperty D} [W.RespectsIso]
  {Φ₁ Φ₂ : C ⥤ D}

/-- If `W` respects isomorphisms and `Φ₁ ≅ Φ₂`, then `W (Φ₁.map f)` implies `W (Φ₂.map f)`. -/
theorem of_natIso_map (e : Φ₁ ≅ Φ₂) {A B : C} {f : A ⟶ B} (h : W (Φ₁.map f)) :
    W (Φ₂.map f) :=
  (W.arrow_mk_iso_iff (Arrow.isoMk (e.app A) (e.app B) (by simp))).1 h

/-- If `W` respects isomorphisms and `Φ₁ ≅ Φ₂`, then `W (Φ₁.map f)` and `W (Φ₂.map f)` are
equivalent. -/
theorem natIso_map_iff (e : Φ₁ ≅ Φ₂) {A B : C} (f : A ⟶ B) :
    W (Φ₁.map f) ↔ W (Φ₂.map f) :=
  ⟨of_natIso_map e, of_natIso_map e.symm⟩

/-- A functor preserving a class of morphisms is a property of its isomorphism class. -/
theorem le_inverseImage_of_natIso (e : Φ₁ ≅ Φ₂) {W' : MorphismProperty C}
    (h : W' ≤ W.inverseImage Φ₁) : W' ≤ W.inverseImage Φ₂ := by
  intro A B f hf
  rw [MorphismProperty.inverseImage_iff]
  exact of_natIso_map e (h f hf)

end CategoryTheory.MorphismProperty

end
