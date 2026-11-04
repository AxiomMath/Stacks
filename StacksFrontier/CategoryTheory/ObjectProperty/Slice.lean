module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Slices of a full subcategory

Let `P` be a property of objects of a category `C` and let `X` be an object satisfying `P`.
Forming the slice at `X` commutes with passing to the full subcategory on `P`: an object of
the full subcategory over `X` is the same thing as an object of `C` over `X` whose source
satisfies `P`.

## Main definitions

* `CategoryTheory.ObjectProperty.overLeft` is the property of an object over `X` that its
  source satisfies `P`.
* `CategoryTheory.ObjectProperty.overLeftEquivalence` is the resulting equivalence between the
  full subcategory of `Over X.obj` on `overLeft` and the slice `Over X` of the full
  subcategory.

## Implementation notes

Both sides have the same underlying data — an object of `C` satisfying `P` together with a
morphism to `X` — so the two functors are the identity on that data and the unit and counit
are built from `Iso.refl`. The equivalence is nevertheless not a definitional equality,
because the two constructions bundle the proof of `P` at different places.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C]

/-- The property of an object over `X` that its source satisfies `P`. -/
abbrev overLeft (P : ObjectProperty C) (X : C) : ObjectProperty (Over X) := fun Z ↦ P Z.left

/-- The slice at `X` of the full subcategory on `P` is the full subcategory of `Over X.obj` on
the objects whose source satisfies `P`. -/
def overLeftEquivalence (P : ObjectProperty C) (X : P.FullSubcategory) :
    (P.overLeft X.obj).FullSubcategory ≌ Over X where
  functor :=
    { obj Z := Over.mk (P.homMk (X := ⟨Z.obj.left, Z.property⟩) (Y := X) Z.obj.hom)
      map {Z W} f := Over.homMk
        (U := Over.mk (P.homMk (X := ⟨Z.obj.left, Z.property⟩) Z.obj.hom))
        (V := Over.mk (P.homMk (X := ⟨W.obj.left, W.property⟩) W.obj.hom))
        (P.homMk f.hom.left) (P.hom_ext f.hom.w)
      map_id _ := Over.OverMorphism.ext rfl
      map_comp _ _ := Over.OverMorphism.ext rfl }
  inverse :=
    { obj Z := ⟨Over.mk (P.ι.map Z.hom), Z.left.property⟩
      map {Z W} f := (P.overLeft X.obj).homMk
        (Over.homMk (P.ι.map f.left) (by
          change P.ι.map f.left ≫ P.ι.map W.hom = P.ι.map Z.hom
          rw [← Functor.map_comp]
          exact congrArg P.ι.map f.w))
      map_id Z := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        simp
      map_comp f g := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        simp }
  unitIso := NatIso.ofComponents
    (fun Z ↦ (P.overLeft X.obj).isoMk (Over.isoMk (Iso.refl _) (by simp)))
    (by
      intro Z W f
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      simp)
  counitIso := NatIso.ofComponents
    (fun Z ↦ Over.isoMk (Iso.refl _) (by
      apply P.hom_ext
      simp))
    (by
      intro Z W f
      apply Over.OverMorphism.ext
      apply P.hom_ext
      simp)
  functor_unitIso_comp Z := by
    apply Over.OverMorphism.ext
    apply P.hom_ext
    simp

end CategoryTheory.ObjectProperty

end
