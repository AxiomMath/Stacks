module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.Deformation.Artin.LocallyNoetherianAlgebraicSpaceCriterion

/-!
# Relative representability along isomorphic functors

For a functor `F : C ⥤ D`, a morphism `f` of `D` is relatively representable along `F` when its
base change along every morphism out of an object `F.obj a` is of the form `F.obj b`, and it has
`P.relative F` when moreover each such represented base change has `P`.  Both notions only depend
on `F` up to isomorphism: an isomorphism `F ≅ F'` transports the pullback squares.

The typical application compares representability along `CategoryTheory.uliftYoneda.{0}` and
along `CategoryTheory.yoneda`, through `CategoryTheory.uliftYonedaIsoYoneda`.

## Main results

* `CategoryTheory.MorphismProperty.relative_iff_of_iso`: `P.relative F` transports along an
  isomorphism of functors, as relative representability does
  (`CategoryTheory.Functor.relativelyRepresentable_of_iso`).
* `CategoryTheory.MorphismProperty.presheaf_iff_relative_uliftYoneda`: for presheaves of types,
  `P.presheaf` is `P.relative uliftYoneda.{0}`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace MorphismProperty

/-- `P.relative F` only depends on the functor `F` up to isomorphism. -/
theorem relative_of_iso (P : MorphismProperty C) {F F' : C ⥤ D} (e : F ≅ F') {X Y : D}
    {f : X ⟶ Y} (hf : P.relative F f) : P.relative F' f := by
  refine ⟨Functor.relativelyRepresentable_of_iso e hf.1, fun a b g fst snd h => ?_⟩
  refine hf.2 (e.hom.app a ≫ g) (e.hom.app b ≫ fst) snd ?_
  exact h.of_iso (e.symm.app b) (Iso.refl _) (e.symm.app a) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- `P.relative F` and `P.relative F'` agree for isomorphic functors `F ≅ F'`. -/
theorem relative_iff_of_iso (P : MorphismProperty C) {F F' : C ⥤ D} (e : F ≅ F') {X Y : D}
    (f : X ⟶ Y) : P.relative F f ↔ P.relative F' f :=
  ⟨relative_of_iso P e, relative_of_iso P e.symm⟩

/-- For presheaves of types on a category, representability by morphisms with `P` along the
Yoneda embedding is representability along its universe lift by the trivial universe. -/
theorem presheaf_iff_relative_uliftYoneda {C : Type u₁} [Category.{v₁} C]
    (P : MorphismProperty C) {X Y : Cᵒᵖ ⥤ Type v₁} (f : X ⟶ Y) :
    P.presheaf f ↔ P.relative uliftYoneda.{0} f :=
  relative_iff_of_iso P uliftYonedaIsoYoneda.{0}.symm f

end MorphismProperty

end CategoryTheory

end
