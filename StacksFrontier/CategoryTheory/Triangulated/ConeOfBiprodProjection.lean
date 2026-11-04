module

public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# The cone of the projection of a biproduct onto one summand

Let `C` be a triangulated category and `X`, `Y` two objects.  The endomorphism

`diag(1, 0) = biprod.map (𝟙 X) 0 : X ⊞ Y ⟶ X ⊞ Y`

has cone `Y ⊞ Y⟦1⟧`: the summand `X` is killed, because the cone of an identity vanishes, and
the summand `Y` is doubled, because the cone of a zero endomorphism of `Y` is `Y ⊞ Y⟦1⟧`.

The statement below takes an arbitrary distinguished triangle whose first morphism is
`diag(1, 0)` up to isomorphisms of its first two objects, which is the form in which the
computation is used: in [Stacks, Tag 08EI] the triangle comes out of a lifting lemma and its
first morphism is only identified with `diag(1, 0)` after transport along an isomorphism
`𝓕[r] ⊕ F ≅ E|_U`.  The triangle is given by its three morphisms rather than as a
`CategoryTheory.Pretriangulated.Triangle`, so that a consumer who has the morphisms need not
meet the projections of a triangle built from them.

## Main results

* `Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang`: the third object of a
  distinguished triangle whose first morphism is `diag(1, 0) : X ⊞ Y ⟶ X ⊞ Y` is `Y ⊞ Y⟦1⟧`.
* `Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang_of_conj`: the same, with the
  hypothesis in the shape a lifting lemma produces -- a morphism that becomes `diag(1, 0)` after
  composing with an invertible morphism and conjugating by an identification of the biproduct.

## Implementation notes

The proof factors `diag(1, 0)` as `biprod.fst ≫ biprod.inl` and runs the octahedron axiom on
that factorization.  The cone of `biprod.inl : X ⟶ X ⊞ Y` is `Y`, by the biproduct triangle; the
cone of `biprod.fst : X ⊞ Y ⟶ X` is `Y⟦1⟧`, by the rotation of the biproduct triangle of
`Y ⊞ X` carried across the braiding.  The octahedron triangle therefore reads
`Y⟦1⟧ ⟶ cone(diag(1,0)) ⟶ Y ⟶ Y⟦1⟧⟦1⟧`, and its third morphism is zero because it factors
through the third morphism of the biproduct triangle, which is zero; so the triangle splits and
its middle object is `Y⟦1⟧ ⊞ Y`.

Only the octahedron axiom and the splitting criterion
`CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` are used; the cone is
not computed on a representing complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- `diag(1, 0)` on a biproduct is the projection onto the first summand followed by its
inclusion. -/
theorem biprod_map_id_zero_eq_fst_comp_inl (X Y : C) :
    biprod.map (𝟙 X) (0 : Y ⟶ Y) = (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

/-- The biproduct triangle `X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧`, with its three morphisms written out. -/
theorem distTriang_biprod_inl (X Y : C) :
    Triangle.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y)
      (0 : Y ⟶ X⟦(1 : ℤ)⟧) ∈ distTriang C :=
  binaryBiproductTriangle_distinguished X Y

/-- **The cone of `biprod.fst : X ⊞ Y ⟶ X` is `Y⟦1⟧`.** This is the rotation of the biproduct
triangle `Y ⟶ Y ⊞ X ⟶ X ⟶ Y⟦1⟧`, carried along the braiding `X ⊞ Y ≅ Y ⊞ X`. Its second
morphism is zero, which is what makes the octahedron on `biprod.fst ≫ biprod.inl` split. -/
theorem distTriang_biprod_fst (X Y : C) :
    Triangle.mk (biprod.fst : X ⊞ Y ⟶ X) (0 : X ⟶ Y⟦(1 : ℤ)⟧)
      (-(biprod.inr : Y ⟶ X ⊞ Y)⟦(1 : ℤ)⟧') ∈ distTriang C := by
  have h : (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.braiding X Y).hom =
      (biprod.inl : Y ⟶ Y ⊞ X) := by
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  have hT : Triangle.mk (biprod.snd : Y ⊞ X ⟶ X) (0 : X ⟶ Y⟦(1 : ℤ)⟧)
      (-(biprod.inl : Y ⟶ Y ⊞ X)⟦(1 : ℤ)⟧') ∈ distTriang C :=
    rot_of_distTriang _ (binaryBiproductTriangle_distinguished Y X)
  refine isomorphic_distinguished _ hT _ ?_
  refine Triangle.isoMk _ _ (biprod.braiding X Y) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change (biprod.fst : X ⊞ Y ⟶ X) ≫ 𝟙 X = (biprod.braiding X Y).hom ≫ biprod.snd
    rw [Category.comp_id, biprod.braiding_hom, biprod.lift_snd]
  · change (0 : X ⟶ Y⟦(1 : ℤ)⟧) ≫ 𝟙 (Y⟦(1 : ℤ)⟧) = 𝟙 X ≫ (0 : X ⟶ Y⟦(1 : ℤ)⟧)
    rw [Category.comp_id, Category.id_comp]
  · change (-(biprod.inr : Y ⟶ X ⊞ Y)⟦(1 : ℤ)⟧') ≫ ((biprod.braiding X Y).hom)⟦(1 : ℤ)⟧' =
      𝟙 (Y⟦(1 : ℤ)⟧) ≫ (-(biprod.inl : Y ⟶ Y ⊞ X)⟦(1 : ℤ)⟧')
    rw [Category.id_comp, Preadditive.neg_comp, ← Functor.map_comp, h]

variable [IsTriangulated C]

/-- **The cone of `diag(1, 0) : X ⊞ Y ⟶ X ⊞ Y` is `Y ⊞ Y⟦1⟧`.** Let `T` be a distinguished
triangle `A ⟶ B ⟶ Z ⟶ A⟦1⟧` whose first two objects are identified with `X ⊞ Y` by isomorphisms
carrying its first morphism to `diag(1, 0)`, written as `biprod.fst ≫ biprod.inl` -- the two are
equal by `Stacks.Triangulated.biprod_map_id_zero_eq_fst_comp_inl`, and that form of the
hypothesis spares a consumer the search for the zero morphism. Then `Z` is isomorphic to
`Y ⊞ Y⟦1⟧`.

The factorization `diag(1, 0) = biprod.fst ≫ biprod.inl` and the octahedron axiom produce a
distinguished triangle `Y⟦1⟧ ⟶ Z ⟶ Y ⟶ Y⟦1⟧⟦1⟧` whose third morphism vanishes, because the
third morphism of the biproduct triangle of `X ⊞ Y` does. -/
theorem exists_iso_biprod_shift_of_distTriang (X Y : C) {A B Z : C} (f : A ⟶ B) (g : B ⟶ Z)
    (h : Z ⟶ A⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang C)
    (e₁ : A ≅ X ⊞ Y) (e₂ : B ≅ X ⊞ Y)
    (hcomm : f ≫ e₂.hom =
      e₁.hom ≫ (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y)) :
    Nonempty (Z ≅ Y ⊞ Y⟦(1 : ℤ)⟧) := by
  obtain ⟨Z₀, v, w, h₁₃⟩ :=
    distinguished_cocone_triangle ((biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y))
  have oct := someOctahedron (rfl :
      (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) = _)
    (distTriang_biprod_fst X Y) (distTriang_biprod_inl X Y) h₁₃
  have hzero : (0 : Y ⟶ X⟦(1 : ℤ)⟧) ≫ (0 : X ⟶ Y⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧' = 0 := zero_comp
  obtain ⟨eZ, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ oct.mem hzero
  refine ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ (Triangle.mk f g h) _ hT h₁₃ e₁ e₂ ?_) ≪≫ eZ ≪≫
    biprod.braiding (Y⟦(1 : ℤ)⟧) Y⟩
  exact hcomm

/-- **The cone computation with the hypothesis in the form a lifting lemma produces it.**  Let
`ε : X ⊞ Y ≅ B` be an identification, `b : A ⟶ B` an isomorphism and `c : A ⟶ B` a morphism with
`b ≫ (ε.inv ≫ diag(1, 0) ≫ ε.hom) = c`, where `diag(1, 0)` is `biprod.fst ≫ biprod.inl`.  Then
the third object of a distinguished triangle on `c` is `Y ⊞ Y⟦1⟧`.

This is `Stacks.Triangulated.exists_iso_biprod_shift_of_distTriang` with the two isomorphisms
`ε.symm` and `asIso b ≪≫ ε.symm`; the hypothesis is the shape in which [Stacks, Tag 08EH] hands
over its conclusion. -/
theorem exists_iso_biprod_shift_of_distTriang_of_conj (X Y : C) {A B Z : C} (ε : X ⊞ Y ≅ B)
    (b c : A ⟶ B) (hb : IsIso b) (g : B ⟶ Z) (h : Z ⟶ A⟦(1 : ℤ)⟧)
    (hT : Triangle.mk c g h ∈ distTriang C)
    (hbc : b ≫ (ε.inv ≫ ((biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y)) ≫ ε.hom) = c) :
    Nonempty (Z ≅ Y ⊞ Y⟦(1 : ℤ)⟧) :=
  exists_iso_biprod_shift_of_distTriang X Y c g h hT (@asIso _ _ _ _ b hb ≪≫ ε.symm) ε.symm
    (by rw [← hbc]; simp)

end Stacks.Triangulated

end
