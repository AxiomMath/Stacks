module

public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

/-!
# Rebasing a slice of a slice along a relocalization

Let `𝒞` be a category, `U` an object of a slice `𝒞/S` and `A` an object of the slice `𝒞/U.left`.
Relocalizing `A` gives an object `A/S` of `𝒞/S`, and the two slices `(𝒞/S)/(A/S)` and
`(𝒞/U.left)/A` are then the same category: both are the slice of `𝒞` at the underlying object of
`A`, by `CategoryTheory.Over.iteratedSliceEquiv` applied twice. The comparison functor
`(𝒞/S)/(A/S) ⥤ (𝒞/U.left)/A` is a 1-morphism over `𝒞/S` and is natural in `A`.

## Main definitions

* `CategoryTheory.Over.sliceRebase`: the comparison functor `(𝒞/S)/(A/S) ⥤ (𝒞/U.left)/A`.

## Main results

* `CategoryTheory.Over.obj_ext`: an object of a slice is determined by its underlying object and
  its structure morphism.
* `CategoryTheory.Over.sliceRebase_comp_forget_map`: the comparison is a 1-morphism over `𝒞/S`.
* `CategoryTheory.Over.sliceRebase_map`: the comparison is natural in `A`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Over

universe v u

variable {C : Type u} [Category.{v} C]

/-- An object of a slice is determined by its underlying object and its structure morphism, the
two structure morphisms being compared through the identification of the underlying objects. -/
theorem obj_ext {X : C} {A B : Over X} (h : A.left = B.left)
    (hh : A.hom = eqToHom h ≫ B.hom) : A = B := by
  rcases A with ⟨a, ⟨⟨⟩⟩, f⟩
  rcases B with ⟨b, ⟨⟨⟩⟩, g⟩
  obtain rfl : a = b := h
  obtain rfl : f = g := by simpa using hh
  rfl

variable {S : C} (U : Over S)

/-- For `A` an object of `𝒞/U.left`, the comparison functor from the slice of `𝒞/S` at the
relocalization of `A` to the slice of `𝒞/U.left` at `A`, both being the slice of `𝒞` at the
underlying object of `A`. -/
def sliceRebase (A : Over U.left) : Over ((Over.map U.hom).obj A) ⥤ Over A :=
  Over.iteratedSliceForward ((Over.map U.hom).obj A) ⋙ Over.iteratedSliceBackward A

/-- The functor `sliceRebase U A` is a 1-morphism over `𝒞/S`: reading an object of the slice of
`𝒞/S` at the relocalization of `A` as an object of `𝒞/U.left` over `A` and relocalizing again
recovers it. -/
theorem sliceRebase_comp_forget_map (A : Over U.left) :
    sliceRebase U A ⋙ Over.forget A ⋙ Over.map U.hom =
      Over.forget ((Over.map U.hom).obj A) := by
  have hobj : ∀ V : Over ((Over.map U.hom).obj A),
      (sliceRebase U A ⋙ Over.forget A ⋙ Over.map U.hom).obj V =
        (Over.forget ((Over.map U.hom).obj A)).obj V := fun V =>
    obj_ext rfl (((Category.assoc _ _ _).trans (Over.w V.hom)).trans (Category.id_comp _).symm)
  refine CategoryTheory.Functor.ext hobj (fun V W i => ?_)
  refine PresheafOfCategories.over_hom_eq_conj (hobj V) (hobj W) rfl rfl _ _ ?_
  show _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The functor `sliceRebase U A` is natural in `A`: relocalizing a morphism `i : G ⟶ A` of
`𝒞/U.left` and rebasing along it is rebasing and then relocalizing along `i`. -/
theorem sliceRebase_map {A G : Over U.left} (i : G ⟶ A) :
    Over.map ((Over.map U.hom).map i) ⋙ sliceRebase U A =
      sliceRebase U G ⋙ Over.map i := by
  have hleft : ∀ V : Over ((Over.map U.hom).obj G),
      ((Over.map ((Over.map U.hom).map i) ⋙ sliceRebase U A).obj V).left =
        ((sliceRebase U G ⋙ Over.map i).obj V).left := fun V => by
    refine obj_ext rfl ?_
    show (V.hom.left ≫ i.left) ≫ A.hom = 𝟙 _ ≫ V.hom.left ≫ G.hom
    simp only [Category.id_comp, Category.assoc, Over.w i]
  have hobj : ∀ V : Over ((Over.map U.hom).obj G),
      (Over.map ((Over.map U.hom).map i) ⋙ sliceRebase U A).obj V =
        (sliceRebase U G ⋙ Over.map i).obj V := fun V => by
    have hid : (eqToHom (hleft V)).left = 𝟙 _ :=
      (Over.eqToHom_left (hleft V)).trans (eqToHom_refl _ _)
    refine obj_ext (hleft V) ?_
    refine Over.OverMorphism.ext ?_
    rw [Over.comp_left, hid]
    exact (Category.id_comp _).symm
  refine CategoryTheory.Functor.ext hobj (fun V W j => ?_)
  refine PresheafOfCategories.over_hom_eq_conj (hobj V) (hobj W) (hleft V) (hleft W) _ _ ?_
  refine PresheafOfCategories.over_hom_eq_conj (hleft V) (hleft W) rfl rfl _ _ ?_
  show _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end CategoryTheory.Over

end
