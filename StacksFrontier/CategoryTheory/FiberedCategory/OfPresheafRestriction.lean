module

public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf

/-!
# The fibred category of a restricted presheaf of categories

Let `i : 𝒞 ⥤ 𝒟` be a functor and let `F : 𝒟ᵒᵖ ⥤ Cat` be a presheaf of categories. The fibred
category of the restriction `i^op ⋙ F` over `𝒞` maps to the fibred category of `F` over `𝒟`,
by `(T, x) ↦ (i T, x)` on objects and `(g, φ) ↦ (i g, φ)` on morphisms: an object of the fibre
of `i^op ⋙ F` over `T` is by definition an object of `F(i T)`, and likewise for morphisms.

The functor covers `i`, so it is the comparison exhibiting the fibred category of `F` restricted
to the image of `i` as the fibred category of `i^op ⋙ F`.

## Main definitions

* `CategoryTheory.PresheafOfCategories.restrictionComparison`: the functor
  `𝒮_{i^op ⋙ F} ⥤ 𝒮_F`.

## Main results

* `CategoryTheory.PresheafOfCategories.restrictionComparison_comp_forget`: the functor covers
  `i`, that is, its composite with the projection of `𝒮_F` is the projection of
  `𝒮_{i^op ⋙ F}` followed by `i`.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃

open Opposite Pseudofunctor
open scoped Pseudofunctor.CoGrothendieck

namespace PresheafOfCategories

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  (i : 𝒞 ⥤ 𝒟) (F : 𝒟ᵒᵖ ⥤ Cat.{v₂, u₂})

/-- **The fibred category of a restricted presheaf of categories maps to that of the presheaf.**
On objects it is `(T, x) ↦ (i T, x)` and on morphisms `(g, φ) ↦ (i g, φ)`, both well typed
because the fibre of `i^op ⋙ F` over `T` is the fibre of `F` over `i T`. -/
def restrictionComparison :
    ∫ᶜ (i.op ⋙ F).toPseudofunctor' ⥤ ∫ᶜ F.toPseudofunctor' where
  obj X := ⟨i.obj X.base, X.fiber⟩
  map f := ⟨i.map f.base, f.fiber⟩
  map_id X := by
    refine CoGrothendieck.Hom.ext _ _ ?_ ?_
    · exact i.map_id X.base
    · cat_disch
  map_comp f g := by
    refine CoGrothendieck.Hom.ext _ _ ?_ ?_
    · exact i.map_comp _ _
    · cat_disch

/-- The comparison covers the restricting functor. -/
theorem restrictionComparison_comp_forget :
    restrictionComparison i F ⋙ CoGrothendieck.forget F.toPseudofunctor' =
      CoGrothendieck.forget (i.op ⋙ F).toPseudofunctor' ⋙ i := rfl

end PresheafOfCategories

end CategoryTheory

end
