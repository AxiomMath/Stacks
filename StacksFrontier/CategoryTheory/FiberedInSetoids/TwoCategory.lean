module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs

/-!
# The 2-category of categories fibred in setoids

Let `𝒞` be a category. The *2-category of categories fibred in setoids over `𝒞`* has as objects
the categories over `𝒞` whose structure functor is fibred in setoids, as 1-morphisms the functors
`G` over `𝒞`, i.e. those with `p' ∘ G = p`, and as 2-morphisms the morphisms of functors `t` with
`p'(t_x) = 𝟙 (p x)` for every object `x`.

## Main definitions

* `CategoryTheory.CatFiberedInSetoids`: the 2-category of categories fibred in setoids over `𝒞`;
* `CategoryTheory.CatFiberedInSetoids.inclusion`: its inclusion into the 2-category of categories
  fibred in groupoids over `𝒞`;
* `CategoryTheory.CatFiberedInSetoids.inclusionTwoHomEquiv`: the inclusion is bijective on
  2-morphisms.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

set_option linter.checkUnivs false in
/-- The 2-category of categories fibred in setoids over `𝒞`: the full sub-2-category of the
2-category `BasedCategory 𝒞` of categories over `𝒞` spanned by the categories fibred in setoids.
Explicitly:

1. its objects are the categories `p : 𝒮 ⥤ 𝒞` over `𝒞` that are fibred in setoids;
2. its 1-morphisms `(𝒮, p) ⟶ (𝒮', p')` are the functors `G : 𝒮 ⥤ 𝒮'` with `p' ∘ G = p`;
3. its 2-morphisms `t : G ⟶ H` are the morphisms of functors with `p'(t_x) = 𝟙 (p x)` for every
   object `x` of `𝒮`. -/
@[stacks 02Y1]
abbrev CatFiberedInSetoids (𝒞 : Type u₁) [Category.{v₁} 𝒞] :=
  Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} 𝒞)
    (Subtype.val (p := fun 𝒳 : BasedCategory.{v₂, u₂} 𝒞 ↦ 𝒳.p.IsFiberedInSetoids))

namespace CatFiberedInSetoids

open CatFiberedInGroupoids
  (homEquivBasedFunctor homFunctor homFunctor_comp_p homEquivBasedNatTrans map_app)

/-- A category over `𝒞` whose structure functor is fibred in setoids, viewed as an object of the
2-category of categories fibred in setoids over `𝒞`. -/
abbrev mk (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (h : 𝒳.p.IsFiberedInSetoids) :
    CatFiberedInSetoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  ⟨𝒳, h⟩

/-- The structure functor of an object of the 2-category of categories fibred in setoids over `𝒞`
is fibred in setoids. -/
instance isFiberedInSetoids (𝒳 : CatFiberedInSetoids.{v₁, v₂, u₁, u₂} 𝒞) :
    𝒳.val.p.IsFiberedInSetoids :=
  𝒳.2


/-- A category fibred in setoids, as an object of the 2-category of categories fibred in
groupoids over `𝒞`. -/
abbrev toCatFiberedInGroupoids (𝒳 : CatFiberedInSetoids.{v₁, v₂, u₁, u₂} 𝒞) :
    CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  CatFiberedInGroupoids.mk 𝒳.val 𝒳.isFiberedInSetoids.isFiberedInGroupoids

/-- The inclusion of the 2-category of categories fibred in setoids over `𝒞` into the
2-category of categories fibred in groupoids over `𝒞`, as a functor on the underlying
1-categories of the two strict bicategories. It sends an object to
`CatFiberedInSetoids.toCatFiberedInGroupoids` of it. -/
@[simps!]
def inclusion : CatFiberedInSetoids.{v₁, v₂, u₁, u₂} 𝒞 ⥤
    CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  CatFiberedInGroupoids.inclusion fun _ h ↦ h.isFiberedInGroupoids

/-- The inclusion of the 2-category of categories fibred in setoids into the 2-category of
categories fibred in groupoids is bijective on 2-morphisms. -/
def inclusionTwoHomEquiv {𝒳 𝒴 : CatFiberedInSetoids.{v₁, v₂, u₁, u₂} 𝒞} (G H : 𝒳 ⟶ 𝒴) :
    (G ⟶ H) ≃ (inclusion.map G ⟶ inclusion.map H) where
  toFun t := Bicategory.InducedBicategory.Hom₂.mk t.hom
  invFun t := Bicategory.InducedBicategory.Hom₂.mk t.hom
  left_inv _ := rfl
  right_inv _ := rfl

end CatFiberedInSetoids

end CategoryTheory
