module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Binary products and pullback squares

Two auxiliary facts about binary products used throughout the theory of descent data, where
the pairwise fibre product `X i ×_T X j` is modelled as a binary product in `Over T`.

## Main results

* `CategoryTheory.Limits.IsPullback.prod`: a product of two pullback squares is a pullback
  square.
* `CategoryTheory.Over.prod_left_ext`: two maps into the underlying object of a binary product
  in an over-category agree as soon as they agree after both projections.

## Implementation notes

`CategoryTheory.Over.prod_left_ext` is not an instance of `CategoryTheory.Limits.prod.hom_ext`:
its two maps go into the *underlying* object `(A ⨯ B).left`, which is a fibre product rather
than a product, so the extensionality used is that of
`CategoryTheory.Over.prodLeftIsoPullback`.

## References

* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
-/

@[expose] public section

universe v u

namespace CategoryTheory

open CategoryTheory.Limits

namespace Limits

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- The product of two pullback squares is a pullback square. -/
lemma IsPullback.prod {P₁ X₁ Y₁ S₁ P₂ X₂ Y₂ S₂ : C} {a₁ : P₁ ⟶ X₁} {b₁ : P₁ ⟶ Y₁}
    {f₁ : X₁ ⟶ S₁} {g₁ : Y₁ ⟶ S₁} {a₂ : P₂ ⟶ X₂} {b₂ : P₂ ⟶ Y₂} {f₂ : X₂ ⟶ S₂}
    {g₂ : Y₂ ⟶ S₂} (h₁ : IsPullback a₁ b₁ f₁ g₁) (h₂ : IsPullback a₂ b₂ f₂ g₂) :
    IsPullback (prod.map a₁ a₂) (prod.map b₁ b₂) (prod.map f₁ f₂) (prod.map g₁ g₂) := by
  have hw : prod.map a₁ a₂ ≫ prod.map f₁ f₂ = prod.map b₁ b₂ ≫ prod.map g₁ g₂ := by
    simp [h₁.w, h₂.w]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  refine PullbackCone.IsLimit.mk hw (fun s ↦ prod.lift
    (h₁.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.fst) (by
      simpa using s.condition =≫ prod.fst))
    (h₂.lift (s.fst ≫ prod.snd) (s.snd ≫ prod.snd) (by
      simpa using s.condition =≫ prod.snd))) ?_ ?_ ?_
  · intro s
    apply prod.hom_ext <;> simp
  · intro s
    apply prod.hom_ext <;> simp
  · intro s m hm₁ hm₂
    exact prod.hom_ext
      (h₁.hom_ext (by simpa using hm₁ =≫ prod.fst)
        (by simpa using hm₂ =≫ prod.fst))
      (h₂.hom_ext (by simpa using hm₁ =≫ prod.snd)
        (by simpa using hm₂ =≫ prod.snd))

end Limits

/-- Two maps into the underlying object of a binary product in an over-category agree as soon
as they agree after both projections. -/
lemma Over.prod_left_ext {C : Type u} [Category.{v} C] {R : C} (A B : Over R)
    [HasBinaryProduct A B] [HasPullback A.hom B.hom] {Z : C} {a b : Z ⟶ (A ⨯ B).left}
    (h₁ : a ≫ (prod.fst : A ⨯ B ⟶ A).left = b ≫ (prod.fst : A ⨯ B ⟶ A).left)
    (h₂ : a ≫ (prod.snd : A ⨯ B ⟶ B).left = b ≫ (prod.snd : A ⨯ B ⟶ B).left) : a = b := by
  apply (cancel_mono (Over.prodLeftIsoPullback A B).hom).mp
  apply pullback.hom_ext <;> simpa using (by assumption)

end CategoryTheory

end
