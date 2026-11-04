module

public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Setoid
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dotted arrows for a faithful 1-morphism

Fix a base category `C` and a 2-commutative square in the 2-category of categories fibred in
groupoids over `C`, filled by a 2-morphism `γ`. Its category of dotted arrows
`CategoryTheory.DottedArrow` is a groupoid, because that 2-category is locally groupoidal. When
the right-hand edge `f` is *faithful* on underlying functors, the category of dotted arrows is
moreover **thin**, hence a setoid.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.isIso_toNatTrans`: every 2-morphism of categories fibred
  in groupoids is invertible on underlying natural transformations.
* `CategoryTheory.DottedArrow.hom_ext_of_faithful`: the category of dotted arrows for a faithful
  1-morphism is thin.
* `CategoryTheory.isSetoidCategory_dottedArrow_of_faithful`: the category of dotted arrows for
  a faithful 1-morphism is a setoid.
* `CategoryTheory.DottedArrow.pasting_eq`: the two pastings prescribed by two dotted
  arrows of the same square agree.

## References

* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
* [Stacks Project, Tag 02XZ](https://stacks.math.columbia.edu/tag/02XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

namespace CatFiberedInGroupoids

/-- **A 2-morphism of categories fibred in groupoids is invertible on underlying natural
transformations.** -/
@[sga "4 XVIII 1.4.6" "more general"]
theorem isIso_toNatTrans {A D : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C} {f g : A ⟶ D}
    (η : f ⟶ g) : IsIso (X := f.hom.toFunctor) η.hom.toNatTrans :=
  have : IsIso η := (homGroupoid A D).all_isIso η
  (underlyingIso (asIso η)).isIso_hom

end CatFiberedInGroupoids

variable {S T X Y : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C}
  {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y} {γ : (j ≫ y) ⟶ (x ≫ f)}

namespace DottedArrow

/-- **The category of dotted arrows for a faithful 1-morphism is thin.** Any two morphisms
between the same two dotted arrows are equal. -/
theorem hom_ext_of_faithful [f.hom.toFunctor.Faithful] {a b : DottedArrow x j f y γ}
    (η μ : a ⟶ b) : η = μ := by
  refine DottedArrow.Hom.ext ?_
  have hβ : IsIso a.β := (CatFiberedInGroupoids.homGroupoid T Y).all_isIso a.β
  have h : η.θ ▷ f = μ.θ ▷ f :=
    (cancel_epi a.β).mp (η.cond_β.symm.trans μ.cond_β)
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext z
  exact f.hom.toFunctor.map_injective (congrArg (fun t => t.hom.toNatTrans.app z) h)

/-- **The two pastings prescribed by two dotted arrows of the same square agree.** -/
theorem pasting_eq (a b : DottedArrow x j f y γ) :
    (j ◁ a.β) ≫ (α_ j a.a f).inv ≫ (a.α ▷ f) =
      (j ◁ b.β) ≫ (α_ j b.a f).inv ≫ (b.α ▷ f) :=
  a.compat.symm.trans b.compat

end DottedArrow

/-- The category of dotted arrows along a faithful 1-morphism is a setoid: every morphism is an
isomorphism and every endomorphism is the identity. -/
theorem isSetoidCategory_dottedArrow_of_faithful [f.hom.toFunctor.Faithful] :
    IsSetoidCategory (DottedArrow x j f y γ) :=
  ⟨fun _ => inferInstance, fun a η => DottedArrow.hom_ext_of_faithful η (𝟙 a)⟩

end CategoryTheory

end
