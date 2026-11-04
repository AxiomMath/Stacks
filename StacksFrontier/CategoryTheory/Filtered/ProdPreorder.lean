module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Order.Directed

/-!
# The product of two index preorders

A product of two preorders is a preorder, and it is directed and nonempty as soon as both
factors are. As an *index category* for a two-variable colimit it is not the product of the two
preorder categories, however: the product category `I₁ × I₂` has a pair of inequalities as a
morphism, whereas the product preorder has a single inequality of pairs. The two categories are
thin with the same hom-sets nonempty, so the comparison between them is an equivalence. This
file defines the type synonym carrying the product *preorder* and that equivalence.

## Main definitions

* `CategoryTheory.ProdPreorder`: the product of two types, as a type synonym carrying the product
  preorder.
* `CategoryTheory.prodPreorderEquivalence`: its preorder category is equivalent to the product
  of the two preorder categories.
-/

@[expose] public section

universe w₁ w₂

namespace CategoryTheory

/-- The product `I₁ × I₂` of two types, as a type synonym carrying the product preorder; its
category structure is that of this preorder, not the product of the two preorder categories. -/
def ProdPreorder (I₁ : Type w₁) (I₂ : Type w₂) : Type max w₁ w₂ := I₁ × I₂

variable (I₁ : Type w₁) (I₂ : Type w₂) [Preorder I₁] [Preorder I₂]

/-- The product preorder on `ProdPreorder I₁ I₂`: `p ≤ q` if and only if `p.1 ≤ q.1` and
`p.2 ≤ q.2`. -/
instance : Preorder (ProdPreorder I₁ I₂) := inferInstanceAs (Preorder (I₁ × I₂))

/-- The product of two nonempty preorders is nonempty. -/
instance [Nonempty I₁] [Nonempty I₂] : Nonempty (ProdPreorder I₁ I₂) :=
  inferInstanceAs (Nonempty (I₁ × I₂))

/-- **A product of two directed preorders is directed.** -/
instance [IsDirected I₁ (· ≤ ·)] [IsDirected I₂ (· ≤ ·)] :
    IsDirected (ProdPreorder I₁ I₂) (· ≤ ·) where
  directed p q := by
    obtain ⟨c, hpc, hqc⟩ := directed_of (· ≤ ·)
      (show I₁ × I₂ from p).1 (show I₁ × I₂ from q).1
    obtain ⟨d, hpd, hqd⟩ := directed_of (· ≤ ·)
      (show I₁ × I₂ from p).2 (show I₁ × I₂ from q).2
    exact ⟨((c, d) : I₁ × I₂), ⟨hpc, hpd⟩, ⟨hqc, hqd⟩⟩

/-- **The preorder category of a product of preorders is equivalent to the product of the two
preorder categories**: the identity on objects, and on morphisms the splitting of an inequality
of pairs into a pair of inequalities. -/
def prodPreorderEquivalence : ProdPreorder I₁ I₂ ≌ I₁ × I₂ where
  functor :=
    { obj := fun p ↦ p
      map := fun f ↦ (homOfLE (leOfHom f).1, homOfLE (leOfHom f).2)
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  inverse :=
    { obj := fun p ↦ p
      map := fun f ↦ homOfLE ⟨leOfHom f.1, leOfHom f.2⟩
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  functor_unitIso_comp := fun _ ↦ rfl

/-- The functor of `CategoryTheory.prodPreorderEquivalence` is the identity on objects. -/
@[simp]
theorem prodPreorderEquivalence_functor_obj (p : ProdPreorder I₁ I₂) :
    (prodPreorderEquivalence I₁ I₂).functor.obj p = p := rfl

end CategoryTheory

end
