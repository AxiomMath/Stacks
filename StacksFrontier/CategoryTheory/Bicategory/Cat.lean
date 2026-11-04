module

public import StacksFrontier.CategoryTheory.Bicategory.TwoOneCategory

/-!
# `Cat` as a `(2,1)`-category

Stacks 003K: the `2`-category `Cat` of categories (Stacks 003J) can be turned into a
`(2,1)`-category by keeping only the *isomorphisms* of functors as `2`-morphisms.

Mathlib already performs that discarding in general: for a bicategory `B`,
`CategoryTheory.Bicategory.Pith B` is `B` with its non-invertible `2`-morphisms thrown away,
and it is locally groupoidal by construction. What is missing for Stacks 003K is that the
operation keeps a `2`-category a `2`-category, i.e. preserves strictness — a `1`-morphism of
`Pith B` is a `1`-morphism of `B` in a one-field wrapper, so this is inherited — and that is
supplied here.

## Main results

* `CategoryTheory.Bicategory.Pith.instStrict`: the pith of a strict bicategory is strict.
* `CategoryTheory.Bicategory.isTwoOneCategory_pith`: the pith of a `2`-category is a
  `(2,1)`-category (Stacks 003I).
* `CategoryTheory.Bicategory.isTwoOneCategory_pith_cat`: **Stacks 003K**, the case `B = Cat`.
* `CategoryTheory.Bicategory.Pith.homEquivIso`: the `2`-morphisms of `Pith Cat` are exactly the
  isomorphisms of functors, which is the content of the source's "by only allowing isomorphisms
  of functors as `2`-morphisms".
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Bicategory

open CategoryTheory

variable (B : Type u) [Bicategory.{w, v} B]

namespace Pith

/-- Transporting a `2`-morphism of `Pith B` along an equality of `1`-morphisms is transport along
the corresponding equality of `1`-morphisms of `B`. -/
@[simp]
lemma eqToHom_iso_hom {a b : Pith B} {x y : a ⟶ b} (h : x = y) :
    (eqToHom h).iso.hom = eqToHom (congrArg Core.of h) := by
  subst h; simp

variable [Bicategory.Strict B]

/-- The pith of a strict bicategory is strict: a `1`-morphism of `Pith B` is a `1`-morphism of
`B` in a one-field wrapper and composition is computed on the wrapped morphism, so the three
equations of `Bicategory.Strict` are inherited; the unitors and associator of `Pith B` are the
images of those of `B`, hence are `eqToIso`s as well. -/
instance instStrict : Bicategory.Strict (Pith B) where
  id_comp f := congrArg Core.mk (Bicategory.Strict.id_comp f.of)
  comp_id f := congrArg Core.mk (Bicategory.Strict.comp_id f.of)
  assoc f g h := congrArg Core.mk (Bicategory.Strict.assoc f.of g.of h.of)
  leftUnitor_eqToIso f := by ext; simp [Bicategory.Strict.leftUnitor_eqToIso]
  rightUnitor_eqToIso f := by ext; simp [Bicategory.Strict.rightUnitor_eqToIso]
  associator_eqToIso f g h := by ext; simp [Bicategory.Strict.associator_eqToIso]

end Pith

/-- Discarding the non-invertible `2`-morphisms of a `2`-category leaves a `(2,1)`-category
(Stacks 003I): strictness is `Pith.instStrict` and local groupoidality is
`Pith.homGroupoid`. -/
lemma isTwoOneCategory_pith [Bicategory.Strict B] : IsTwoOneCategory (Pith B) :=
  ⟨inferInstance, inferInstance⟩

/-- **Stacks 003K.** The `2`-category `Cat` of categories, functors and morphisms of functors
(Stacks 003J) becomes a `(2,1)`-category once only the *isomorphisms* of functors are allowed as
`2`-morphisms. The resulting `2`-category is `Bicategory.Pith Cat`; that its `2`-morphisms are
precisely the isomorphisms of functors is `Pith.homEquivIso`. -/
@[stacks 003K]
lemma isTwoOneCategory_pith_cat : IsTwoOneCategory (Pith Cat.{v, u}) :=
  isTwoOneCategory_pith _

namespace Pith

/-- The `2`-morphisms of `Pith B` between two `1`-morphisms are exactly the isomorphisms, in
`B`, of the underlying `1`-morphisms. Specialized to `B = Cat` this is the source's description
of Stacks 003K: the `2`-morphisms are the isomorphisms of functors. -/
def homEquivIso {a b : Pith B} (f g : a ⟶ b) : (f ⟶ g) ≃ (f.of ≅ g.of) where
  toFun η := η.iso
  invFun e := ⟨e⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Pith

end CategoryTheory.Bicategory
