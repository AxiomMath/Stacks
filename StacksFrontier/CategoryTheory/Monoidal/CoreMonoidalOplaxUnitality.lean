module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The unitality clauses of a tensorator, inverted

`CategoryTheory.Functor.CoreMonoidal` states its two unitality clauses on the `hom` of the
unitors and of the tensorator; `CategoryTheory.Functor.CoreMonoidal.mk'`, the constructor whose
associativity clause is the one a comparison of bifunctors naturally proves, states them on the
`inv`.  Each clause asserts that an isomorphism is a composite of three isomorphisms, so the two
forms carry the same content, and this file is that passage.

It is pure bookkeeping and the proofs are `Iso.ext` followed by `congrArg Iso.inv`: the inverse
of `a ≪≫ b ≪≫ c` is `c.inv ≫ b.inv ≫ a.inv` by definition, with one reassociation.

## Main results

* `Stacks.CategoryTheory.Monoidal.oplax_left_unitality_of_hom` and
  `Stacks.CategoryTheory.Monoidal.oplax_right_unitality_of_hom`: the `left_unitality` and
  `right_unitality` clauses of `CategoryTheory.Functor.CoreMonoidal` give the
  `oplax_left_unitality` and `oplax_right_unitality` arguments of
  `CategoryTheory.Functor.CoreMonoidal.mk'`.

## Implementation notes

The statements name no monoidal functor structure, only a unit comparison `εIso` and a
tensorator `μIso` as bare isomorphisms, so they apply before any such structure exists — which
is the point, since they are two of the arguments that build one.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Stacks.CategoryTheory.Monoidal

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
  (μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))

/-- The inverse of an isomorphism that is a composite of three isomorphisms. -/
private theorem inv_eq_of_hom_eq_comp_comp {E : Type u₂} [Category.{v₂} E] {A B C' G : E}
    (f : A ≅ G) (a : A ≅ B) (b : B ≅ C') (c : C' ≅ G) (h : f.hom = a.hom ≫ b.hom ≫ c.hom) :
    f.inv = c.inv ≫ b.inv ≫ a.inv :=
  (congrArg Iso.inv (Iso.ext h : f = a ≪≫ b ≪≫ c)).trans (Category.assoc _ _ _)

/-- **The left-unitality clause of `CategoryTheory.Functor.CoreMonoidal`, inverted**: this is
the `oplax_left_unitality` argument of `CategoryTheory.Functor.CoreMonoidal.mk'`. -/
theorem oplax_left_unitality_of_hom {X : C}
    (h : (λ_ (F.obj X)).hom =
      εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom) :
    (λ_ (F.obj X)).inv =
      F.map (λ_ X).inv ≫ (μIso (𝟙_ C) X).inv ≫ εIso.inv ▷ F.obj X :=
  inv_eq_of_hom_eq_comp_comp _ (whiskerRightIso εIso _) _ (F.mapIso _) h

/-- **The right-unitality clause of `CategoryTheory.Functor.CoreMonoidal`, inverted**: this is
the `oplax_right_unitality` argument of `CategoryTheory.Functor.CoreMonoidal.mk'`. -/
theorem oplax_right_unitality_of_hom {X : C}
    (h : (ρ_ (F.obj X)).hom =
      F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom) :
    (ρ_ (F.obj X)).inv =
      F.map (ρ_ X).inv ≫ (μIso X (𝟙_ C)).inv ≫ F.obj X ◁ εIso.inv :=
  inv_eq_of_hom_eq_comp_comp _ (whiskerLeftIso _ εIso) _ (F.mapIso _) h

end Stacks.CategoryTheory.Monoidal

end
