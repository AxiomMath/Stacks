module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorMate

/-!
# Congruences across a change of spelling, for the squares of the mate

The squares of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux` are instances of general
lemmas whose categories, functors, objects and morphisms are spelled differently from the instance.
The congruences of this file transport such an equation one factor at a time: components of natural
transformations, images of morphisms, composites and underlying morphisms of isomorphisms agree as
soon as their pieces agree, each piece being compared on its own.

## Main results

* `CategoryTheory.NatTrans.app_heq_of_heq`, `CategoryTheory.Functor.map_heq_of_heq`,
  `CategoryTheory.comp_heq_of_heq`, `CategoryTheory.Iso.hom_heq_of_heq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace CategoryTheory

/-- Components of natural transformations agree across a change of spelling of the categories,
the functors, the transformations and the object. -/
theorem NatTrans.app_heq_of_heq.{v₁, v₂, u₁, u₂} {C₁ C : Type u₁} {D₁ D : Type u₂}
    {iC₁ : Category.{v₁} C₁} {iC : Category.{v₁} C} {iD₁ : Category.{v₂} D₁} {iD : Category.{v₂} D}
    {F₁ G₁ : C₁ ⥤ D₁} {F G : C ⥤ D} {θ₁ : F₁ ⟶ G₁} {θ : F ⟶ G} {X₁ : C₁} {X : C}
    (eC : C₁ = C) (eD : D₁ = D) (hiC : HEq iC₁ iC) (hiD : HEq iD₁ iD) (hF : HEq F₁ F)
    (hG : HEq G₁ G) (hθ : HEq θ₁ θ) (hX : HEq X₁ X) : HEq (θ₁.app X₁) (θ.app X) := by
  subst eC eD; cases hiC; cases hiD; cases hF; cases hG; cases hθ; cases hX; rfl

/-- Images of morphisms agree across a change of spelling of the categories, the functor, the
objects and the morphism. -/
theorem Functor.map_heq_of_heq.{v₁, v₂, u₁, u₂} {C₁ C : Type u₁} {D₁ D : Type u₂}
    {iC₁ : Category.{v₁} C₁} {iC : Category.{v₁} C} {iD₁ : Category.{v₂} D₁} {iD : Category.{v₂} D}
    {F₁ : C₁ ⥤ D₁} {F : C ⥤ D} {X₁ Y₁ : C₁} {X Y : C} {f₁ : X₁ ⟶ Y₁} {f : X ⟶ Y}
    (eC : C₁ = C) (eD : D₁ = D) (hiC : HEq iC₁ iC) (hiD : HEq iD₁ iD) (hF : HEq F₁ F)
    (hX : HEq X₁ X) (hY : HEq Y₁ Y) (hf : HEq f₁ f) : HEq (F₁.map f₁) (F.map f) := by
  subst eC eD; cases hiC; cases hiD; cases hF; cases hX; cases hY; cases hf; rfl

/-- Composites agree across a change of spelling of the category, the objects and the two
morphisms. -/
theorem comp_heq_of_heq.{v, u'} {C₁ C : Type u'} {i₁ : Category.{v} C₁} {i : Category.{v} C}
    {X₁ Y₁ Z₁ : C₁} {X Y Z : C} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Z₁} {f : X ⟶ Y} {g : Y ⟶ Z}
    (eC : C₁ = C) (ei : HEq i₁ i) (eX : HEq X₁ X) (eY : HEq Y₁ Y) (eZ : HEq Z₁ Z)
    (hf : HEq f₁ f) (hg : HEq g₁ g) : HEq (f₁ ≫ g₁) (f ≫ g) := by
  subst eC; cases ei; cases eX; cases eY; cases eZ; cases hf; cases hg; rfl

/-- Underlying morphisms of isomorphisms agree across a change of spelling of the category, the
objects and the isomorphism. -/
theorem Iso.hom_heq_of_heq.{v, u'} {C₁ C : Type u'} {i₁ : Category.{v} C₁} {i : Category.{v} C}
    {X₁ Y₁ : C₁} {X Y : C} {e₁ : X₁ ≅ Y₁} {e : X ≅ Y}
    (eC : C₁ = C) (ei : HEq i₁ i) (eX : HEq X₁ X) (eY : HEq Y₁ Y) (he : HEq e₁ e) :
    HEq e₁.hom e.hom := by
  subst eC; cases ei; cases eX; cases eY; cases he; rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The hypothesis number 1 of a sevenfold implication, as a proposition. -/
abbrev HypothesisOf₇_1 {α1 α2 α3 α4 α5 α6 α7 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → β) : Prop := α1
/-- The hypothesis number 2 of a sevenfold implication, as a proposition. -/
abbrev HypothesisOf₇_2 {α1 α2 α3 α4 α5 α6 α7 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → β) : Prop := α2
/-- The hypothesis number 3 of a sevenfold implication, as a proposition. -/
abbrev HypothesisOf₇_3 {α1 α2 α3 α4 α5 α6 α7 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → β) : Prop := α3
/-- The hypothesis number 4 of a sevenfold implication, as a proposition. -/
abbrev HypothesisOf₇_4 {α1 α2 α3 α4 α5 α6 α7 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → β) : Prop := α4
/-- The hypothesis number 5 of a sevenfold implication, as a proposition. -/
abbrev HypothesisOf₇_5 {α1 α2 α3 α4 α5 α6 α7 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → β) : Prop := α5
/-- The hypothesis number 6 of a sevenfold implication, as a proposition. -/
abbrev HypothesisOf₇_6 {α1 α2 α3 α4 α5 α6 α7 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → β) : Prop := α6
/-- The hypothesis number 7 of a sevenfold implication, as a proposition. -/
abbrev HypothesisOf₇_7 {α1 α2 α3 α4 α5 α6 α7 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → β) : Prop := α7
/-- The hypothesis number 1 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_1 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α1
/-- The hypothesis number 2 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_2 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α2
/-- The hypothesis number 3 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_3 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α3
/-- The hypothesis number 4 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_4 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α4
/-- The hypothesis number 5 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_5 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α5
/-- The hypothesis number 6 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_6 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α6
/-- The hypothesis number 7 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_7 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α7
/-- The hypothesis number 8 of a eightfold implication, as a proposition. -/
abbrev HypothesisOf₈_8 {α1 α2 α3 α4 α5 α6 α7 α8 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → β) : Prop := α8
/-- The hypothesis number 1 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_1 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α1
/-- The hypothesis number 2 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_2 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α2
/-- The hypothesis number 3 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_3 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α3
/-- The hypothesis number 4 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_4 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α4
/-- The hypothesis number 5 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_5 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α5
/-- The hypothesis number 6 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_6 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α6
/-- The hypothesis number 7 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_7 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α7
/-- The hypothesis number 8 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_8 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α8
/-- The hypothesis number 9 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_9 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α9
/-- The hypothesis number 10 of a tenfold implication, as a proposition. -/
abbrev HypothesisOf₁₀_10 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → β) : Prop := α10
end AlgebraicGeometry.Space
