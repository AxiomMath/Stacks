module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Recognizing a mate whose source is a right derived functor

`Stacks.CategoryTheory.mateEquiv_eq_of_counit` recognizes a 2-cell `β : R₁ ⋙ G ⟶ H ⋙ R₂` as the
mate of `α : G ⋙ L₂ ⟶ L₁ ⋙ H` from its counit square, one object at a time.  A comparison
produced by right derivation is not computable at an arbitrary object: it is a lift through a
localization, pinned only after the derivation unit.  This file records that the counit square
then needs to be checked only on the image of that localization, provided the source `R₁ ⋙ G` of
the two 2-cells is itself a total right derived functor.

## Main results

* `Stacks.CategoryTheory.mateEquiv_eq_of_counit_rightDerived`: a 2-cell out of a right derived
  functor whose counit square commutes after the derivation unit is the mate.

## Implementation notes

The hypothesis is the counit square of `Stacks.CategoryTheory.mateEquiv_eq_of_counit` with
`γ.app X` prepended on both sides, and is therefore weaker than that statement's: it quantifies
only over the objects of the category being localized.  The proof transposes along `adj₂`, where
`CategoryTheory.mateEquiv_counit` turns the mate into `α` followed by `H` of the counit of
`adj₁`, and then appeals to `CategoryTheory.Functor.rightDerived_ext`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace Stacks.CategoryTheory

variable {A : Type u₁} {B : Type u₂} {E : Type u₃} {F : Type u₄} {C : Type u₅}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} E] [Category.{v₄} F] [Category.{v₅} C]
  {G : A ⥤ E} {H : B ⥤ F} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- **A 2-cell out of a right derived functor is the mate as soon as its counit square commutes
after the derivation unit.**  Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions, let
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` be a 2-cell and let `β : R₁ ⋙ G ⟶ H ⋙ R₂` be a candidate for its mate.
Suppose `R₁ ⋙ G` is a total right derived functor of `F₀` along a localization `L` of `W`, with
derivation unit `γ`.  If the counit square of `β` commutes after `γ` at every object of the
category being localized, then `β` is the mate of `α`.

`Stacks.CategoryTheory.mateEquiv_eq_of_counit` is the same statement with the counit square
asked for at every object of `B`.  That is what a comparison built by right derivation cannot
supply: it is a lift through `L`, so it is pinned only after `γ`, which is exactly the hypothesis
here. -/
theorem mateEquiv_eq_of_counit_rightDerived (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂) {L : C ⥤ B} {F₀ : C ⥤ E}
    (γ : F₀ ⟶ L ⋙ (R₁ ⋙ G)) (W : MorphismProperty C) [L.IsLocalization W]
    [(R₁ ⋙ G).IsRightDerivedFunctor γ W]
    (h : ∀ X : C, L₂.map (γ.app X) ≫ α.app (R₁.obj (L.obj X)) ≫
          H.map (adj₁.counit.app (L.obj X)) =
        L₂.map (γ.app X ≫ β.app (L.obj X)) ≫ adj₂.counit.app (H.obj (L.obj X))) :
    mateEquiv adj₁ adj₂ α = β := by
  have key : mateEquiv adj₁ adj₂ α = β := by
    refine Functor.rightDerived_ext (R₁ ⋙ G) γ W (H ⋙ R₂) _ _ (NatTrans.ext (funext fun X => ?_))
    have hmate := mateEquiv_counit adj₁ adj₂ α (L.obj X)
    apply (adj₂.homEquiv (F₀.obj X) (H.obj (L.obj X))).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    rw [hmate, h X, Functor.map_comp, Category.assoc]
  exact key

end Stacks.CategoryTheory

end
