module

public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare

/-!
# The unit criterion for a mate, read at transported left adjoints

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions and let `e₁ : L₁ ≅ L₁'` and
`e₂ : L₂ ≅ L₂'` identify the two left adjoints with other functors, so that
`CategoryTheory.Adjunction.ofNatIsoLeft` presents `L₁' ⊣ R₁` and `L₂' ⊣ R₂`.  A 2-square
`β : R₁ ⋙ G ⟶ H ⋙ R₂` then has a mate `(mateEquiv adj₁ adj₂).symm β : G ⋙ L₂ ⟶ L₁ ⋙ H`, and
conjugating it by `e₁` and `e₂` reads that mate as a morphism `G ⋙ L₂' ⟶ L₁' ⋙ H`.

`CategoryTheory.mateEquiv_symm_eq_of_unit` recognises a candidate for the mate from the square
it makes with the two units.  This file states that criterion for the conjugated mate, with the
two units taken in the *transported* spelling: a candidate `α₀ : G ⋙ L₂' ⟶ L₁' ⋙ H` is the
conjugated mate as soon as it makes the unit square of the two transported adjunctions commute.

This is what lets a mate constructed from one spelling of the two left adjoints be identified
with a morphism written in another spelling, in the situation where the units are computable in
the second spelling and not in the first.

## Main results

* `CategoryTheory.mateEquiv_symm_whisker_eq_of_unit`: the recognition criterion for the
  conjugated mate, in terms of the units of the two transported adjunctions.

## Implementation notes

The proof is `CategoryTheory.mateEquiv_symm_eq_of_unit` applied to the candidate conjugated back
along `e₁` and `e₂`, plus `CategoryTheory.Adjunction.ofNatIsoLeft_unit` to unfold the two
transported units and the naturality of `β` at `e₁.hom` to move the conjugation across it.

Nothing here carries a Stacks attribute: this is a general fact about adjunctions.
-/

@[expose] public section

open CategoryTheory Category Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
variable {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')

/-- **A 2-square whose unit square commutes in the transported spelling is the conjugated
mate.**  If `α₀ : G ⋙ L₂' ⟶ L₁' ⋙ H` and `β : R₁ ⋙ G ⟶ H ⋙ R₂` satisfy the square made by the
units of the two adjunctions transported along `e₁` and `e₂`, then `α₀` is the mate of `β`
conjugated by `e₁` and `e₂`.

Only the transported units occur in the hypothesis, so the criterion can be checked entirely in
the spelling `L₁'`, `L₂'` of the two left adjoints. -/
theorem mateEquiv_symm_whisker_eq_of_unit (α₀ : G ⋙ L₂' ⟶ L₁' ⋙ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ c : C, (adj₂.ofNatIsoLeft e₂).unit.app (G.obj c) ≫ R₂.map (α₀.app c) =
      G.map ((adj₁.ofNatIsoLeft e₁).unit.app c) ≫ β.app (L₁'.obj c)) :
    Functor.whiskerLeft G e₂.inv ≫ (mateEquiv adj₁ adj₂).symm β ≫
        Functor.whiskerRight e₁.hom H = α₀ := by
  have key : (mateEquiv adj₁ adj₂).symm β =
      Functor.whiskerLeft G e₂.hom ≫ α₀ ≫ Functor.whiskerRight e₁.inv H := by
    refine mateEquiv_symm_eq_of_unit adj₁ adj₂ _ β ?_
    intro c
    have hc := h c
    have hnat := β.naturality (e₁.hom.app c)
    simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.map_comp, Functor.comp_obj, Functor.comp_map,
      Category.assoc] at hc hnat ⊢
    rw [reassoc_of% hc, reassoc_of% hnat]
    simp [← Functor.map_comp]
  rw [key]
  ext c
  simp [← Functor.map_comp]

end CategoryTheory

end
