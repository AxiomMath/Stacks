module

public import StacksFrontier.CategoryTheory.Functor.Derived.EquivalenceConjugationIso

/-!
# The defining property of the conjugation isomorphism of right Kan extensions

`CategoryTheory.Functor.rightKanExtensionConjugateIso` and its total-left-derived form
`CategoryTheory.Functor.totalLeftDerivedConjugateIso` are built by uniqueness of right Kan
extensions, so each is pinned down by the one factorisation through the counits that uniqueness
provides.  That factorisation is what this file records; without it the isomorphism is opaque and
nothing can be proved about how it interacts with anything else.

## Main results

* `CategoryTheory.Functor.rightKanExtensionConjugateCounit_app`: the counit exhibiting
  `G' ⋙ LF₂` as a right Kan extension, written out at an object.
* `CategoryTheory.Functor.rightKanExtensionConjugateIso_hom_app_comp`: **the conjugation
  isomorphism followed by the counit of the second Kan extension is the image under `E` of the
  counit of the first.**
* `CategoryTheory.Functor.totalLeftDerivedConjugateIso_hom_app_comp`: the same for total left
  derived functors — the conjugation isomorphism at `L₁ M`, followed by the comparison of the
  second derived functor with its underived functor, is the image of the comparison of the first.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

section

variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁]
  [Category* D₂] [Category* H₁] [Category* H₂]
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {F₁ : C₁ ⥤ H₁} {F₂ : C₂ ⥤ H₂}
  (LF₁ : D₁ ⥤ H₁) (α₁ : L₁ ⋙ LF₁ ⟶ F₁) (LF₂ : D₂ ⥤ H₂) (α₂ : L₂ ⋙ LF₂ ⟶ F₂)
  {G : C₁ ⥤ C₂} {G' : D₁ ⥤ D₂} (E : H₁ ⥤ H₂) [G.IsEquivalence] [G'.IsEquivalence]
  [E.IsEquivalence] (iso : G ⋙ L₂ ≅ L₁ ⋙ G') (β : F₁ ⋙ E ≅ G ⋙ F₂)

omit [G.IsEquivalence] [G'.IsEquivalence] [E.IsEquivalence] in
/-- `CategoryTheory.Functor.rightKanExtensionConjugateCounit` at an object. -/
theorem rightKanExtensionConjugateCounit_app (M : C₁) :
    (rightKanExtensionConjugateCounit LF₂ α₂ E iso β).app M =
      LF₂.map (iso.inv.app M) ≫ α₂.app (G.obj M) ≫ β.inv.app M := by
  simp [rightKanExtensionConjugateCounit]

include iso in
/-- **The defining factorisation of the conjugation isomorphism of right Kan extensions.**
At an object in the image of `L₁` the isomorphism `LF₁ ⋙ E ≅ G' ⋙ LF₂`, followed by the counit
exhibiting `G' ⋙ LF₂` as a right Kan extension of `F₁ ⋙ E`, is the image under `E` of the
counit of `LF₁`. -/
theorem rightKanExtensionConjugateIso_hom_app_comp [LF₁.IsRightKanExtension α₁]
    [LF₂.IsRightKanExtension α₂] (M : C₁) :
    (rightKanExtensionConjugateIso LF₁ α₁ LF₂ α₂ E iso β).hom.app (L₁.obj M) ≫
        LF₂.map (iso.inv.app M) ≫ α₂.app (G.obj M) ≫ β.inv.app M =
      E.map (α₁.app M) := by
  have : (LF₁ ⋙ E).IsRightKanExtension
      ((associator _ _ _).inv ≫ whiskerRight α₁ E) :=
    (isRightKanExtension_postcompose₂_iff LF₁ α₁ E).2 inferInstance
  have := isRightKanExtension_rightKanExtensionConjugateCounit LF₂ α₂ E iso β
  rw [← rightKanExtensionConjugateCounit_app LF₂ α₂ E iso β M]
  simp [rightKanExtensionConjugateIso, rightKanExtensionUnique]

end

section

variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁]
  [Category* D₂] [Category* H₁] [Category* H₂]
  {G : C₁ ⥤ C₂} {G' : D₁ ⥤ D₂} (E : H₁ ⥤ H₂) [G.IsEquivalence] [G'.IsEquivalence]
  [E.IsEquivalence]

/-- **The defining factorisation of the conjugation isomorphism of total left derived
functors.**  At an object in the image of the localization functor, the isomorphism
`LF₁ ⋙ E ≅ G' ⋙ LF₂`, followed by the identification of the two localizations and the comparison
of `LF₂` with `F₂`, is the image under `E` of the comparison of `LF₁` with `F₁`. -/
theorem totalLeftDerivedConjugateIso_hom_app_comp (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] (F₁ : C₁ ⥤ H₁) (F₂ : C₂ ⥤ H₂) [F₁.HasLeftDerivedFunctor W₁]
    [F₂.HasLeftDerivedFunctor W₂] (iso : G ⋙ L₂ ≅ L₁ ⋙ G') (β : F₁ ⋙ E ≅ G ⋙ F₂) (M : C₁) :
    (totalLeftDerivedConjugateIso E L₁ L₂ W₁ W₂ F₁ F₂ iso β).hom.app (L₁.obj M) ≫
        (F₂.totalLeftDerived L₂ W₂).map (iso.inv.app M) ≫
          (F₂.totalLeftDerivedCounit L₂ W₂).app (G.obj M) ≫ β.inv.app M =
      E.map ((F₁.totalLeftDerivedCounit L₁ W₁).app M) :=
  have := IsLeftDerivedFunctor.isRightKanExtension (F₁.totalLeftDerived L₁ W₁)
    (F₁.totalLeftDerivedCounit L₁ W₁) W₁
  have := IsLeftDerivedFunctor.isRightKanExtension (F₂.totalLeftDerived L₂ W₂)
    (F₂.totalLeftDerivedCounit L₂ W₂) W₂
  rightKanExtensionConjugateIso_hom_app_comp _ (F₁.totalLeftDerivedCounit L₁ W₁) _
    (F₂.totalLeftDerivedCounit L₂ W₂) E iso β M

end

end CategoryTheory.Functor

end
