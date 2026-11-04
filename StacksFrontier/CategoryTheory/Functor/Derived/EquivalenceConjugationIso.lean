module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Right Kan extensions and total left derived functors conjugated by equivalences

Let `LF₁ : D₁ ⥤ H₁` be a right Kan extension of `F₁ : C₁ ⥤ H₁` along `L₁ : C₁ ⥤ D₁`, and
`LF₂ : D₂ ⥤ H₂` one of `F₂ : C₂ ⥤ H₂` along `L₂ : C₂ ⥤ D₂`. Given equivalences
`G : C₁ ⥤ C₂`, `G' : D₁ ⥤ D₂`, `E : H₁ ⥤ H₂` with `G ⋙ L₂ ≅ L₁ ⋙ G'` and `F₁ ⋙ E ≅ G ⋙ F₂`,
the two Kan extensions are conjugate: `LF₁ ⋙ E ≅ G' ⋙ LF₂`.

For total left derived functors this says that a derived functor commutes with equivalences of
the source and target categories which intertwine the underived functors and the localization
functors. It is how a derived pullback is compared with the derived pullback of an equivalent
presentation of the same morphism of ringed topoi.

## Main definitions

* `CategoryTheory.Functor.rightKanExtensionConjugateIso`: `LF₁ ⋙ E ≅ G' ⋙ LF₂`.
* `CategoryTheory.Functor.totalLeftDerivedConjugateIso`: the same for total left derived
  functors.

## Implementation notes

`LF₁ ⋙ E` is a right Kan extension of `F₁ ⋙ E` along `L₁`, by
`CategoryTheory.Functor.isRightKanExtension_postcompose₂_iff`; `G' ⋙ LF₂` is one of
`G ⋙ F₂ ≅ F₁ ⋙ E` along `L₁`, by
`CategoryTheory.Functor.isRightKanExtension_iff_precomp_equivalence`. Right Kan extensions are
unique up to isomorphism.

The companion `CategoryTheory.Functor.hasLeftDerivedFunctor_conjugate_iff`
(`StacksFrontier/CategoryTheory/Functor/Derived/EquivalenceConjugation.lean`) is about the existence
of the derived functor; this file compares two derived functors which both exist.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

section

variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁]
  [Category* D₂] [Category* H₁] [Category* H₂]
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {F₁ : C₁ ⥤ H₁} {F₂ : C₂ ⥤ H₂}
  (LF₁ : D₁ ⥤ H₁) (α₁ : L₁ ⋙ LF₁ ⟶ F₁) (LF₂ : D₂ ⥤ H₂) (α₂ : L₂ ⋙ LF₂ ⟶ F₂)
  {G : C₁ ⥤ C₂} {G' : D₁ ⥤ D₂} (E : H₁ ⥤ H₂) [G.IsEquivalence] [G'.IsEquivalence]
  [E.IsEquivalence] (iso : G ⋙ L₂ ≅ L₁ ⋙ G') (β : F₁ ⋙ E ≅ G ⋙ F₂)

/-- The counit exhibiting `G' ⋙ LF₂` as a right Kan extension of `F₁ ⋙ E` along `L₁`. -/
def rightKanExtensionConjugateCounit : L₁ ⋙ G' ⋙ LF₂ ⟶ F₁ ⋙ E :=
  whiskerLeft L₁ (Iso.refl (G' ⋙ LF₂)).inv ≫ (associator _ _ _).inv ≫
    whiskerRight iso.inv LF₂ ≫ (associator _ _ _).hom ≫ whiskerLeft G α₂ ≫ β.inv

include iso in
omit [E.IsEquivalence] in
/-- `G' ⋙ LF₂` is a right Kan extension of `F₁ ⋙ E` along `L₁`. -/
theorem isRightKanExtension_rightKanExtensionConjugateCounit [LF₂.IsRightKanExtension α₂] :
    (G' ⋙ LF₂).IsRightKanExtension (rightKanExtensionConjugateCounit LF₂ α₂ E iso β) :=
  (isRightKanExtension_iff_precomp_equivalence (rightKanExtensionConjugateCounit LF₂ α₂ E iso β)
    α₂ iso β (Iso.refl _) rfl).1 inferInstance

/-- **Right Kan extensions are conjugate under equivalences.** If `LF₁`, `LF₂` are right Kan
extensions of `F₁`, `F₂` along `L₁`, `L₂`, and the equivalences `G`, `G'`, `E` satisfy
`G ⋙ L₂ ≅ L₁ ⋙ G'` and `F₁ ⋙ E ≅ G ⋙ F₂`, then `LF₁ ⋙ E ≅ G' ⋙ LF₂`. -/
noncomputable def rightKanExtensionConjugateIso [LF₁.IsRightKanExtension α₁]
    [LF₂.IsRightKanExtension α₂] : LF₁ ⋙ E ≅ G' ⋙ LF₂ :=
  haveI : (LF₁ ⋙ E).IsRightKanExtension ((associator _ _ _).inv ≫ whiskerRight α₁ E) :=
    (isRightKanExtension_postcompose₂_iff LF₁ α₁ E).2 inferInstance
  haveI := isRightKanExtension_rightKanExtensionConjugateCounit LF₂ α₂ E iso β
  rightKanExtensionUnique (LF₁ ⋙ E) ((associator _ _ _).inv ≫ whiskerRight α₁ E)
    (G' ⋙ LF₂) (rightKanExtensionConjugateCounit LF₂ α₂ E iso β)

end

section

variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁]
  [Category* D₂] [Category* H₁] [Category* H₂]
  {G : C₁ ⥤ C₂} {G' : D₁ ⥤ D₂} (E : H₁ ⥤ H₂) [G.IsEquivalence] [G'.IsEquivalence]
  [E.IsEquivalence]

/-- **Total left derived functors are conjugate under equivalences.** If `F₁`, `F₂` have total
left derived functors for `W₁`, `W₂` along the localization functors `L₁`, `L₂`, and the
equivalences `G`, `G'`, `E` satisfy `G ⋙ L₂ ≅ L₁ ⋙ G'` and `F₁ ⋙ E ≅ G ⋙ F₂`, then
`LF₁ ⋙ E ≅ G' ⋙ LF₂`. -/
noncomputable def totalLeftDerivedConjugateIso (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) [L₁.IsLocalization W₁]
    [L₂.IsLocalization W₂] (F₁ : C₁ ⥤ H₁) (F₂ : C₂ ⥤ H₂) [F₁.HasLeftDerivedFunctor W₁]
    [F₂.HasLeftDerivedFunctor W₂] (iso : G ⋙ L₂ ≅ L₁ ⋙ G') (β : F₁ ⋙ E ≅ G ⋙ F₂) :
    F₁.totalLeftDerived L₁ W₁ ⋙ E ≅ G' ⋙ F₂.totalLeftDerived L₂ W₂ :=
  haveI := IsLeftDerivedFunctor.isRightKanExtension (F₁.totalLeftDerived L₁ W₁)
    (F₁.totalLeftDerivedCounit L₁ W₁) W₁
  haveI := IsLeftDerivedFunctor.isRightKanExtension (F₂.totalLeftDerived L₂ W₂)
    (F₂.totalLeftDerivedCounit L₂ W₂) W₂
  rightKanExtensionConjugateIso _ (F₁.totalLeftDerivedCounit L₁ W₁) _
    (F₂.totalLeftDerivedCounit L₂ W₂) E iso β

end

end CategoryTheory.Functor
