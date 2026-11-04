module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Left Kan extensions and precomposition with a functor whose whiskering is fully faithful

Being a left Kan extension of `F : C ⥤ H` along `L : C ⥤ D` can be tested after precomposing
with a functor `q : C' ⥤ C`, provided only that precomposition with `q` is fully faithful as a
functor `(C ⥤ H) ⥤ (C' ⥤ H)`.

## Main results

* `CategoryTheory.Functor.isLeftKanExtension_iff_precomp_of_fullyFaithful`: for such a `q`, a
  functor is a left Kan extension of `F` along `L` with unit `α` if and only if it is one of
  `q ⋙ F` along `q ⋙ L` with the whiskered unit.

## Implementation notes

Mathlib's `CategoryTheory.Functor.isLeftKanExtension_iff_precomp` is the same statement under
the stronger hypothesis that `q` itself is an equivalence. The weaker hypothesis here is what a
localization functor satisfies: the homotopy-category quotient is not an equivalence, while
precomposition with it is fully faithful, and that is already enough for
`CategoryTheory.StructuredArrow.isEquivalenceMap₂` to make
`CategoryTheory.Functor.LeftExtension.precomp` an equivalence, which is all the proof uses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Being a left Kan extension can be tested after precomposing with a functor whose
whiskering is fully faithful. -/
lemma isLeftKanExtension_iff_precomp_of_fullyFaithful
    {C C' D H : Type*} [Category C] [Category C'] [Category D] [Category H]
    (q : C' ⥤ C) [((whiskeringLeft C' C H).obj q).Full]
    [((whiskeringLeft C' C H).obj q).Faithful]
    {L : C ⥤ D} {F : C ⥤ H} (G : D ⥤ H) (α : F ⟶ L ⋙ G) :
    G.IsLeftKanExtension α ↔
      G.IsLeftKanExtension (whiskerLeft q α ≫ (Functor.associator _ _ _).inv) := by
  have : (LeftExtension.precomp L F q).IsEquivalence := StructuredArrow.isEquivalenceMap₂ _ _
  let E₁ := LeftExtension.mk G α
  let E₂ := LeftExtension.mk G (whiskerLeft q α ≫ (Functor.associator _ _ _).inv)
  let e₁ : (LeftExtension.precomp L F q).obj E₁ ≅ E₂ :=
    StructuredArrow.isoMk (Iso.refl G) (by
      ext Y
      simp [LeftExtension.precomp, E₁, E₂])
  let e : E₁.IsUniversal ≃ E₂.IsUniversal :=
    (IsInitial.isInitialIffObj (LeftExtension.precomp L F q) E₁).trans
      (IsInitial.equivOfIso e₁)
  exact ⟨fun _ => ⟨⟨e (isUniversalOfIsLeftKanExtension G α)⟩⟩,
    fun _ => ⟨⟨e.symm (isUniversalOfIsLeftKanExtension G _)⟩⟩⟩

end CategoryTheory.Functor

end
