module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Left derived functors along a localization that factors through a quotient

Mathlib's `CategoryTheory.Functor.isRightKanExtension_iff_precomp` compares a right Kan
extension along `L : C ⥤ D` with the one along `G ⋙ L` when `G` is an *equivalence*. The
situation this file covers is the other one that occurs for differential graded modules: `G` is
a quotient functor `q : C' ⥤ C`, which is not an equivalence, but for which precomposition of
natural transformations, `(whiskeringLeft C' C H).obj q`, is fully faithful. That is exactly
enough for the comparison, because the index category of the Kan extension only sees
`CostructuredArrow` along that whiskering.

The consequence this file is written for: a total left derived functor along `L` for `W` is the
total left derived functor along `q ⋙ L` for any class `W'` that `q ⋙ L` localizes. For
differential graded modules `q` is the quotient by homotopy, `L` is the localization of the
homotopy category at the quasi-isomorphisms, and `W'` is the class of quasi-isomorphisms of
differential graded modules.

## Main results

* `CategoryTheory.Functor.isRightKanExtension_precomp_whiskering`: a right Kan extension along
  `L` is one along `q ⋙ L`, when precomposition with `q` is fully faithful.
* `CategoryTheory.Functor.isLeftDerivedFunctor_precomp_whiskering`: **the same for total left
  derived functors**, with the class of morphisms replaced by one that `q ⋙ L` localizes.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {C' : Type u₂} {D : Type u₃} {H : Type u₄}
  [Category.{v₁} C] [Category.{v₂} C'] [Category.{v₃} D] [Category.{v₄} H]

/-- **A right Kan extension along `L` is a right Kan extension along `q ⋙ L`**, as soon as
precomposition with `q` is fully faithful on natural transformations with values in `H`. -/
theorem isRightKanExtension_precomp_whiskering (q : C' ⥤ C)
    [((whiskeringLeft C' C H).obj q).Full] [((whiskeringLeft C' C H).obj q).Faithful]
    {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) [LF.IsRightKanExtension α] :
    LF.IsRightKanExtension ((associator q L LF).hom ≫ whiskerLeft q α) := by
  have : (RightExtension.precomp L F q).IsEquivalence := by
    apply CostructuredArrow.isEquivalenceMap₂
  let e : (RightExtension.mk LF α).IsUniversal ≃
      (RightExtension.mk LF ((associator q L LF).hom ≫ whiskerLeft q α)).IsUniversal :=
    (IsTerminal.isTerminalIffObj (RightExtension.precomp L F q)
      (RightExtension.mk LF α)).trans
      (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  exact ⟨⟨e (isUniversalOfIsRightKanExtension LF α)⟩⟩

/-- **A total left derived functor along `L` is a total left derived functor along `q ⋙ L`**,
for any class of morphisms of `C'` that `q ⋙ L` localizes, as soon as precomposition with `q`
is fully faithful on natural transformations with values in `H`. -/
theorem isLeftDerivedFunctor_precomp_whiskering (q : C' ⥤ C)
    [((whiskeringLeft C' C H).obj q).Full] [((whiskeringLeft C' C H).obj q).Faithful]
    {L : C ⥤ D} {F : C ⥤ H} (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (W : MorphismProperty C) [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]
    (W' : MorphismProperty C') [(q ⋙ L).IsLocalization W'] :
    LF.IsLeftDerivedFunctor ((associator q L LF).hom ≫ whiskerLeft q α) W' := by
  have := IsLeftDerivedFunctor.isRightKanExtension LF α W
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  exact isRightKanExtension_precomp_whiskering q LF α

end CategoryTheory.Functor

end
