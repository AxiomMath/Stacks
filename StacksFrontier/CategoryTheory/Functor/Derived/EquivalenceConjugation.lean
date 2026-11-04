module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Total left derived functors under conjugation by equivalences

Let `F : C ⥤ H` be a functor and `W : MorphismProperty C`. Replacing `C` by an equivalent
category along `G : C' ⥤ C`, and `H` by an equivalent one along `G' : H ⥤ H'`, turns `F` into
`G ⋙ F ⋙ G'` and `W` into its inverse image along `G`. This file proves that the existence of a
total left derived functor is unchanged by that replacement.

Mathlib compares the total left derived functors of two naturally isomorphic functors between
the same pair of categories (`CategoryTheory.Functor.hasLeftDerivedFunctor_iff_of_iso`) and
compares the property of *being* a left derived functor across a localizer morphism whose
functor is an equivalence
(`CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp`); the statements below are
about the existence of the derived functor and about both variances at once.

## Main results

* `CategoryTheory.Functor.hasRightKanExtension_precomp_iff` and
  `CategoryTheory.Functor.hasRightKanExtension_postcompose_iff`: the existence of a right Kan
  extension is unchanged by precomposing both the extended functor and the functor it is
  extended along with one equivalence, and by postcomposing the extended functor with another.
* `CategoryTheory.Functor.hasLeftDerivedFunctor_precomp_iff` and
  `CategoryTheory.Functor.hasLeftDerivedFunctor_postcompose_iff`: the two corresponding
  statements for total left derived functors.
* `CategoryTheory.Functor.hasLeftDerivedFunctor_conjugate_iff`: **conjugation by two
  equivalences.** `F` has a total left derived functor with respect to `W` if and only if
  `G ⋙ F ⋙ G'` has one with respect to `W.inverseImage G`.

## Implementation notes

A total left derived functor is a right Kan extension along a localization functor for `W`, so
each half is the corresponding statement about right Kan extensions evaluated at a suitable
localization functor. For the source the localization functor used on the primed side is
`G ⋙ W.Q`, which localizes `W.inverseImage G` because `G` is an equivalence and the class of
morphisms is the inverse image of `W`; that is
`CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_isInduced`, whence the hypothesis
that `W` respects isomorphisms. The target needs no hypothesis on `W`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.Functor

variable {C : Type u₁} {C' : Type u₂} {D : Type u₃} {H : Type u₄} {H' : Type u₅}
  [Category.{v₁} C] [Category.{v₂} C'] [Category.{v₃} D] [Category.{v₄} H] [Category.{v₅} H']

/-- Precomposing both the functor being extended and the functor it is extended along with an
equivalence does not change the existence of a right Kan extension. -/
lemma hasRightKanExtension_precomp_iff (L : C ⥤ D) (F : C ⥤ H) (G : C' ⥤ C) [G.IsEquivalence] :
    HasRightKanExtension L F ↔ HasRightKanExtension (G ⋙ L) (G ⋙ F) :=
  (RightExtension.precomp L F G).asEquivalence.hasTerminal_iff

/-- Postcomposing the functor being extended with an equivalence does not change the existence
of a right Kan extension. -/
lemma hasRightKanExtension_postcompose_iff (L : C ⥤ D) (F : C ⥤ H) (G : H ⥤ H')
    [G.IsEquivalence] :
    HasRightKanExtension L F ↔ HasRightKanExtension L (F ⋙ G) :=
  (RightExtension.postcompose₂ L F G).asEquivalence.hasTerminal_iff

/-- A functor has a total left derived functor with respect to `W` if and only if its composite
with an equivalence of the target does. -/
lemma hasLeftDerivedFunctor_postcompose_iff (F : C ⥤ H) (W : MorphismProperty C) (G : H ⥤ H')
    [G.IsEquivalence] :
    F.HasLeftDerivedFunctor W ↔ (F ⋙ G).HasLeftDerivedFunctor W := by
  rw [hasLeftDerivedFunctor_iff F W.Q W, hasLeftDerivedFunctor_iff (F ⋙ G) W.Q W]
  exact hasRightKanExtension_postcompose_iff W.Q F G

/-- A functor has a total left derived functor with respect to `W` if and only if its composite
with an equivalence of the source does with respect to the inverse image of `W`. -/
lemma hasLeftDerivedFunctor_precomp_iff (F : C ⥤ H) (W : MorphismProperty C) [W.RespectsIso]
    (G : C' ⥤ C) [G.IsEquivalence] :
    F.HasLeftDerivedFunctor W ↔ (G ⋙ F).HasLeftDerivedFunctor (W.inverseImage G) := by
  let Φ : LocalizerMorphism (W.inverseImage G) W := LocalizerMorphism.ofEq rfl
  have hΦe : Φ.functor.IsEquivalence := inferInstanceAs G.IsEquivalence
  have hΦi : Φ.IsInduced := ⟨rfl⟩
  have := Φ.isLocalizedEquivalence_of_isInduced
  have hloc : (G ⋙ W.Q).IsLocalization (W.inverseImage G) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ W.Q
  rw [hasLeftDerivedFunctor_iff F W.Q W,
    hasLeftDerivedFunctor_iff (G ⋙ F) (G ⋙ W.Q) (W.inverseImage G)]
  exact hasRightKanExtension_precomp_iff W.Q F G

/-- **Total left derived functors are preserved by conjugation by equivalences.** A functor
`F : C ⥤ H` has a total left derived functor with respect to `W` if and only if its conjugate by
an equivalence `eC` of the source and an equivalence `eH` of the target has one with respect to
the inverse image of `W`. -/
theorem hasLeftDerivedFunctor_conjugate_iff (F : C ⥤ H) (W : MorphismProperty C) [W.RespectsIso]
    (eC : C' ≌ C) (eH : H ≌ H') :
    F.HasLeftDerivedFunctor W ↔
      (eC.functor ⋙ F ⋙ eH.functor).HasLeftDerivedFunctor (W.inverseImage eC.functor) := by
  rw [hasLeftDerivedFunctor_postcompose_iff F W eH.functor,
    hasLeftDerivedFunctor_precomp_iff (F ⋙ eH.functor) W eC.functor]

end CategoryTheory.Functor

end
