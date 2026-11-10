module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.PresheafComp

/-!
# The base change of right Kan extensions is the mate of the composition comparison

Let
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```
be a square of functors with a 2-cell `w : T ⋙ R ⟶ L ⋙ B`, and let right Kan extensions into a
category `H` exist along all four functors.  There are then two 2-cells attached to `w`:

* the base change `CategoryTheory.TwoSquare.ranBaseChange`, a transformation
  `Ran_B ⋙ R^* ⟶ L^* ⋙ Ran_T` of functors `(C₃ ⥤ H) ⥤ (C₂ ⥤ H)`, where `L^*` and `R^*` denote
  precomposition; and
* the comparison `Ran_B ∘ Ran_L ⟶ Ran_R ∘ Ran_T` of the two composites, the conjugate of the
  precomposition transformation induced by `w` for the two composite adjunctions.

The main result says they are mates for the adjunctions `L^* ⊣ Ran_L` and `R^* ⊣ Ran_R`.

## Main results

* `Stacks.CategoryTheory.ranCompSquare`: the comparison of the two composites.
* `Stacks.CategoryTheory.mateEquiv_symm_ranCompSquare`: its mate is the base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace Stacks.CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {H : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄] [Category.{v₅} H]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}

variable (H) in
/-- The comparison `Ran_B ∘ Ran_L ⟶ Ran_R ∘ Ran_T` attached to a 2-square `w`: the two composites
are right adjoints of precomposition with `L ⋙ B` and with `T ⋙ R` respectively, and `w` induces
a transformation of those precompositions, whose conjugate this is. -/
noncomputable def ranCompSquare
    [∀ F : C₁ ⥤ H, T.HasRightKanExtension F] [∀ F : C₁ ⥤ H, L.HasRightKanExtension F]
    [∀ F : C₂ ⥤ H, R.HasRightKanExtension F] [∀ F : C₃ ⥤ H, B.HasRightKanExtension F]
    (w : TwoSquare T L R B) :
    TwoSquare (L.ran (H := H)) T.ran B.ran R.ran :=
  TwoSquare.mk _ _ _ _
    (conjugateEquiv (Functor.ranCompAdjunction H L B) (Functor.ranCompAdjunction H T R)
      ((whiskeringLeft C₁ C₄ H).map w))

section

variable [∀ F : C₁ ⥤ H, T.HasRightKanExtension F] [∀ F : C₁ ⥤ H, L.HasRightKanExtension F]
  [∀ F : C₂ ⥤ H, R.HasRightKanExtension F] [∀ F : C₃ ⥤ H, B.HasRightKanExtension F]

/-- The comparison of the two composites, read through the identification of each composite with
a single right Kan extension: it is the contravariant functoriality of `Ran` applied to the
2-cell, conjugated by the two composition comparisons of
`CategoryTheory.Functor.ranCompIsoOfAdjunctions`.

This is the shape in which the comparison arises in practice, the composition comparisons being
how a commuting square of site functors produces a 2-cell. -/
theorem ranCompIso_hom_comp_ranCompSquare (w : TwoSquare T L R B) :
    (Functor.ranCompIsoOfAdjunctions H L B).hom ≫ (ranCompSquare H w) =
      conjugateEquiv ((L ⋙ B).ranAdjunction H) ((T ⋙ R).ranAdjunction H)
          ((whiskeringLeft C₁ C₄ H).map w) ≫
        (Functor.ranCompIsoOfAdjunctions H T R).hom := by
  change conjugateEquiv _ _ (𝟙 _) ≫ conjugateEquiv _ _ _ = conjugateEquiv _ _ _ ≫
    conjugateEquiv _ _ (𝟙 _)
  rw [conjugateEquiv_comp, conjugateEquiv_comp, Category.comp_id, Category.id_comp]

/-- **The base change of right Kan extensions is the mate of the comparison of the two
composites.** -/
theorem mateEquiv_symm_ranCompSquare (w : TwoSquare T L R B) :
    ((mateEquiv (L.ranAdjunction H) (R.ranAdjunction H)).symm (ranCompSquare H w)) =
      w.ranBaseChange (D := H) := by
  refine NatTrans.ext (funext fun Y => ?_)
  have key := Stacks.CategoryTheory.homEquiv_mate (B.ranAdjunction H) (L.ranAdjunction H)
    (R.ranAdjunction H) (T.ranAdjunction H) (ranCompSquare H w)
    ((B.ranAdjunction H).counit.app Y)
  have h1 : ((B.ranAdjunction H).homEquiv (B.ran.obj Y) Y) ((B.ranAdjunction H).counit.app Y) =
      𝟙 _ := by
    rw [Adjunction.homEquiv_unit, (B.ranAdjunction H).right_triangle_components]
  simp only [Functor.id_obj, h1] at key
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at key
  rw [← key, TwoSquare.ranBaseChange_app]
  congr 1
  simp only [ranCompSquare, Functor.ranCompAdjunction, Equiv.symm_apply_apply]
  refine NatTrans.ext (funext fun c => ?_)
  simp

/-- **Beck–Chevalley for right Kan extensions, in mate form.** For a Guitart exact square the
comparison of the two composites of right Kan extensions has an invertible mate.

Without the Guitart exactness the mate of an isomorphism is in general only a morphism; what makes
this one invertible is that it *is* the base change, by
`Stacks.CategoryTheory.mateEquiv_symm_ranCompSquare`. -/
theorem isIso_mateEquiv_symm_ranCompSquare [∀ F : C₃ ⥤ H, B.HasPointwiseRightKanExtension F]
    (w : TwoSquare T L R B) [w.GuitartExact] :
    IsIso ((mateEquiv (L.ranAdjunction H) (R.ranAdjunction H)).symm
      (ranCompSquare H w)) := by
  rw [mateEquiv_symm_ranCompSquare]
  infer_instance

end

end Stacks.CategoryTheory

end
