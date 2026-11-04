module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous

/-!
# The legs of the right Kan extension of the underlying presheaf

Let `L : A ⥤ B` and let `F : H ⥤ Type t` preserve the limits over the comma categories
`StructuredArrow b L`, as a forgetful functor of a concrete category does. Mathlib's
`CategoryTheory.Functor.rightKanExtensionCompIsoOfPreserves` identifies the right Kan extension
along `L` of an `H`-valued functor, read through `F`, with the right Kan extension of its
composite with `F`. This file computes that comparison on the legs of the limit cone that computes
the extension pointwise, and shows that it is natural in the extended functor.

## Main results

* `Stacks.SheafOfModules.ranCompIso_hom_app_comp_ranπ`: the comparison carries the leg of the
  limit cone at an index to the image under `F` of the leg at that index.
* `Stacks.SheafOfModules.ranCompIso_hom_app_naturality` and
  `Stacks.SheafOfModules.ranCompIso_naturality`: the comparison is natural in the extended
  functor, over one object of `B` and as an equality of natural transformations.
* `Stacks.SheafOfModules.ranπ_ext`: two sections of a `Type`-valued right Kan extension agree as
  soon as all their legs agree.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe t vA uA vB uB vH uH

namespace Stacks.SheafOfModules

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B] (L : A ⥤ B)
  {H : Type uH} [Category.{vH} H] (F : H ⥤ Type t)
  [∀ N : A ⥤ H, L.HasPointwiseRightKanExtension N]
  [∀ N : A ⥤ Type t, L.HasPointwiseRightKanExtension N]
  [∀ b : B, PreservesLimitsOfShape (StructuredArrow b L) F]
  (N : A ⥤ H)

/-- **The comparison carries legs to legs.** Followed by the leg of the limit cone computing the
right Kan extension of `N ⋙ F` at the index `j`, the comparison is the image under `F` of the leg
at `j` for `N`. -/
@[reassoc]
lemma ranCompIso_hom_app_comp_ranπ (b : B) (j : StructuredArrow b L) :
    (F.rightKanExtensionCompIsoOfPreserves N L).hom.app b ≫ ranπ L (N ⋙ F) b j =
      F.map (ranπ L N b j) := by
  have h := (F.rightKanExtensionCompIsoOfPreserves N L).hom.naturality j.hom
  dsimp only [ranπ]
  rw [F.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g ↦ g ≫ (L.ranCounit.app (N ⋙ F)).app j.right) h.symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g ↦ F.map ((L.ran.obj N).map j.hom) ≫ g)
          (Functor.rightKanExtensionCompIsoOfPreserves_hom_fac_app F N L j.right))))

/-- **The comparison is natural in the extended functor, over one object of `B`.** -/
lemma ranCompIso_hom_app_naturality {N₁ N₂ : A ⥤ H} (φ : N₁ ⟶ N₂) (b : B) :
    F.map ((L.ran.map φ).app b) ≫ (F.rightKanExtensionCompIsoOfPreserves N₂ L).hom.app b =
      (F.rightKanExtensionCompIsoOfPreserves N₁ L).hom.app b ≫
        (L.ran.map (Functor.whiskerRight φ F)).app b := by
  refine ran_hom_ext L (N₂ ⋙ F) (fun j ↦ ?_)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g ↦ F.map ((L.ran.map φ).app b) ≫ g)
        (ranCompIso_hom_app_comp_ranπ L F N₂ b j)).trans
      ((F.map_comp _ _).symm.trans
        ((congrArg (fun g ↦ F.map g) (ranπ_map_functor L φ b j)).trans
          ((F.map_comp _ _).trans
            ((congrArg (fun g ↦ g ≫ F.map (φ.app j.right))
                (ranCompIso_hom_app_comp_ranπ L F N₁ b j).symm).trans
              ((Category.assoc _ _ _).trans
                ((congrArg
                    (fun g ↦ (F.rightKanExtensionCompIsoOfPreserves N₁ L).hom.app b ≫ g)
                    (ranπ_map_functor L (Functor.whiskerRight φ F) b j).symm).trans
                  (Category.assoc _ _ _).symm)))))))

/-- **The comparison is natural in the extended functor**, as an equality of natural
transformations. -/
lemma ranCompIso_naturality {N₁ N₂ : A ⥤ H} (φ : N₁ ⟶ N₂) :
    Functor.whiskerRight (L.ran.map φ) F ≫ (F.rightKanExtensionCompIsoOfPreserves N₂ L).hom =
      (F.rightKanExtensionCompIsoOfPreserves N₁ L).hom ≫
        L.ran.map (Functor.whiskerRight φ F) :=
  NatTrans.ext (funext fun b ↦ ranCompIso_hom_app_naturality L F φ b)

section Elementwise

variable {A' : Type uA} [Category.{vA} A'] {B' : Type uB} [Category.{vB} B'] (L' : A' ⥤ B')
  [∀ N : A' ⥤ Type t, L'.HasPointwiseRightKanExtension N] (N' : A' ⥤ Type t)

/-- **Elementwise extensionality for a `Type`-valued right Kan extension.** Two sections of the
extension over the same object agree as soon as their images under every leg of the limit cone
agree. -/
lemma ranπ_ext {b : B'} {x y : (L'.ran.obj N').obj b}
    (h : ∀ j : StructuredArrow b L', ranπ L' N' b j x = ranπ L' N' b j y) : x = y :=
  (homOfElement_eq_iff x y).1
    (ran_hom_ext L' N' (fun j ↦ ConcreteCategory.hom_ext _ _ (fun _ ↦ h j)))

end Elementwise

end Stacks.SheafOfModules

end
