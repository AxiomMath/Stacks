module

public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategoriesApp

/-!
# Invertibility of a mate at one object along a change of categories

In the situation of `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq` (two squares of adjunctions
joined by functors at the four corners), invertibility of the back mate at one object gives
invertibility of the image of the front mate under the functor `ΦF` at the lower right corner.

## Main results

* `Stacks.CategoryTheory.isIso_map_mateEquiv_symm_app_of_isIso` — the transfer at one object.

## Implementation notes

This theorem extends `StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories` and is
placed in a file of its own. The cube identity at one
object it uses, `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app`, is in
`StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategoriesApp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace Stacks.CategoryTheory

section Cube

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  {C' : Type u₅} {D' : Type u₆} {E' : Type u₇} {F' : Type u₈}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  [Category.{v₅} C'] [Category.{v₆} D'] [Category.{v₇} E'] [Category.{v₈} F']
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} {L₂' : E' ⥤ F'} {R₂' : F' ⥤ E'}
  {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
  {ΦC : C ⥤ C'} {ΦD : D ⥤ D'} {ΦE : E ⥤ E'} {ΦF : F ⥤ F'}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
  (τ₁ : TwoSquare ΦC L₁ L₁' ΦD) (τ₂ : TwoSquare ΦE L₂ L₂' ΦF)
  (σG : G ⋙ ΦE ⟶ ΦC ⋙ G') (σH : ΦD ⋙ H' ⟶ H ⋙ ΦF)
  (β : TwoSquare R₁ H G R₂) (β' : TwoSquare R₁' H' G' R₂')

/-- **Invertibility of the back mate gives invertibility of the image of the front mate.** In the
situation of `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`, with the four comparisons
invertible, if the back mate is invertible at `ΦC c` then the image under `ΦF` of the front mate
at `c` is invertible. No hypothesis is made on `ΦF`: this is the form needed when the front mate
is detected by a jointly conservative family of functors `ΦF`, one cube for each. -/
public theorem isIso_map_mateEquiv_symm_app_of_isIso
    [IsIso τ₁] [IsIso τ₂] [IsIso σG] [IsIso σH]
    (h : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
      β ≫ᵥ mateEquiv adj₂ adj₂' τ₂) (c : C)
    [IsIso (((mateEquiv adj₁' adj₂').symm β').app (ΦC.obj c))] :
    IsIso (ΦF.map (((mateEquiv adj₁ adj₂).symm β).app c)) := by
  have e := mateEquiv_symm_hComp_eq_app adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' h c
  have : IsIso (τ₂.app (G.obj c) ≫
      ΦF.map (((mateEquiv adj₁ adj₂).symm β).app c)) := by
    rw [e]; infer_instance
  exact IsIso.of_isIso_comp_left (τ₂.app (G.obj c)) _

end Cube

end Stacks.CategoryTheory

end
