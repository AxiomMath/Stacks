module

public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories

/-!
# The cube identity for mates, with its hypothesis read on components

`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` asks for an equality of two
pastings of 2-squares.  A consumer never has that equality in that form: what it has is, for each
object, an equation between two composites of morphisms.  This file performs the translation once,
at variable functors, so that a consumer pays only an instantiation.

The translation is the component formula for `CategoryTheory.TwoSquare.vComp`,
`CategoryTheory.TwoSquare.whiskerLeft` and `CategoryTheory.TwoSquare.whiskerRight`, whose
associators contribute identities.

## Main results

* `Stacks.CategoryTheory.cubeFaces_of_app`: the cube hypothesis from its components.
* `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_app`: the invertibility transfer
  `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` with its hypothesis in
  that form, and with the five invertibility side conditions as explicit arguments: at the
  concrete functors of a consumer, instance search does not find them.

## Implementation notes

Doing this at variable functors is not a convenience. At the concrete functors of a sheaf-theoretic
application, both the `simp only` that unfolds the pastings and the kernel check of its result are
out of budget; at variable functors they are immediate, and the instantiation is first-order
matching.

## References

* [nLab, *mate*](https://ncatlab.org/nlab/show/mate)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace Stacks.CategoryTheory

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

/-- **The cube hypothesis of `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`, from its
components.**  For every object of the upper right corner of the front face, the comparison of
the two vertical functors, the mate of the comparison of the two horizontal left adjoints over
the first face, the back 2-cell and the second vertical comparison compose to the front 2-cell
followed by the mate over the second face. -/
theorem cubeFaces_of_app
    (h : ∀ d : D, σG.app (R₁.obj d) ≫ G'.map ((mateEquiv adj₁ adj₁' τ₁).natTrans.app d) ≫
          β'.natTrans.app (ΦD.obj d) ≫ R₂'.map (σH.app d) =
        ΦE.map (β.natTrans.app d) ≫ (mateEquiv adj₂ adj₂' τ₂).natTrans.app (H.obj d)) :
    ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
      β ≫ᵥ mateEquiv adj₂ adj₂' τ₂ := by
  refine TwoSquare.ext _ _ fun d ↦ ?_
  simp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  exact h d

/-- **Invertibility of a mate transports along a change of the four categories of its square**,
with the cube hypothesis read on components.  This is
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` composed with
`Stacks.CategoryTheory.cubeFaces_of_app`. -/
theorem isIso_mateEquiv_symm_of_app (hΦF : ΦF.ReflectsIsomorphisms)
    (hτ₁ : IsIso τ₁.natTrans) (hτ₂ : IsIso τ₂.natTrans) (hσG : IsIso σG) (hσH : IsIso σH)
    (hβ' : IsIso ((mateEquiv adj₁' adj₂').symm β').natTrans)
    (h : ∀ d : D, σG.app (R₁.obj d) ≫ G'.map ((mateEquiv adj₁ adj₁' τ₁).natTrans.app d) ≫
          β'.natTrans.app (ΦD.obj d) ≫ R₂'.map (σH.app d) =
        ΦE.map (β.natTrans.app d) ≫ (mateEquiv adj₂ adj₂' τ₂).natTrans.app (H.obj d)) :
    IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  have := hΦF
  have := hτ₁
  have := hτ₂
  have := hσG
  have := hσH
  have := hβ'
  exact isIso_mateEquiv_symm_of_reflectsIsomorphisms adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β'
    (cubeFaces_of_app adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' h)

end Stacks.CategoryTheory

end
