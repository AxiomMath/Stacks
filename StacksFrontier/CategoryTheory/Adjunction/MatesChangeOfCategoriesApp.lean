module

public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
import all StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories

/-!
# The cube identity for mates at one object

`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq` says that, for two squares of adjunctions joined
by functors at the four corners, the mates of two 2-cells which paste to the same 2-cell again
paste to the same 2-cell. This file reads that identity at a single object.

## Main results

* `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app`: the cube identity at one object.
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

/-- **The cube identity at one object.** In the situation of
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`, the two pasted 2-cells agree at every object
`c`: the front mate followed by `ΦF`, preceded by `τ₂`, is the back mate at `ΦC c` corrected by
`σG`, `τ₁` and `σH`. -/
public theorem mateEquiv_symm_hComp_eq_app
    (h : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
      β ≫ᵥ mateEquiv adj₂ adj₂' τ₂) (c : C) :
    τ₂.natTrans.app (G.obj c) ≫ ΦF.map (((mateEquiv adj₁ adj₂).symm β).natTrans.app c) =
      L₂'.map (σG.app c) ≫ ((mateEquiv adj₁' adj₂').symm β').natTrans.app (ΦC.obj c) ≫
        H'.map (τ₁.natTrans.app c) ≫ σH.app (L₁.obj c) := by
  have e := congrArg (fun w => TwoSquare.natTrans w |>.app c)
    (mateEquiv_symm_hComp_eq adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' h)
  simp only [hComp_natTrans_app] at e
  simpa [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, Category.assoc] using e

end Cube

end Stacks.CategoryTheory

end
