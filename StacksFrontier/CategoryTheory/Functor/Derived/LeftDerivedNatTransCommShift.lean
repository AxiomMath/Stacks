module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Shift.CommShift

/-! # The transformation induced on total left derived functors commutes with the shift

Let `α : L ⋙ LF ⟶ F` and `α' : L ⋙ LF' ⟶ F'` exhibit `LF` and `LF'` as the total left derived
functors of `F` and `F'` along a localization `L` at a class `W` of morphisms compatible with the
shift. A transformation `τ : F' ⟶ F` which commutes with the shift induces one of the derived
functors which again commutes with the shift.

## Main results

* `CategoryTheory.Functor.leftDerivedNatTrans_commShift`
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF' LF : D ⥤ H) {F F' : C ⥤ H} {L : C ⥤ D}
  (α' : L ⋙ LF' ⟶ F') (α : L ⋙ LF ⟶ F) (W : MorphismProperty C)
  [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]
  (M : Type*) [AddGroup M] [HasShift C M] [HasShift D M] [HasShift H M]
  [F.CommShift M] [F'.CommShift M] [L.CommShift M] [LF.CommShift M] [LF'.CommShift M]
  [NatTrans.CommShift α M] [NatTrans.CommShift α' M]

/-- **The transformation induced on total left derived functors commutes with the shift.** -/
lemma leftDerivedNatTrans_commShift (τ : F' ⟶ F) [NatTrans.CommShift τ M] :
    NatTrans.CommShift (leftDerivedNatTrans LF' LF α' α W τ) M := by
  refine ⟨fun a ↦ ?_⟩
  have hadj : (shiftFunctor H a).IsRightAdjoint := inferInstance
  refine leftDerived_ext (LF ⋙ shiftFunctor H a)
    ((associator L LF (shiftFunctor H a)).inv ≫ whiskerRight α (shiftFunctor H a)) W
    (shiftFunctor D a ⋙ LF') _ _ ?_
  ext X
  dsimp
  have hc : IsIso ((L.commShiftIso a).hom.app X) := inferInstance
  have h6 : LF'.map ((L.commShiftIso a).hom.app X) ≫
        (leftDerivedNatTrans LF' LF α' α W τ).app ((shiftFunctor D a).obj (L.obj X)) =
      (leftDerivedNatTrans LF' LF α' α W τ).app (L.obj ((shiftFunctor C a).obj X)) ≫
        LF.map ((L.commShiftIso a).hom.app X) :=
    (leftDerivedNatTrans LF' LF α' α W τ).naturality ((L.commShiftIso a).hom.app X)
  have hL : LF'.map ((L.commShiftIso a).hom.app X) ≫
        (LF'.commShiftIso a).hom.app (L.obj X) ≫
          (shiftFunctor H a).map ((leftDerivedNatTrans LF' LF α' α W τ).app (L.obj X)) ≫
            (shiftFunctor H a).map (α.app X) =
      (leftDerivedNatTrans LF' LF α' α W τ).app (L.obj ((shiftFunctor C a).obj X)) ≫
        α.app ((shiftFunctor C a).obj X) ≫ (F.commShiftIso a).hom.app X := by
    rw [← Functor.map_comp (shiftFunctor H a)
        ((leftDerivedNatTrans LF' LF α' α W τ).app (L.obj X)) (α.app X),
      leftDerivedNatTrans_app, Functor.map_comp, ← assoc (LF'.map _),
      ← Functor.commShiftIso_comp_hom_app, NatTrans.shift_app_comm_assoc,
      NatTrans.shift_app_comm, ← assoc, ← leftDerivedNatTrans_app LF' LF α' α W τ, assoc]
  have hR : LF'.map ((L.commShiftIso a).hom.app X) ≫
        (leftDerivedNatTrans LF' LF α' α W τ).app ((shiftFunctor D a).obj (L.obj X)) ≫
          (LF.commShiftIso a).hom.app (L.obj X) ≫ (shiftFunctor H a).map (α.app X) =
      (leftDerivedNatTrans LF' LF α' α W τ).app (L.obj ((shiftFunctor C a).obj X)) ≫
        α.app ((shiftFunctor C a).obj X) ≫ (F.commShiftIso a).hom.app X := by
    rw [← assoc (LF'.map _), h6, assoc, ← assoc (LF.map _),
      ← Functor.commShiftIso_comp_hom_app, NatTrans.shift_app_comm]
  rw [← cancel_epi (LF'.map ((L.commShiftIso a).hom.app X))]
  simp only [id_comp, assoc]
  exact hL.trans hR.symm

end CategoryTheory.Functor

end
