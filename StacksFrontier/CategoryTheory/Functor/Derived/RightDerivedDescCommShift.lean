module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# The morphism out of a right derived functor commutes with the shift

Let `RF : H ⥤ D` be a right derived functor of `F : C ⥤ D` along a localization `L : C ⥤ H`,
with unit `α : F ⟶ L ⋙ RF`, everything commuting with shifts by an additive group `A` and `RF`
carrying the shift-commutation of `CategoryTheory.Functor.IsRightDerivedFunctor.commShift`. For
a functor `G : H ⥤ D` commuting with the shift and a natural transformation `β : F ⟶ L ⋙ G`
compatible with the shift, the morphism `RF ⟶ G` induced by the universal property,
`CategoryTheory.Functor.rightDerivedDesc`, is compatible with the shift.

## Main results

* `CategoryTheory.Functor.IsRightDerivedFunctor.rightDerivedDesc_commShift`: the morphism
  `RF.rightDerivedDesc α W G β` commutes with the shift.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

namespace IsRightDerivedFunctor

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (RF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : F ⟶ L ⋙ RF) (W : MorphismProperty C) [L.IsLocalization W]
  [RF.IsRightDerivedFunctor α W]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
  [W.IsCompatibleWithShift A] [F.CommShift A] [L.CommShift A]
  (G : H ⥤ D) [G.CommShift A] (β : F ⟶ L ⋙ G) [NatTrans.CommShift β A]

/-- **The morphism out of a right derived functor induced by a shift-compatible transformation
is shift-compatible**, for the shift-commutation of the right derived functor deduced from its
unit. -/
theorem rightDerivedDesc_commShift :
    letI := commShift RF α W A
    NatTrans.CommShift (RF.rightDerivedDesc α W G β) A := by
  let := commShift RF α W A
  refine ⟨fun a => ?_⟩
  refine Functor.rightDerived_ext (RF := shiftFunctor H a ⋙ RF)
    (α := precomposeShiftNatTrans RF α a) (W := W) _ _ _ ?_
  ext X
  have h₁ := comp_map_commShiftIso_hom_app RF α W (A := A) a X
  have h₂ := NatTrans.shift_app_comm β a X
  have hfac := Functor.rightDerived_fac_app RF α W G β X
  have hfac' := Functor.rightDerived_fac_app RF α W G β (X⟦a⟧)
  have hnat := (RF.rightDerivedDesc α W G β).naturality ((L.commShiftIso a).hom.app X)
  simp only [Functor.commShiftIso_comp_hom_app] at h₂
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, precomposeShiftNatTrans_app,
    Functor.comp_obj, Functor.whiskerRight_app, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp, hfac, reassoc_of% hnat, reassoc_of% hfac', ← h₂]

end IsRightDerivedFunctor

end Functor

end CategoryTheory
