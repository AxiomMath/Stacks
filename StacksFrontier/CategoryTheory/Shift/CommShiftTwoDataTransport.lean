module

public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp
public import StacksFrontier.CategoryTheory.Shift.CommShiftCompOfEqData

/-!
# Transporting `NatTrans.CommShift` along equalities of the commutation data

`CategoryTheory.NatTrans.CommShift τ M` takes the `CategoryTheory.Functor.CommShift` structures
of the source and the target of `τ` as instance arguments. This file shows that it transports
along equalities of these structures, and records the one-variable commutation data of the
closure instances `postcomp`, `precomp₁` and `precomp₂` of `CategoryTheory.Functor.CommShift₂`.

## Main results

* `CategoryTheory.NatTrans.commShift_of_eq_data`: a `NatTrans.CommShift` transports along
  equalities of the two commutation data.
* `CategoryTheory.Functor.CommShift₂.postcomp_commShiftObj`,
  `postcomp_commShiftFlipObj`, `precomp₁_commShiftObj`, `precomp₁_commShiftFlipObj`,
  `precomp₂_commShiftObj`, `precomp₂_commShiftFlipObj`: the one-variable commutation data of the
  three closure instances.
-/

@[expose] public section

namespace CategoryTheory

namespace NatTrans

/-- `CategoryTheory.NatTrans.CommShift` transports along equalities of the source and target
commutation data. -/
theorem commShift_of_eq_data {C D : Type*} [Category* C] [Category* D]
    {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] {F G : C ⥤ D}
    {dF dF' : F.CommShift M} {dG dG' : G.CommShift M} (hF : dF = dF') (hG : dG = dG')
    (τ : F ⟶ G) (h : @NatTrans.CommShift _ _ _ _ F G τ M _ _ _ dF dG) :
    @NatTrans.CommShift _ _ _ _ F G τ M _ _ _ dF' dG' := by
  subst hF hG
  exact h

end NatTrans

namespace Functor.CommShift₂

variable {C₁ C₁' C₂ C₂' D D' : Type*} [Category* C₁] [Category* C₁'] [Category* C₂]
  [Category* C₂'] [Category* D] [Category* D']
  {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₁' M] [HasShift C₂ M]
  [HasShift C₂' M] [HasShift D M] [HasShift D' M]

section Postcomp

variable (G : C₁ ⥤ C₂ ⥤ D) (H : D ⥤ D') [H.CommShift M]
  (h : CommShift₂Setup D M) (h' : CommShift₂Setup D' M) [G.CommShift₂ h]
  (hε : ∀ (m n : M) (Z : D), H.map ((h.ε m n).val.app Z) = (h'.ε m n).val.app (H.obj Z))

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.postcomp` puts on
`(G ⋙ H).obj X₁` is `CategoryTheory.Functor.CommShift.comp` of the datum on `G.obj X₁` and the
datum on `H`. -/
theorem postcomp_commShiftObj (X₁ : C₁) :
    commShiftObj (self := postcomp G H h h' hε) h' X₁ = CommShift.comp (G.obj X₁) H :=
  rfl

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.postcomp` puts on
`(G ⋙ H).flip.obj X₂` is `CategoryTheory.Functor.CommShift.comp` of the datum on `G.flip.obj X₂`
and the datum on `H`. -/
theorem postcomp_commShiftFlipObj (X₂ : C₂) :
    commShiftFlipObj (self := postcomp G H h h' hε) h' X₂ =
      CommShift.comp (G.flip.obj X₂) H :=
  rfl

end Postcomp

section Precomp₁

variable (F : C₁' ⥤ C₁) [F.CommShift M] (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M)
  [G.CommShift₂ h]

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.precomp₁` puts on
`(F ⋙ G).obj X₁'` is the ambient datum on `G.obj (F.obj X₁')`. -/
theorem precomp₁_commShiftObj (X₁' : C₁') :
    commShiftObj (self := precomp₁ F G h) h X₁' = commShiftObj h (F.obj X₁') :=
  rfl

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.precomp₁` puts on
`(F ⋙ G).flip.obj X₂` is `CategoryTheory.Functor.CommShift.comp` of the datum on `F` and the
datum on `G.flip.obj X₂`. -/
theorem precomp₁_commShiftFlipObj (X₂ : C₂) :
    commShiftFlipObj (self := precomp₁ F G h) h X₂ = CommShift.comp F (G.flip.obj X₂) :=
  rfl

end Precomp₁

section Precomp₂

variable (F : C₂' ⥤ C₂) [F.CommShift M] (G : C₁ ⥤ C₂ ⥤ D) (h : CommShift₂Setup D M)
  [G.CommShift₂ h]

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.precomp₂` puts on
`(G ⋙ (whiskeringLeft _ _ _).obj F).obj X₁` is `CategoryTheory.Functor.CommShift.comp` of the
datum on `F` and the datum on `G.obj X₁`. -/
theorem precomp₂_commShiftObj (X₁ : C₁) :
    commShiftObj (self := precomp₂ F G h) h X₁ = CommShift.comp F (G.obj X₁) :=
  rfl

/-- The commutation datum that `CategoryTheory.Functor.CommShift₂.precomp₂` puts on
`(G ⋙ (whiskeringLeft _ _ _).obj F).flip.obj X₂'` is the ambient datum on
`G.flip.obj (F.obj X₂')`. -/
theorem precomp₂_commShiftFlipObj (X₂' : C₂') :
    commShiftFlipObj (self := precomp₂ F G h) h X₂' = commShiftFlipObj h (F.obj X₂') :=
  rfl

end Precomp₂

end Functor.CommShift₂

end CategoryTheory

end
