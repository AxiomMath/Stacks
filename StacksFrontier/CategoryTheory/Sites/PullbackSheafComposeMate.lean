module

public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pullback of sheaves and change of coefficients, as a mate

Let `F : C ⥤ D` be a continuous functor of sites and `G : A ⥤ B` a change of coefficient
category. Pushforward of sheaves commutes with `G` on the nose, and the mate of that identity
under any choice of left adjoints `F^*` of the two pushforwards is a comparison
`F^*(G ∘ S) ⟶ G ∘ F^*(S)`. This file computes it for the explicit left adjoints
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` in terms of
`CategoryTheory.Functor.sheafPullbackSheafComposeHom` (which uses Mathlib's chosen left adjoint),
and deduces that it is an isomorphism when `G` preserves the colimits computing the left Kan
extension and sheafification.

## Main definitions

* `CategoryTheory.Functor.sheafPullbackConstructionSheafComposeMate`: the mate.

## Main results

* `CategoryTheory.Functor.sheafPullbackConstructionSheafComposeMate_app`: its components.
* `CategoryTheory.Functor.isIso_sheafPullbackConstructionSheafComposeMate`: it is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P]
  {B : Type u₄} [Category.{v₄} B] (G : A ⥤ B)
  [HasWeakSheafify K B] [∀ P : Cᵒᵖ ⥤ B, F.op.HasLeftKanExtension P]
  [J.HasSheafCompose G] [K.HasSheafCompose G]

/-- The mate, under the adjunctions `F^* ⊣ F_*` of `sheafPullbackConstruction` with coefficients
in `A` and in `B`, of the identification of `F_*` followed by `G` with `G` followed by `F_*`: the
canonical comparison `F^*(G ∘ S) ⟶ G ∘ F^*(S)`. -/
def sheafPullbackConstructionSheafComposeMate :
    TwoSquare (sheafCompose J G) (sheafPullbackConstruction.sheafPullback F A J K)
      (sheafPullbackConstruction.sheafPullback F B J K) (sheafCompose K G) :=
  (mateEquiv (sheafPullbackConstruction.sheafAdjunctionContinuous F A J K)
    (sheafPullbackConstruction.sheafAdjunctionContinuous F B J K)).symm
      (TwoSquare.mk _ _ _ _ (F.sheafComposeSheafPushforwardIso A J K G).inv)

/-- The comparison of the explicit pullbacks is `sheafPullbackSheafComposeHom` of Mathlib's
chosen pullbacks, read through the identifications of the two left adjoints. -/
theorem sheafPullbackConstructionSheafComposeMate_app (S : Sheaf J A) :
    (sheafPullbackConstructionSheafComposeMate F A J K G).natTrans.app S =
      ((sheafPullbackConstruction.sheafAdjunctionContinuous F B J K).leftAdjointUniq
          (F.sheafAdjunctionContinuous B J K)).hom.app ((sheafCompose J G).obj S) ≫
        F.sheafPullbackSheafComposeHom A J K G S ≫
        (sheafCompose K G).map
          (((sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).leftAdjointUniq
            (F.sheafAdjunctionContinuous A J K)).inv.app S) := by
  set adjA := sheafPullbackConstruction.sheafAdjunctionContinuous F A J K
  set adjB := sheafPullbackConstruction.sheafAdjunctionContinuous F B J K
  set adjcA := F.sheafAdjunctionContinuous A J K
  set adjcB := F.sheafAdjunctionContinuous B J K
  apply (adjB.homEquiv _ _).injective
  have hL : adjB.homEquiv _ _
      ((sheafPullbackConstructionSheafComposeMate F A J K G).natTrans.app S) =
      (sheafCompose J G).map (adjA.unit.app S) ≫
        (F.sheafComposeSheafPushforwardIso A J K G).inv.app
          ((sheafPullbackConstruction.sheafPullback F A J K).obj S) := by
    rw [Adjunction.homEquiv_unit]
    have h := unit_mateEquiv adjA adjB (sheafPullbackConstructionSheafComposeMate F A J K G) S
    rw [sheafPullbackConstructionSheafComposeMate, Equiv.apply_symm_apply] at h
    exact h.symm
  rw [hL, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app, ← Category.assoc,
    unit_comp_pushforward_map_sheafPullbackSheafComposeHom, Category.assoc]
  have hnat := (F.sheafComposeSheafPushforwardIso A J K G).inv.naturality
    ((adjA.leftAdjointUniq adjcA).inv.app S)
  dsimp only [Functor.comp_map] at hnat
  rw [← hnat, ← Category.assoc, ← Functor.map_comp, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.unit_leftAdjointUniq_hom_app]

variable [K.PreservesSheafification G]
  [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension F.op P]
  [∀ Y : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op Y) G]

/-- **Pulling back commutes with a change of coefficients**: the comparison is invertible. -/
instance isIso_sheafPullbackConstructionSheafComposeMate :
    IsIso (sheafPullbackConstructionSheafComposeMate F A J K G).natTrans := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun S => ?_
  rw [sheafPullbackConstructionSheafComposeMate_app]
  infer_instance

end CategoryTheory.Functor
