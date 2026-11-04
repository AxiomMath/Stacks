module

public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose

/-!
# Supplement to `StacksFrontier/CategoryTheory/Sites/PullbackSheafCompose`

Declarations used by the pro-étale comparison of Stacks 09B1 and 09A6, kept in their own module
so that `StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose` is unchanged.
-/

@[expose] public section
open CategoryTheory.Limits

namespace CategoryTheory.Functor
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P]

section
variable {B : Type u₄} [Category.{v₄} B] (G : A ⥤ B)
  [HasWeakSheafify K B] [∀ P : Cᵒᵖ ⥤ B, F.op.HasLeftKanExtension P]
  [J.HasSheafCompose G] [K.HasSheafCompose G]
variable (S : Sheaf J A)
variable [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension F.op P]
  [∀ Y : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op Y) G]
variable [K.PreservesSheafification G]

omit [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension F.op P]
  [∀ Y : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op Y) G]
  [K.PreservesSheafification G] in
/-- The counit of the pullback/pushforward adjunction for the coefficient category `B`, at
`G ∘ T`, is the comparison isomorphism followed by `G` applied to the counit for `A` at `T`. -/
lemma sheafAdjunctionContinuous_counit_app_sheafCompose (T : Sheaf K A) :
    (F.sheafAdjunctionContinuous B J K).counit.app ((sheafCompose K G).obj T) =
      F.sheafPullbackSheafComposeHom A J K G ((F.sheafPushforwardContinuous A J K).obj T) ≫
        (sheafCompose K G).map ((F.sheafAdjunctionContinuous A J K).counit.app T) := by
  have h := F.sheafPullbackSheafComposeHom_comp_sheafCompose_map A J K G
    ((F.sheafPushforwardContinuous A J K).obj T) T (𝟙 _)
  simp only [Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp] at h
  rw [h]
  simp only [sheafComposeSheafPushforwardIso, Iso.refl_inv, NatTrans.id_app]
  exact (Category.id_comp _).symm.trans (by rw [← Functor.map_id]; rfl)

/-- The counit of the pullback/pushforward adjunction is invertible at `T` if and only if it is
invertible at `G ∘ T` for the coefficient category `B`, provided changing coefficients along `G`
reflects isomorphisms of sheaves. -/
lemma isIso_sheafAdjunctionContinuous_counit_app_iff_sheafCompose
    [(sheafCompose K G).ReflectsIsomorphisms] (T : Sheaf K A) :
    IsIso ((F.sheafAdjunctionContinuous A J K).counit.app T) ↔
      IsIso ((F.sheafAdjunctionContinuous B J K).counit.app ((sheafCompose K G).obj T)) := by
  have hκ : IsIso (F.sheafPullbackSheafComposeHom A J K G
      ((F.sheafPushforwardContinuous A J K).obj T)) :=
    F.isIso_sheafPullbackSheafComposeHom A J K G _
  rw [F.sheafAdjunctionContinuous_counit_app_sheafCompose A J K G T]
  refine ⟨fun _ => @IsIso.comp_isIso _ _ _ _ _ _ _ hκ inferInstance, fun h => ?_⟩
  have : IsIso ((sheafCompose K G).map ((F.sheafAdjunctionContinuous A J K).counit.app T)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hκ h
  exact isIso_of_reflects_iso _ (sheafCompose K G)

/-- The unit of the pullback/pushforward adjunction is invertible at a sheaf `S` as soon as it is
invertible at `G ∘ S` for the coefficient category `B`, provided changing coefficients along `G`
reflects isomorphisms of sheaves: changing coefficients carries the one unit to the other, up to
the comparison isomorphism. -/
lemma isIso_sheafAdjunctionContinuous_unit_app_of_sheafCompose
    [(sheafCompose J G).ReflectsIsomorphisms]
    (h : IsIso ((F.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J G).obj S))) :
    IsIso ((F.sheafAdjunctionContinuous A J K).unit.app S) := by
  have : IsIso ((sheafCompose J G).map ((F.sheafAdjunctionContinuous A J K).unit.app S) ≫
      (F.sheafComposeSheafPushforwardIso A J K G).inv.app ((F.sheafPullback A J K).obj S)) := by
    rw [← F.unit_comp_pushforward_map_sheafPullbackSheafComposeHom A J K G S]
    infer_instance
  have : IsIso ((sheafCompose J G).map ((F.sheafAdjunctionContinuous A J K).unit.app S)) :=
    IsIso.of_isIso_comp_right _
      ((F.sheafComposeSheafPushforwardIso A J K G).inv.app ((F.sheafPullback A J K).obj S))
  exact isIso_of_reflects_iso _ (sheafCompose J G)

end
end CategoryTheory.Functor
end
