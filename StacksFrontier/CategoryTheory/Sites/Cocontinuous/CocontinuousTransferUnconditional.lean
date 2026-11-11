module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousTransfer
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-! # The iso `(u^p G)^# ≅ (u^p G^#)^#` for a cocontinuous functor

Let `u : C ⥤ D` be a cocontinuous functor between sites `(C, J)` and `(D, K)`, with values in a
category `A` admitting sheafification on both sides and right Kan extensions along `u.op` (the
situation of Stacks Lemma 00XL). For any presheaf `G : Dᵒᵖ ⥤ A` there is a canonical isomorphism
`(u^p G)^# ≅ (u^p (G^#))^#` of sheaves on `(C, J)`.

In Mathlib notation:
* `u^p G` is `u.op ⋙ G`, the precomposition of presheaves;
* `(-)^#` is sheafification, witnessed by `presheafToSheaf _ _`;
* `G^#` (as a presheaf) is `(sheafToPresheaf K A).obj ((presheafToSheaf K A).obj G)`;
* the canonical morphism between the two presheaves is
  `Functor.whiskerLeft u.op (toSheafify K G)`.

As in the Stacks proof, both functors `G ↦ (u^p G)^#` and `G ↦ (u^p (G^#))^#` from presheaves
on `D` to sheaves on `C` are left adjoint to `G' ↦ {}_p u G'` (the first by composing the
adjunctions `u^p ⊣ {}_p u` and sheafification, the second by composing sheafification on `D` with
the adjunction of Stacks 00XL, `Functor.sheafAdjunctionPullbackCocontinuous`), so they agree by
uniqueness of adjoints (the Yoneda lemma). Consequently `(-)^# ∘ u^p` sends every morphism whose
sheafification is an isomorphism to a morphism whose sheafification is an isomorphism; applied to
the unit `G ⟶ G^#` this shows the canonical morphism `(u^p G)^# ⟶ (u^p (G^#))^#` is an iso.

## Main results

* `CategoryTheory.Functor.sheafifyRestrictionIsoSheafPullbackCocontinuous`: the natural
  isomorphism `(u^p G)^# ≅ (u^p (G^#))^#` of functors `PSh(D) ⥤ Sh(C)`.
* `CategoryTheory.Functor.isIso_presheafToSheaf_map_whiskerLeft`: if `α` becomes an iso after
  sheafification on `D`, then `u^p α` becomes an iso after sheafification on `C`.
* `CategoryTheory.Functor.isStacks00XLTransfer_of_isCocontinuous`: the same, as
  `IsStacks00XLTransfer`.
* `CategoryTheory.Functor.sheafifyRestrictionIsoOfIsCocontinuous`: the canonical
  isomorphism `(u^p G)^# ≅ (u^p G^#)^#` (Stacks 00XM).

This proves the transfer property `IsStacks00XLTransfer` that the conditional
`sheafifyRestrictionIsoSheafifyRestrictionSheafify` takes as a hypothesis.

Tags covered: 00XM.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ w w' u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
variable (A : Type w) [Category.{w'} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsCocontinuous J K] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]

/-- For a cocontinuous `u`, the functors `G ↦ (u^p G)^#` and `G ↦ (u^p (G^#))^#` from presheaves
on `D` to sheaves on `C` are naturally isomorphic: both are left adjoint to
`G' ↦ {}_p u G'` (restricted to sheaves), the second through the adjunction of Stacks 00XL. -/
noncomputable def sheafifyRestrictionIsoSheafPullbackCocontinuous :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ⋙ presheafToSheaf J A ≅
      presheafToSheaf K A ⋙ u.sheafPullbackCocontinuous A J K :=
  Adjunction.leftAdjointUniq
    (((u.op.ranAdjunction A).comp (sheafificationAdjunction J A)).ofNatIsoRight
      (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm)
    ((sheafificationAdjunction K A).comp (u.sheafAdjunctionPullbackCocontinuous A J K))

/-- For a cocontinuous `u`, if a morphism `α : F ⟶ F'` of presheaves on `D` becomes an iso after
sheafification, then so does its restriction `u^p α = whiskerLeft u.op α` on `C`. -/
theorem isIso_presheafToSheaf_map_whiskerLeft {F F' : Dᵒᵖ ⥤ A} (α : F ⟶ F')
    [IsIso ((presheafToSheaf K A).map α)] :
    IsIso ((presheafToSheaf J A).map (Functor.whiskerLeft u.op α)) := by
  have : IsIso (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ⋙ presheafToSheaf J A).map α) := by
    rw [NatIso.isIso_map_iff (u.sheafifyRestrictionIsoSheafPullbackCocontinuous A J K)]
    dsimp only [Functor.comp_map]
    infer_instance
  exact this

/-- For a cocontinuous `u`, the transfer property `IsStacks00XLTransfer` holds. -/
theorem isStacks00XLTransfer_of_isCocontinuous : IsStacks00XLTransfer J K u A :=
  fun α _ ↦ u.isIso_presheafToSheaf_map_whiskerLeft A J K α

/-- **Stacks 00XM.** For a cocontinuous functor `u : C ⥤ D` between sites and any presheaf `G`
on `D`, `(u^p G)^# = (u^p (G^#))^#`: the sheafification of the restricted unit
`whiskerLeft u.op (toSheafify K G) : u^p G ⟶ u^p (G^#)` is an isomorphism of sheaves on `C`. -/
@[stacks 00XM]
noncomputable def sheafifyRestrictionIsoOfIsCocontinuous (G : Dᵒᵖ ⥤ A) :
    (presheafToSheaf J A).obj (u.op ⋙ G) ≅
      (presheafToSheaf J A).obj
        (u.op ⋙ (sheafToPresheaf K A).obj ((presheafToSheaf K A).obj G)) := by
  -- On `D`, sheafification sends the unit `toSheafify K G` to an iso, because its right adjoint
  -- `sheafToPresheaf K A` is fully faithful.
  haveI : (sheafToPresheaf K A).Full := (fullyFaithfulSheafToPresheaf K A).full
  haveI : (sheafToPresheaf K A).Faithful := (fullyFaithfulSheafToPresheaf K A).faithful
  haveI : IsIso ((presheafToSheaf K A).map ((sheafificationAdjunction K A).unit.app G)) :=
    inferInstance
  haveI : IsIso ((presheafToSheaf K A).map (toSheafify K G)) := by assumption
  haveI := u.isIso_presheafToSheaf_map_whiskerLeft A J K (toSheafify K G)
  exact asIso ((presheafToSheaf J A).map (Functor.whiskerLeft u.op (toSheafify K G)))

end CategoryTheory.Functor
