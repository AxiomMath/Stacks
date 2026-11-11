module

public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # The iso `(u^p G)^# ≅ (u^p G^#)^#` from a transfer property

For a functor `u : C ⥤ D` between sites `(C, J)` and `(D, K)`, with values in a category `A`
admitting sheafification on both sides, this file packages the (one-line) implication from the
transfer property `IsStacks00XLTransfer` (whiskering by `u.op` carries morphisms that become isos
after sheafification on `D` to morphisms that become isos after sheafification on `C`) to the
canonical isomorphism `(u^p G)^# ≅ (u^p (G^#))^#` between sheafifications on the `(C, J)`-side.

This is not Stacks 00XM itself: here `u` is an arbitrary functor and the transfer property, which
contains the conclusion, is a hypothesis. Stacks 00XM, for a cocontinuous `u`, is
`CategoryTheory.Functor.sheafifyRestrictionIsoOfIsCocontinuous` in
`StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousTransferUnconditional`, which also
proves the transfer property for cocontinuous `u`
(`CategoryTheory.Functor.isStacks00XLTransfer_of_isCocontinuous`).

In Mathlib notation:
* `u^p G` is `u.op ⋙ G`, the precomposition of presheaves;
* `(-)^#` is sheafification, witnessed by `presheafToSheaf _ _`;
* `G^#` (as a presheaf) is `(sheafToPresheaf K A).obj ((presheafToSheaf K A).obj G)`;
* the canonical morphism between the two presheaves is
  `Functor.whiskerLeft u.op (toSheafify K G)`.

## Main results

* `IsStacks00XLTransfer`: the transfer property.
* `sheafifyRestrictionIsoSheafifyRestrictionSheafify`: the canonical isomorphism `(u^p G)^# ≅ (u^p
  G^#)^#`, given the transfer property.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v u₁ u₂ u

/-- The transfer property for a functor `u : C ⥤ D`: for every morphism `α : F ⟶ F'` of
presheaves on `D`, if `(presheafToSheaf K A).map α` is an iso in `Sheaf K A`, then
`(presheafToSheaf J A).map (whiskerLeft u.op α)` is an iso in `Sheaf J A`. It holds for
cocontinuous `u` (`CategoryTheory.Functor.isStacks00XLTransfer_of_isCocontinuous`, from the
adjunction of Stacks 00XL); for an arbitrary `u` it is an assumption. -/
def IsStacks00XLTransfer
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D)
    (A : Type u) [Category.{v} A]
    [HasWeakSheafify J A] [HasWeakSheafify K A] : Prop :=
  ∀ {F F' : Dᵒᵖ ⥤ A} (α : F ⟶ F'),
    IsIso ((presheafToSheaf K A).map α) →
    IsIso ((presheafToSheaf J A).map (Functor.whiskerLeft u.op α))

/-- Given the transfer property `h00XL`, for any presheaf `G` on `D` we have a canonical
isomorphism `(u^p G)^# ≅ (u^p G^#)^#` of sheaves on `(C, J)`, namely the
sheafification of the whiskered unit `whiskerLeft u.op (toSheafify K G)`.
The transfer property is proved for cocontinuous `u` in
`CategoryTheory.Functor.isIso_presheafToSheaf_map_whiskerLeft`, and the unconditional
iso (Stacks 00XM) is `CategoryTheory.Functor.sheafifyRestrictionIsoOfIsCocontinuous`. -/
noncomputable def sheafifyRestrictionIsoSheafifyRestrictionSheafify
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D)
    (A : Type u) [Category.{v} A]
    [HasWeakSheafify J A] [HasWeakSheafify K A]
    (h00XL : IsStacks00XLTransfer J K u A)
    (G : Dᵒᵖ ⥤ A) :
    (presheafToSheaf J A).obj (u.op ⋙ G) ≅
      (presheafToSheaf J A).obj
        (u.op ⋙ (sheafToPresheaf K A).obj ((presheafToSheaf K A).obj G)) := by
  -- On the `(D, K)`-side, `presheafToSheaf K A` sends the unit `toSheafify K G` to an iso,
  -- because its right adjoint `sheafToPresheaf K A` is fully faithful.
  haveI : (sheafToPresheaf K A).Full :=
    (fullyFaithfulSheafToPresheaf K A).full
  haveI : (sheafToPresheaf K A).Faithful :=
    (fullyFaithfulSheafToPresheaf K A).faithful
  haveI hKunit : IsIso ((presheafToSheaf K A).map
      ((sheafificationAdjunction K A).unit.app G)) :=
    inferInstance
  haveI hK : IsIso ((presheafToSheaf K A).map (toSheafify K G)) := by
    have h : (sheafificationAdjunction K A).unit.app G = toSheafify K G := rfl
    rw [← h]; exact hKunit
  -- 00XL transfers this iso to the `(C, J)`-side along `whiskerLeft u.op`.
  haveI hJ : IsIso ((presheafToSheaf J A).map
      (Functor.whiskerLeft u.op (toSheafify K G))) :=
    h00XL (toSheafify K G) hK
  exact @asIso _ _ _ _ _ hJ
