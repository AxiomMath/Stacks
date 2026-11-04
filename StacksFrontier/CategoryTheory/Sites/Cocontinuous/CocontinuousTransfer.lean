module

public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # The iso `(u^p G)^# ≅ (u^p G^#)^#` for a cocontinuous functor

In the situation of Stacks Lemma 00XL — a cocontinuous functor `u : C ⥤ D` between sites
`(C, J)` and `(D, K)`, with values in a category `A` admitting sheafification on both sides —
for any presheaf `G : Dᵒᵖ ⥤ A` there is a canonical isomorphism `(u^p G)^# ≅ (u^p (G^#))^#`
between sheafifications on the `(C, J)`-side.

In Mathlib notation:
* `u^p G` is `u.op ⋙ G`, the precomposition of presheaves;
* `(-)^#` is sheafification, witnessed by `presheafToSheaf _ _`;
* `G^#` (as a presheaf) is `(sheafToPresheaf K A).obj ((presheafToSheaf K A).obj G)`;
* the canonical morphism between the two presheaves is
  `Functor.whiskerLeft u.op (toSheafify K G)`.

The Stacks proof goes through the adjunction `(u^p (-))^# ⊣ _s u` of Lemma 00XL together with
the Yoneda lemma. Mathlib delivers the `(D, K)`-side fact for free: the right adjoint
`sheafToPresheaf K A` is fully faithful, so the left adjoint `presheafToSheaf K A` sends the
unit `toSheafify K G` to an isomorphism in `Sheaf K A`. The remaining content — transferring
this iso along the cocontinuous pullback to the `(C, J)`-side — is the statement of Stacks 00XL
specialised to `α := toSheafify K G`, taken here as the hypothesis
`IsStacks00XLTransfer`.

## Main results

* `IsStacks00XLTransfer`: the transfer property supplied by Stacks 00XL.
* `sheafifyRestrictionIsoSheafifyRestrictionSheafify`: the canonical isomorphism `(u^p G)^# ≅ (u^p
  G^#)^#` (Stacks 00XM).

Tags covered: 00XM.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v u₁ u₂ u

/-- The **Stacks 00XL transfer property** specialised to a single
morphism: for the cocontinuous functor `u : C ⥤ D` and the morphism
`α : F ⟶ F'` of presheaves on `D`, if `(presheafToSheaf K A).map α`
is an iso in `Sheaf K A`, then
`(presheafToSheaf J A).map (whiskerLeft u.op α)` is an iso in
`Sheaf J A`. This is the substantive content of Stacks 00XL
("cocontinuous pullback transports iso-after-sheafification") that
the Stacks proof of 00XM invokes via the adjunction. -/
def IsStacks00XLTransfer
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D)
    (A : Type u) [Category.{v} A]
    [HasWeakSheafify J A] [HasWeakSheafify K A] : Prop :=
  ∀ {F F' : Dᵒᵖ ⥤ A} (α : F ⟶ F'),
    IsIso ((presheafToSheaf K A).map α) →
    IsIso ((presheafToSheaf J A).map (Functor.whiskerLeft u.op α))

/-- **Stacks 00XM (canonical iso form).** In the situation of Stacks
Lemma 00XL — i.e. assuming the 00XL transfer property `h00XL` — for
any presheaf `G` on `D` we have a canonical isomorphism
`(u^p G)^# ≅ (u^p G^#)^#` of sheaves on `(C, J)`, namely the
sheafification of the whiskered unit `whiskerLeft u.op (toSheafify K G)`. -/
@[stacks 00XM]
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
