module

public import StacksFrontier.CategoryTheory.Localization.InducedNatTrans

/-!
# Changing the source factorization of an induced natural transformation

Let `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` be functors, and let `γ : X' ⟶ Y'` be a natural
transformation of functors `D₁ ⥤ D₂` which is induced by `γ₀ : X₀ ⟶ Y₀` along factorizations
`L₁ ⋙ X' ≅ X₀ ⋙ L₂` and `L₁ ⋙ Y' ≅ Y₀ ⋙ L₂`. Given an isomorphism `ε : X₀ ≅ X₀'`, the
transformation `γ` is induced by `ε⁻¹ ≫ γ₀` along the factorization of `X'` through `X₀'`
obtained by composing with `ε`.

## Main results

* `CategoryTheory.NatTrans.IsInducedBy.trans_isoWhiskerRight_left`: changing the factorization
  of the source along an isomorphism of the functors upstairs.
-/

public section

namespace CategoryTheory

namespace NatTrans.IsInducedBy

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] {D₁ : Type*} [Category* D₁]
  {D₂ : Type*} [Category* D₂] {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {X' Y' : D₁ ⥤ D₂}
  {X₀ X₀' Y₀ : C₁ ⥤ C₂}

/-- If `γ` is induced by `γ₀` along `ΦX` and `ΦY`, then for an isomorphism `ε : X₀ ≅ X₀'` it is
induced by `ε.inv ≫ γ₀` along `ΦX ≪≫ Functor.isoWhiskerRight ε L₂` and `ΦY`. -/
theorem trans_isoWhiskerRight_left {ΦX : L₁ ⋙ X' ≅ X₀ ⋙ L₂} {ΦY : L₁ ⋙ Y' ≅ Y₀ ⋙ L₂}
    {γ : X' ⟶ Y'} {γ₀ : X₀ ⟶ Y₀} (h : IsInducedBy ΦX ΦY γ γ₀) (ε : X₀ ≅ X₀') :
    IsInducedBy (ΦX ≪≫ Functor.isoWhiskerRight ε L₂) ΦY γ (ε.inv ≫ γ₀) := fun c => by
  simp [h c, ← L₂.map_comp_assoc]

end NatTrans.IsInducedBy

end CategoryTheory

end
