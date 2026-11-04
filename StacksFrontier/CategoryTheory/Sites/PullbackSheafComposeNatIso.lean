module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFullnessAbelian

/-!
# Pullback of sheaves commutes with change of coefficients, naturally

`CategoryTheory.Functor.sheafPullbackSheafComposeIso` identifies, one sheaf at a time, the pullback
of a sheaf composed with a coefficient functor `G` with the composite with `G` of its pullback.
This identification is natural in the sheaf
(`CategoryTheory.Functor.sheafPullbackSheafComposeHom_naturality`), so it is an isomorphism of
functors, which this file records.

## Main definitions

* `CategoryTheory.Functor.sheafPullbackSheafComposeNatIso` — the comparison as a natural
  isomorphism `sheafCompose J G ⋙ F^* ≅ F^* ⋙ sheafCompose K G`.

## Implementation notes

The naturality of the comparison is the library's
`CategoryTheory.Functor.sheafPullbackSheafComposeHom_naturality`, proved together with the
fullness half of Tag 09YU, clause (2); this file imports it from there.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P]
  {B : Type u₄} [Category.{v₄} B] (G : A ⥤ B)
  [HasWeakSheafify K B] [∀ P : Cᵒᵖ ⥤ B, F.op.HasLeftKanExtension P]
  [J.HasSheafCompose G] [K.HasSheafCompose G]

variable [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension F.op P]
  [∀ Y : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op Y) G]
  [K.PreservesSheafification G]

/-- **Pulling back sheaves along a continuous functor commutes with changing the coefficient
category**, as an isomorphism of functors, along a functor which preserves sheafification and
the colimits computing the presheaf-level left Kan extension. -/
noncomputable def sheafPullbackSheafComposeNatIso :
    sheafCompose J G ⋙ F.sheafPullback B J K ≅ F.sheafPullback A J K ⋙ sheafCompose K G :=
  NatIso.ofComponents (fun S ↦ F.sheafPullbackSheafComposeIso A J K G S)
    (fun f ↦ F.sheafPullbackSheafComposeHom_naturality A J K G f)

end CategoryTheory.Functor
