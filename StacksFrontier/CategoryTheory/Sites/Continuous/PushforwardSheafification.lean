module

public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Sheafification commutes with pushforward along a continuous functor

## Main results

* `PushforwardSheafificationCompatible`: the assertion that restricting a presheaf along `G.op` and
  then sheafifying
  agrees with sheafifying and then pushing forward.
* `nonempty_pushforwardContinuousSheafificationCompatibility`: this natural isomorphism exists
  (Stacks 00WY).

Tags covered: 00WY.
-/

@[expose] public section

open CategoryTheory

/-- For a continuous and cocontinuous functor `G : C ⥤ D` between sites, the assertion that
restricting a presheaf along `G.op` and then sheafifying is naturally isomorphic to
sheafifying and then applying the sheaf pushforward along `G`. -/
def PushforwardSheafificationCompatible (C : Type*) [Category C] (D : Type*) [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsCocontinuous J K] [G.IsContinuous J K]
    (A : Type*) [Category A]
    [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J A] [HasWeakSheafify K A] : Prop :=
  Nonempty ((Functor.whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
    presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K)

/-- **Stacks 00WY.** The natural isomorphism asserted by `PushforwardSheafificationCompatible`
  exists; it is
`Functor.pushforwardContinuousSheafificationCompatibility`. -/
@[stacks 00WY]
theorem nonempty_pushforwardContinuousSheafificationCompatibility (C : Type*) [Category C] (D :
  Type*) [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsCocontinuous J K] [G.IsContinuous J K]
    (A : Type*) [Category A]
    [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J A] [HasWeakSheafify K A] :
    PushforwardSheafificationCompatible C D J K G A :=
  ⟨Functor.pushforwardContinuousSheafificationCompatibility G A J K⟩
