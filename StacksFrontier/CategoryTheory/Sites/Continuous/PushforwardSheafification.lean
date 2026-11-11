module

public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Sheafification commutes with pushforward along a continuous functor

## Main results

* `PushforwardSheafificationCompatible`: the assertion that restricting a presheaf along `G.op` and
  then sheafifying
  agrees with sheafifying and then pushing forward.
* `nonempty_pushforwardContinuousSheafificationCompatibility`: this natural isomorphism exists.

This is the analogue, for the restriction `u^p` along a functor that is both cocontinuous and
continuous, of Stacks Lemma 00XM (`(u^p G)^# = (u^p (G^#))^#` for cocontinuous `u`); it assumes
continuity in addition, so it is not registered as 00XM. It is not Stacks 00WY, which concerns
the left adjoint `u_p` along a continuous functor: that is
`CategoryTheory.Functor.lanCompPresheafToSheafIsoSheafPullback`.
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

/-- The natural isomorphism asserted by `PushforwardSheafificationCompatible` exists; it is
`Functor.pushforwardContinuousSheafificationCompatibility`. This is a statement about the
restriction `u^p` along a cocontinuous and continuous functor (compare Stacks 00XM, which needs
only cocontinuity), not Stacks 00WY. -/
theorem nonempty_pushforwardContinuousSheafificationCompatibility (C : Type*) [Category C] (D :
  Type*) [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsCocontinuous J K] [G.IsContinuous J K]
    (A : Type*) [Category A]
    [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J A] [HasWeakSheafify K A] :
    PushforwardSheafificationCompatible C D J K G A :=
  ⟨Functor.pushforwardContinuousSheafificationCompatibility G A J K⟩
