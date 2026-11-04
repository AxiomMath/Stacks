module

public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality

/-!
# The composition comparison of inverse images on sheafified representables

Let `F : C ⥤ D`, `G : D ⥤ E` and `FG : C ⥤ E` be continuous functors of sites with an isomorphism
`e : F ⋙ G ≅ FG`, all of whose sheaf pushforwards have left adjoints. The inverse images then
compose up to the canonical isomorphism `CategoryTheory.Functor.sheafPullbackComp' e`, the
conjugate of the composition of the pushforwards. Each inverse image also carries a sheafified
representable `h_U^#` to the sheafified representable of the image object, by
`CategoryTheory.Sheaf.sheafPullbackSheafifiedYonedaIso`.

This file proves that the two families of comparisons are compatible: on `h_U^#`, the
composition comparison is the composite of the two representable comparisons followed by the
representable of `e` at `U`. This is what identifies the composition comparison of inverse images
on representable sheaves with the composition comparison of the underlying functors of sites,
the form a descent argument along a limit of schemes needs.

## Main results

* `CategoryTheory.Sheaf.sheafPullbackComp'_hom_app_sheafifiedYoneda` — the compatibility.

## Implementation notes

Both sides are maps out of `G_s(F_s(h_U^#))`, which corepresents sections over `G(F(U))`. The
proof evaluates both on that corepresentability bijection: the composition comparison is a
conjugate, so `CategoryTheory.Adjunction.unit_conjugateEquiv_symm` computes it on the unit, and
the representable comparisons are characterized by
`CategoryTheory.Sheaf.sheafPullbackSheafifiedYonedaIso_hom_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u₁

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v} C] {D : Type u₁} [Category.{v} D]
  {E : Type u₁} [Category.{v} E]
  {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]
  [HasWeakSheafify J (Type max u₁ v)] [HasWeakSheafify K (Type max u₁ v)]
  [HasWeakSheafify L (Type max u₁ v)]
  [(F.sheafPushforwardContinuous (Type max u₁ v) J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous (Type max u₁ v) K L).IsRightAdjoint]
  [(FG.sheafPushforwardContinuous (Type max u₁ v) J L).IsRightAdjoint]

/-- **The composition comparison of inverse images on a sheafified representable.** For
`e : F ⋙ G ≅ FG`, the component at `h_U^#` of the comparison
`G_s ∘ F_s ≅ FG_s` is `G_s(h_U^# ≅ ...) : G_s(F_s(h_U^#)) ≅ G_s(h_{F(U)}^#) ≅ h_{G(F(U))}^#`
followed by the representable of `e_U : G(F(U)) ⟶ FG(U)` and the inverse of the comparison
`FG_s(h_U^#) ≅ h_{FG(U)}^#`. -/
public theorem sheafPullbackComp'_hom_app_sheafifiedYoneda (U : C) :
    (Functor.sheafPullbackComp' eFG (Type max u₁ v) J K L).hom.app
        ((presheafToSheaf J (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj U)) =
      (G.sheafPullback (Type max u₁ v) K L).map (sheafPullbackSheafifiedYonedaIso F J K U).hom ≫
        (sheafPullbackSheafifiedYonedaIso G K L (F.obj U)).hom ≫
        (presheafToSheaf L (Type max u₁ v)).map (uliftYoneda.{u₁}.map (eFG.hom.app U)) ≫
        (sheafPullbackSheafifiedYonedaIso FG J L U).inv := by
  set hU := (presheafToSheaf J (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj U)
  set T := (FG.sheafPullback (Type max u₁ v) J L).obj hU
  set adjF := F.sheafAdjunctionContinuous (Type max u₁ v) J K
  set adjG := G.sheafAdjunctionContinuous (Type max u₁ v) K L
  set adjFG := FG.sheafAdjunctionContinuous (Type max u₁ v) J L
  -- the corepresentability bijection for the composite inverse image
  let Φ : ((G.sheafPullback (Type max u₁ v) K L).obj
      ((F.sheafPullback (Type max u₁ v) J K).obj hU) ⟶ T) ≃ T.obj.obj (op (G.obj (F.obj U))) :=
    (adjG.homEquiv _ _).trans
      ((pullbackSheafifiedYonedaEquiv F J K U _).trans (pushforwardSectionsEquiv F J K _ U))
  apply Φ.injective
  -- the common value: the canonical section of `T`, reindexed along `e_U`
  have hcan : pullbackSheafifiedYonedaEquiv FG J L U T (𝟙 T) =
      uliftYonedaEquiv.{u₁} (((sheafificationAdjunction J (Type max u₁ v)).homEquiv _ _)
        (adjFG.unit.app hU)) := by
    simp only [pullbackSheafifiedYonedaEquiv, Equiv.trans_apply]
    rfl
  -- the left-hand side
  have hL : Φ ((Functor.sheafPullbackComp' eFG (Type max u₁ v) J K L).hom.app hU) =
      T.obj.map (eFG.hom.app U).op (pullbackSheafifiedYonedaEquiv FG J L U T (𝟙 T)) := by
    have hconj := unit_conjugateEquiv_symm adjFG (adjF.comp adjG)
      (Functor.sheafPushforwardContinuousComp' eFG (Type max u₁ v) J K L).inv hU
    have hhom : (Functor.sheafPullbackComp' eFG (Type max u₁ v) J K L).hom =
        ((conjugateEquiv adjFG (adjF.comp adjG)).symm
          (Functor.sheafPushforwardContinuousComp' eFG (Type max u₁ v) J K L).inv) := rfl
    rw [← hhom] at hconj
    have hcomp : (adjF.comp adjG).homEquiv _ _
        ((Functor.sheafPullbackComp' eFG (Type max u₁ v) J K L).hom.app hU) =
        adjFG.unit.app hU ≫
          (Functor.sheafPushforwardContinuousComp' eFG (Type max u₁ v) J K L).inv.app T := by
      rw [Adjunction.homEquiv_unit, ← hconj]
    rw [hcan]
    simp only [Φ, Equiv.trans_apply]
    show uliftYonedaEquiv.{u₁} (((sheafificationAdjunction J (Type max u₁ v)).homEquiv _ _)
      (((adjF.comp adjG).homEquiv _ _)
        ((Functor.sheafPullbackComp' eFG (Type max u₁ v) J K L).hom.app hU))) = _
    rw [hcomp, Adjunction.homEquiv_naturality_right, uliftYonedaEquiv_comp]
    rfl
  -- the right-hand side
  have hR : Φ ((G.sheafPullback (Type max u₁ v) K L).map
        (sheafPullbackSheafifiedYonedaIso F J K U).hom ≫
        (sheafPullbackSheafifiedYonedaIso G K L (F.obj U)).hom ≫
        (presheafToSheaf L (Type max u₁ v)).map (uliftYoneda.{u₁}.map (eFG.hom.app U)) ≫
        (sheafPullbackSheafifiedYonedaIso FG J L U).inv) =
      T.obj.map (eFG.hom.app U).op (pullbackSheafifiedYonedaEquiv FG J L U T (𝟙 T)) := by
    show pushforwardSectionsEquiv F J K _ U (pullbackSheafifiedYonedaEquiv F J K U _
      (adjG.homEquiv _ _ ((G.sheafPullback (Type max u₁ v) K L).map
        (sheafPullbackSheafifiedYonedaIso F J K U).hom ≫
        (sheafPullbackSheafifiedYonedaIso G K L (F.obj U)).hom ≫
        (presheafToSheaf L (Type max u₁ v)).map (uliftYoneda.{u₁}.map (eFG.hom.app U)) ≫
        (sheafPullbackSheafifiedYonedaIso FG J L U).inv))) = _
    rw [Adjunction.homEquiv_naturality_left, sheafPullbackSheafifiedYonedaIso_hom_comp]
    show pushforwardSectionsEquiv G K L T (F.obj U) (pullbackSheafifiedYonedaEquiv G K L
      (F.obj U) T ((sheafPullbackSheafifiedYonedaIso G K L (F.obj U)).hom ≫
        (presheafToSheaf L (Type max u₁ v)).map (uliftYoneda.{u₁}.map (eFG.hom.app U)) ≫
        (sheafPullbackSheafifiedYonedaIso FG J L U).inv)) = _
    rw [sheafPullbackSheafifiedYonedaIso_hom_comp, sheafifiedYonedaEquiv_naturality_obj]
    congr 1
    have h := sheafPullbackSheafifiedYonedaIso_hom_comp FG J L U T
      (sheafPullbackSheafifiedYonedaIso FG J L U).inv
    rw [Iso.hom_inv_id] at h
    exact h.symm
  exact hL.trans hR.symm

end CategoryTheory.Sheaf

end
