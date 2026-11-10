module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates along adjunctions of restrictions of sheaves of modules

An adjunction `p ⊣ q` of functors of sites, compatible with morphisms of sheaves of rings,
induces the adjunction `SheafOfModules.pushforwardPushforwardAdj` between restriction of
sheaves of modules along `p` and along `q`; its unit and counit are, on sections, restriction
along the counit and the unit of `p ⊣ q`. This file shows that the formation of mates along
such adjunctions is computed on the sites: the mate of a 2-cell which is restriction along a
2-cell of functors of sites is restriction along the mate of that 2-cell
(`SheafOfModules.mateEquiv_symm_pushforwardPushforwardAdj_app_val_app`), so it is invertible as
soon as the mate on the sites is (`SheafOfModules.isIso_mateEquiv_symm_pushforwardPushforwardAdj`).

## Main results

* `SheafOfModules.mateEquiv_symm_pushforwardPushforwardAdj_app_val_app`
* `SheafOfModules.isIso_mateEquiv_symm_pushforwardPushforwardAdj`
-/

@[expose] public section

universe v u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ u

open CategoryTheory Functor Opposite

namespace SheafOfModules

variable {CY : Type u₁} [Category.{v₁} CY] {CW : Type u₂} [Category.{v₂} CW]
  {CY' : Type u₃} [Category.{v₃} CY'] {CW' : Type u₄} [Category.{v₄} CW']
  {JY : GrothendieckTopology CY} {JW : GrothendieckTopology CW}
  {JY' : GrothendieckTopology CY'} {JW' : GrothendieckTopology CW'}
  {RY : Sheaf JY RingCat.{u}} {RW : Sheaf JW RingCat.{u}} {RY' : Sheaf JY' RingCat.{u}}
  {RW' : Sheaf JW' RingCat.{u}}
  {p : CY ⥤ CW} {q : CW ⥤ CY} {p' : CY' ⥤ CW'} {q' : CW' ⥤ CY'} {a : CW ⥤ CW'} {b : CY ⥤ CY'}
  [hp : p.IsContinuous JY JW] [hq : q.IsContinuous JW JY] [hp' : p'.IsContinuous JY' JW']
  [hq' : q'.IsContinuous JW' JY'] [ha : a.IsContinuous JW JW'] [hb : b.IsContinuous JY JY']
  (adj : p ⊣ q) (adj' : p' ⊣ q')
  (φ : RY ⟶ (p.sheafPushforwardContinuous RingCat.{u} JY JW).obj RW)
  (ψ : RW ⟶ (q.sheafPushforwardContinuous RingCat.{u} JW JY).obj RY)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) RW.obj = ψ.hom ≫ q.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ p.op.whiskerLeft ψ.hom ≫ Functor.whiskerRight (NatTrans.op adj.unit) RY.obj =
    𝟙 RY.obj)
  (φ' : RY' ⟶ (p'.sheafPushforwardContinuous RingCat.{u} JY' JW').obj RW')
  (ψ' : RW' ⟶ (q'.sheafPushforwardContinuous RingCat.{u} JW' JY').obj RY')
  (H₁' : Functor.whiskerRight (NatTrans.op adj'.counit) RW'.obj = ψ'.hom ≫ q'.op.whiskerLeft φ'.hom)
  (H₂' : φ'.hom ≫ p'.op.whiskerLeft ψ'.hom ≫ Functor.whiskerRight (NatTrans.op adj'.unit) RY'.obj =
    𝟙 RY'.obj)
  (γ : RW ⟶ (a.sheafPushforwardContinuous RingCat.{u} JW JW').obj RW')
  (δ : RY ⟶ (b.sheafPushforwardContinuous RingCat.{u} JY JY').obj RY')

/-- **The mate of a 2-cell of restrictions along adjoint functors of sites, on sections.**
Let `p ⊣ q` and `p' ⊣ q'` be adjunctions of sites and `a`, `b` functors of sites, so that
restriction gives adjunctions `p_* ⊣ q_*`, `p'_* ⊣ q'_*` of sheaves of modules
(`SheafOfModules.pushforwardPushforwardAdj`). If a 2-cell `β : q'_* ⋙ a_* ⟶ b_* ⋙ q_*` is, on
sections, restriction along a 2-cell `τ : q ⋙ b ⟶ a ⋙ q'` of functors of sites, then its mate
`a_* ⋙ p_* ⟶ p'_* ⋙ b_*` is, on sections, restriction along the mate
`b ⋙ p' ⟶ p ⋙ a` of `τ`. -/
theorem mateEquiv_symm_pushforwardPushforwardAdj_app_val_app
    (β : TwoSquare (pushforward.{v} ψ') (pushforward.{v} δ) (pushforward.{v} γ) (pushforward.{v} ψ))
    (τ : TwoSquare q a b q')
    (hβ : ∀ (N : SheafOfModules.{v} RY') (V : CWᵒᵖ) (x),
      (β.app N).val.app V x = N.val.map (τ.app V.unop).op x)
    (M : SheafOfModules.{v} RW') (U : CYᵒᵖ) (x) :
    (((mateEquiv (pushforwardPushforwardAdj adj' φ' ψ' H₁' H₂')
        (pushforwardPushforwardAdj adj φ ψ H₁ H₂)).symm β).app M).val.app U x =
      M.val.map (((mateEquiv adj adj').symm τ).app U.unop).op x := by
  have hs : ((mateEquiv adj adj').symm τ).app U.unop =
      p'.map (b.map (adj.unit.app U.unop)) ≫ p'.map (τ.app (p.obj U.unop)) ≫
        adj'.counit.app (a.obj (p.obj U.unop)) := by
    simp [mateEquiv]
  let P := M.val.presheaf
  change _ = P.map _ x
  rw [hs]
  change ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app
      ((pushforward δ).obj ((pushforward φ').obj M))).val.app U
      ((β.app ((pushforward φ').obj M)).val.app (op (p.obj U.unop))
        (((pushforwardPushforwardAdj adj' φ' ψ' H₁' H₂').unit.app M).val.app
          (op (a.obj (p.obj U.unop))) x)) = _
  refine (congrArg (fun y => ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app
      ((pushforward δ).obj ((pushforward φ').obj M))).val.app U y) (hβ _ _ _)).trans ?_
  change P.map _ (P.map _ (P.map _ x)) = _
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  change (P.map (adj'.counit.app (a.obj (p.obj U.unop))).op ≫ P.map _) x = _
  rw [← P.map_comp]
  simp only [op_comp, Category.assoc]
  rfl


/-- **Beck–Chevalley for restrictions of sheaves of modules from Beck–Chevalley for the sites.**
In the situation of `SheafOfModules.mateEquiv_symm_pushforwardPushforwardAdj_app_val_app`, the
mate of `β` is invertible as soon as the mate of `τ` is. -/
theorem isIso_mateEquiv_symm_pushforwardPushforwardAdj
    (β : TwoSquare (pushforward.{v} ψ') (pushforward.{v} δ) (pushforward.{v} γ) (pushforward.{v} ψ))
    (τ : TwoSquare q a b q')
    (hβ : ∀ (N : SheafOfModules.{v} RY') (V : CWᵒᵖ) (x),
      (β.app N).val.app V x = N.val.map (τ.app V.unop).op x)
    [hσ : IsIso ((mateEquiv adj adj').symm τ)] :
    IsIso ((mateEquiv (pushforwardPushforwardAdj adj' φ' ψ' H₁' H₂')
        (pushforwardPushforwardAdj adj φ ψ H₁ H₂)).symm β) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let f := ((mateEquiv (pushforwardPushforwardAdj adj' φ' ψ' H₁' H₂')
        (pushforwardPushforwardAdj adj φ ψ H₁ H₂)).symm β).app M
  have hf : IsIso ((sheafToPresheaf JY AddCommGrpCat.{v}).map ((toSheaf.{v} RY).map f)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    have e : ((sheafToPresheaf JY AddCommGrpCat.{v}).map ((toSheaf.{v} RY).map f)).app U =
        M.val.presheaf.map (((mateEquiv adj adj').symm τ).app U.unop).op := by
      ext x
      exact mateEquiv_symm_pushforwardPushforwardAdj_app_val_app adj adj' φ ψ H₁ H₂ φ' ψ' H₁' H₂'
        γ δ β τ hβ M U x
    rw [e]
    exact Functor.map_isIso _ _
  have : IsIso ((toSheaf.{v} RY).map f) := isIso_of_reflects_iso _ (sheafToPresheaf JY _)
  exact isIso_of_reflects_iso f (toSheaf.{v} RY)

end SheafOfModules
