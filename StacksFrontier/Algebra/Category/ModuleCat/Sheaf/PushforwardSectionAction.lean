module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Multiplication by a section, after restriction of scalars and pushforward

Let `F : C ⥤ D` be a continuous functor of sites, `φ : 𝒮 ⟶ F_*ℛ` a morphism of sheaves of rings,
and `ψ : ℛ ⟶ 𝒜` a morphism of sheaves of rings into a sheaf of *commutative* rings on `D`.  A
family of sections `e_T ∈ 𝒜(F T)`, compatible with restriction along `F`, acts on every
`𝒜`-module `ℳ`, and after restricting scalars to `ℛ` and pushing forward along `F` the action
is a morphism of `𝒮`-modules

`μ_e : F_*(ℳ_ℛ) ⟶ F_*(ℳ_ℛ)`,  `m ↦ e_T · m`,

natural in `ℳ` along morphisms of `𝒜`-modules.

The case in view is the restriction along an étale morphism `g : U ⟶ X` of algebraic spaces of a
module over `𝒜 = π_*𝒪_Y`, with `e` a global section of the restriction of `𝒜` to `U`.

## Main definitions

* `Stacks.SheafOfModules.pushforwardSectionAction`: the morphism `μ_e`.

## Main results

* `Stacks.SheafOfModules.pushforwardSectionAction_naturality`: `μ_e` is natural in `ℳ`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v v₁ v₂ u₁ u₂ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]
  {𝒮 : Sheaf J RingCat.{u}} {ℛ : Sheaf K RingCat.{u}}
  (φ : 𝒮 ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj ℛ)
  {𝒜 : Sheaf K RingCat.{u}} (ψ : ℛ ⟶ 𝒜)
  (h𝒜 : ∀ (V : Dᵒᵖ) (a b : 𝒜.obj.obj V), a * b = b * a)
  (e : ∀ T : Cᵒᵖ, 𝒜.obj.obj (op (F.obj T.unop)))
  (he : ∀ {T T' : Cᵒᵖ} (f : T ⟶ T'), (𝒜.obj.map (F.map f.unop).op).hom (e T) = e T')
  (M : _root_.SheafOfModules.{v} 𝒜)

/-- Multiplication by a section `a ∈ 𝒜(V)` on `ℳ(V)`, an `𝒜(V)`-linear map since `𝒜(V)` is
commutative. -/
def smulLinear (V : Dᵒᵖ) (a : 𝒜.obj.obj V) : M.val.obj V ⟶ M.val.obj V :=
  ModuleCat.ofHom
    { toFun := fun m => a • m
      map_add' := fun m m' => smul_add a m m'
      map_smul' := fun b m => by
        rw [RingHom.id_apply, smul_smul, smul_smul, h𝒜] }

/-- **Multiplication by the compatible family `e`**, after restriction of scalars along `ψ` and
pushforward along `F`. -/
def pushforwardSectionAction :
    (_root_.SheafOfModules.pushforward φ).obj ((_root_.SheafOfModules.restrictScalars ψ).obj M) ⟶
      (_root_.SheafOfModules.pushforward φ).obj ((_root_.SheafOfModules.restrictScalars ψ).obj M)
      where
  val :=
    { app T := (ModuleCat.restrictScalars (φ.hom.app T).hom).map
        ((ModuleCat.restrictScalars (ψ.hom.app (op (F.obj T.unop))).hom).map
          (smulLinear h𝒜 M _ (e T)))
      naturality := fun {T T'} f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        have h := M.val.map_smul (F.map f.unop).op (e T) m
        rw [he] at h
        exact h.symm }

theorem pushforwardSectionAction_app_apply (T : Cᵒᵖ)
    (m : M.val.obj (op (F.obj T.unop))) :
    ((pushforwardSectionAction F φ ψ h𝒜 e he M).val.app T).hom m =
      (e T • m : M.val.obj (op (F.obj T.unop))) := rfl

variable {M} in
/-- **`μ_e` is natural** along morphisms of `𝒜`-modules. -/
theorem pushforwardSectionAction_naturality {M' : _root_.SheafOfModules.{v} 𝒜} (α : M ⟶ M') :
    (_root_.SheafOfModules.pushforward φ).map ((_root_.SheafOfModules.restrictScalars ψ).map α) ≫
        pushforwardSectionAction F φ ψ h𝒜 e he M' =
      pushforwardSectionAction F φ ψ h𝒜 e he M ≫
        (_root_.SheafOfModules.pushforward φ).map
          ((_root_.SheafOfModules.restrictScalars ψ).map α) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (map_smul (α.val.app (op (F.obj T.unop))).hom (e T)
    (show M.val.obj (op (F.obj T.unop)) from m)).symm

end Stacks.SheafOfModules
