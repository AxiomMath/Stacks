module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatStalk

/-!
# The stalk of a restriction of scalars at a point of a site

Let `α : O' ⟶ O` be a morphism of sheaves of commutative rings on a site and `F` a sheaf of
`O`-modules.  At a point `Φ` of the site, the stalk of the restriction of scalars `α^* F` has the
same underlying abelian group as the stalk of `F`, and the stalk `O'_Φ` acts on it through the
fibre `α_Φ : O'_Φ ⟶ O_Φ` of `α`.

## Main results

* `Stacks.moduleStalk_restrictScalars_smul`: the action of `O'_Φ` on the stalk of `α^* F` is the
  action of `O_Φ` through `α_Φ`.
* `Stacks.isFlatModuleStalk_restrictScalars`: the stalk of `α^* F` is flat over `O'_Φ` as soon as
  the stalk of `F` is flat over `O'_Φ` acting through `α_Φ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : J.Point.{w}) {O' O : Sheaf J CommRingCat.{w}} (α : O' ⟶ O)
  (β : commRingSheafToRingSheaf O' ⟶ commRingSheafToRingSheaf O)
  (F : SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-- **The stalk action on a restriction of scalars.**  At a point `Φ` of a site, the stalk
`O'_Φ` acts on the stalk of the restriction of scalars of an `O`-module `F` along
`α : O' ⟶ O` through the fibre of `α`: the two stalks have the same underlying group, and
`a • m = α_Φ(a) • m`.  The morphism of sheaves of rings along which the scalars are restricted is
taken as a separate argument `β`, agreeing with `α` on sections. -/
theorem moduleStalk_restrictScalars_smul
    (hβ : ∀ (U : Cᵒᵖ) (a : O'.obj.obj U), β.hom.app U a = α.hom.app U a)
    (a : (Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj)
    (m : moduleStalk Φ O F) :
    a • (id m : moduleStalk Φ O' ((SheafOfModules.restrictScalars β).obj F)) =
      (id (α := moduleStalk Φ O F) ((Φ.presheafFiber (A := CommRingCat.{w})).map α.hom a • m) :
        moduleStalk Φ O' ((SheafOfModules.restrictScalars β).obj F)) := by
  let F' := (SheafOfModules.restrictScalars β).obj F
  obtain ⟨U, ξ, a₀, s, ha, hs⟩ := exists_germ_representatives Φ O' F' ![a] ![m]
  have ha' : ringStalkGerm Φ O' U ξ (a₀ 0) = a := ha 0
  have hs' : (moduleStalkGerm Φ O' F' U ξ (s 0) : moduleStalk Φ O F) = m := hs 0
  rw [← ha']
  show ringStalkGerm Φ O' U ξ (a₀ 0) • (id m : moduleStalk Φ O' F') = _
  rw [← hs']
  refine (moduleStalkGerm_smul Φ O' F' U ξ (a₀ 0) (s 0)).symm.trans ?_
  have hr : (Φ.presheafFiber (A := CommRingCat.{w})).map α.hom (ringStalkGerm Φ O' U ξ (a₀ 0)) =
      ringStalkGerm Φ O U ξ (α.hom.app (op U) (a₀ 0)) :=
    Φ.toPresheafFiber_naturality_apply α.hom U ξ (a₀ 0)
  refine Eq.trans ?_ (congrArg (fun r => (id (α := moduleStalk Φ O F)
    (r • moduleStalkGerm Φ O F U ξ (s 0)) : moduleStalk Φ O' F')) hr.symm)
  refine Eq.trans ?_ (moduleStalkGerm_smul Φ O F U ξ (α.hom.app (op U) (a₀ 0)) (s 0))
  let s₀ : F.val.obj (op U) := s 0
  show moduleStalkGerm Φ O F U ξ (β.hom.app (op U) (a₀ 0) • s₀) = _
  exact congrArg (fun r => moduleStalkGerm Φ O F U ξ (r • s₀)) (hβ (op U) (a₀ 0))

/-- **Flatness of the stalk of a restriction of scalars.**  At a point `Φ`, the stalk of the
restriction of scalars of `F` along `O' ⟶ O` is flat over `O'_Φ` as soon as the stalk of `F` is
flat over `O'_Φ` acting through the fibre `α_Φ : O'_Φ ⟶ O_Φ`. -/
theorem isFlatModuleStalk_restrictScalars
    (hβ : ∀ (U : Cᵒᵖ) (a : O'.obj.obj U), β.hom.app U a = α.hom.app U a)
    (h : @Module.Flat ((Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj) (moduleStalk Φ O F)
      _ _ (Module.compHom _ ((Φ.presheafFiber (A := CommRingCat.{w})).map α.hom).hom)) :
    IsFlatModuleStalk Φ O' ((SheafOfModules.restrictScalars β).obj F) := by
  let : Module ((Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj) (moduleStalk Φ O F) :=
    Module.compHom _ ((Φ.presheafFiber (A := CommRingCat.{w})).map α.hom).hom
  let e : moduleStalk Φ O' ((SheafOfModules.restrictScalars β).obj F) ≃ₗ[
      (Φ.presheafFiber (A := CommRingCat.{w})).obj O'.obj] moduleStalk Φ O F :=
    { toFun := fun m => m
      invFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => moduleStalk_restrictScalars_smul Φ α β F hβ a m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Flat.of_linearEquiv e

end Stacks
