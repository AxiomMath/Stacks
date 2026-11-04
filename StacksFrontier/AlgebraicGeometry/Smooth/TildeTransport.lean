module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Modules over the global sections of an affine scheme as sheaves of modules

Let `T` be an affine scheme and let `A = Γ(T, ⊤)` be its ring of global sections. Mathlib's
`AlgebraicGeometry.tilde.adjunction` presents every `A`-module as the module of global sections
of a sheaf of modules, but only on `Spec A` on the nose. This file transports that presentation
along the isomorphism `T ≅ Spec Γ(T, ⊤)` of `AlgebraicGeometry.Scheme.isoSpec`, so that it
applies to an arbitrary affine scheme.

## Main definitions

* `Stacks.Modules.specModules M` is the sheaf of modules on `T` attached to a
  `Γ(T, ⊤)`-module `M`: the sheaf `M^~` on `Spec Γ(T, ⊤)`, pushed forward along
  `T.isoSpec.inv`.
* `Stacks.Modules.specModulesEquiv` is the isomorphism `M ≃ Γ(specModules M, ⊤)` of
  `Γ(T, ⊤)`-modules.
* `Stacks.Modules.specModulesLift` is the morphism `specModules M ⟶ P` attached to a
  `Γ(T, ⊤)`-linear map from `M` to the global sections of a sheaf of modules `P` on `T`.

## Main results

* `Stacks.Modules.specModulesLift_app_top`: `specModulesLift` induces the given linear map on
  global sections.
* `Stacks.Modules.exists_modules_globalSections` packages the three together: every module over
  the global sections of an affine scheme is the module of global sections of a sheaf of modules,
  adjointly.

## Implementation notes

Write `u = T.isoSpec.hom` and `v = T.isoSpec.inv`. The transport is by *pushforward* rather than
pullback, in both directions: `Γ((pushforward w).obj Q, U) = Γ(Q, w ⁻¹ᵁ U)` holds by definition
and `w ⁻¹ᵁ ⊤ = ⊤`, so on global sections the pushforward functors do nothing at all, whereas the
sections of a pullback are not computable in closed form. Concretely, `specModules M` is
`v_*(M^~)` and the identification `Γ(specModules M, ⊤) = Γ(M^~, ⊤)` is a reflexivity; the
morphism attached to a linear map is obtained by pushing the morphism `M^~ ⟶ u_*P` produced by
`tilde.adjunction` forward along `v` and using `Stacks.Modules.pushforwardIsoSpecCompIso`, the
identification `u_* ⋙ v_* ≅ 𝟭` coming from `u ≫ v = 𝟙`.

The only thing that is *not* a reflexivity is the comparison of the two `Γ(T, ⊤)`-module
structures on those global sections. On `Γ(Q, ⊤)` for `Q` a sheaf of modules on `Spec A`,
Mathlib's instance restricts scalars along `Scheme.ΓSpecIso A`, while on `Γ(w_*Q, ⊤)` the module
structure restricts scalars along `w.appTop`; the two agree because
`T.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).inv`
(`Stacks.Modules.isoSpec_inv_appTop`). That comparison is what
`Stacks.Modules.pushforwardTopEquiv` and `Stacks.Modules.pushforwardHomTopEquiv` record.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Modules

/-! ### Restriction to `⊤` -/

/-- The restriction map of a sheaf of modules attached to `Opens.leTop ⊤` is the identity. -/
theorem map_leTop_top {Y : Scheme.{u}} {F : Y.Modules} (x : Γ(F, (⊤ : Y.Opens))) :
    (F.presheaf.map (⊤ : Y.Opens).leTop.op).hom x = x :=
  congrArg (fun f ↦ f.hom x) (F.presheaf.map_id (op ⊤))

/-- The restriction map of the structure sheaf attached to `Opens.leTop ⊤` is the identity. -/
theorem presheaf_map_leTop_top {Y : Scheme.{u}} (x : Γ(Y, (⊤ : Y.Opens))) :
    (Y.presheaf.map (⊤ : Y.Opens).leTop.op).hom x = x :=
  congrArg (fun f ↦ f.hom x) (Y.presheaf.map_id (op ⊤))

/-! ### The two module structures on global sections -/

/-- The action of `Γ(Z, ⊤)` on the global sections of a pushforward along `w : Y ⟶ Z` is the
action of `Γ(Y, ⊤)` restricted along `w.appTop`. -/
theorem smul_pushforward_top {Y Z : Scheme.{u}} (w : Y ⟶ Z) (Q : Y.Modules)
    (s : Γ(Z, (⊤ : Z.Opens))) (x : Γ((Scheme.Modules.pushforward w).obj Q, (⊤ : Z.Opens))) :
    s • x = w.appTop.hom s • (show Γ(Q, (⊤ : Y.Opens)) from x) :=
  rfl

/-- The action of `R` on the global sections of a sheaf of modules on `Spec R` is the action of
`Γ(Spec R, ⊤)` restricted along `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem smul_spec_top {R : CommRingCat.{u}} (Q : (Spec R).Modules) (r : R)
    (x : Γ(Q, (⊤ : (Spec R).Opens))) :
    r • x = (Scheme.ΓSpecIso R).inv.hom r • x := by
  rw [Scheme.Modules.smul_Spec_def, presheaf_map_leTop_top]

variable {T : Scheme.{u}} [IsAffine T]

/-! ### Global sections along `Scheme.isoSpec` -/

/- These two are about `AlgebraicGeometry.Scheme.isoSpec` of an affine scheme, not about
`AlgebraicGeometry.IsAffineOpen.isoSpec` of an affine open: Mathlib's homonyms
`IsAffineOpen.isoSpec_hom_appTop`/`isoSpec_inv_appTop` carry the extra comparison
`U.topIso` between `Γ(U, ⊤)` and `Γ(X, U)`, which has no counterpart here. -/

/-- On global sections `AlgebraicGeometry.Scheme.isoSpec` is the canonical identification
`Γ(Spec Γ(T, ⊤), ⊤) ≅ Γ(T, ⊤)`. -/
theorem isoSpec_hom_appTop : T.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).hom := by
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]

/-- On global sections the inverse of `AlgebraicGeometry.Scheme.isoSpec` is the inverse of the
canonical identification `Γ(Spec Γ(T, ⊤), ⊤) ≅ Γ(T, ⊤)`. -/
theorem isoSpec_inv_appTop : T.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).inv :=
  (Iso.comp_hom_eq_id _).mp <| by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv,
      Scheme.Hom.id_appTop]

/-! ### Transporting a sheaf of modules on `Spec Γ(T, ⊤)` to `T` -/

/-- Pushing a sheaf of modules on `T` forward along `T.isoSpec.hom` and then back along
`T.isoSpec.inv` does nothing. -/
noncomputable def pushforwardIsoSpecCompIso :
    Scheme.Modules.pushforward T.isoSpec.hom ⋙ Scheme.Modules.pushforward T.isoSpec.inv
      ≅ 𝟭 T.Modules :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr T.isoSpec.hom_inv_id ≪≫ Scheme.Modules.pushforwardId T

/-- `Stacks.Modules.pushforwardIsoSpecCompIso` is the identity on global sections. -/
theorem pushforwardIsoSpecCompIso_app_top (P : T.Modules) (x : Γ(P, (⊤ : T.Opens))) :
    ((pushforwardIsoSpecCompIso.hom.app P).app ⊤).hom x = x := by
  simp only [pushforwardIsoSpecCompIso, Iso.trans_hom, Functor.id_obj, Functor.comp_obj,
    Scheme.Modules.pushforward_obj_obj, TopologicalSpace.Opens.map_top]
  exact map_leTop_top x

/-- **The sheaf of modules on an affine scheme attached to a module over its global sections.**
For `T` an affine scheme and `M` a `Γ(T, ⊤)`-module, this is the sheaf `M^~` on `Spec Γ(T, ⊤)`
transported to `T` along `T ≅ Spec Γ(T, ⊤)`. -/
noncomputable def specModules (M : ModuleCat.{u} Γ(T, ⊤)) : T.Modules :=
  (Scheme.Modules.pushforward T.isoSpec.inv).obj (tilde M)

/-- The `Γ(T, ⊤)`-action on the global sections of the transport to `T` of a sheaf of modules on
`Spec Γ(T, ⊤)` is the action that `AlgebraicGeometry.Scheme.ΓSpecIso` restricts. -/
theorem smul_pushforward_isoSpec_inv (Q : (Spec Γ(T, ⊤)).Modules) (r : Γ(T, ⊤))
    (x : Γ((Scheme.Modules.pushforward T.isoSpec.inv).obj Q, (⊤ : T.Opens))) :
    r • x = (Scheme.ΓSpecIso Γ(T, ⊤)).inv.hom r •
      (show Γ(Q, (⊤ : (Spec Γ(T, ⊤)).Opens)) from x) := by
  rw [smul_pushforward_top, isoSpec_inv_appTop]

/-- The global sections of a sheaf of modules `Q` on `Spec Γ(T, ⊤)`, as a `Γ(T, ⊤)`-module, are
the global sections of the transport of `Q` to `T`. -/
def pushforwardTopEquiv (Q : (Spec Γ(T, ⊤)).Modules) :
    Γ(Q, (⊤ : (Spec Γ(T, ⊤)).Opens)) ≃ₗ[Γ(T, ⊤)]
      Γ((Scheme.Modules.pushforward T.isoSpec.inv).obj Q, (⊤ : T.Opens)) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := (smul_spec_top Q r x).trans (smul_pushforward_isoSpec_inv Q r x).symm
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `Γ(T, ⊤)`-action that `AlgebraicGeometry.Scheme.ΓSpecIso` restricts on the global
sections of the pushforward of a sheaf of modules on `T` is the original action. -/
theorem smul_pushforward_isoSpec_hom (P : T.Modules) (r : Γ(T, ⊤))
    (x : Γ((Scheme.Modules.pushforward T.isoSpec.hom).obj P, (⊤ : (Spec Γ(T, ⊤)).Opens))) :
    r • x = r • (show Γ(P, (⊤ : T.Opens)) from x) := by
  rw [smul_spec_top, smul_pushforward_top, isoSpec_hom_appTop, ← CommRingCat.comp_apply,
    Iso.inv_hom_id]
  rfl

/-- The global sections of a sheaf of modules `P` on `T`, as a `Γ(T, ⊤)`-module, are the global
sections of the pushforward of `P` to `Spec Γ(T, ⊤)`. -/
def pushforwardHomTopEquiv (P : T.Modules) :
    Γ(P, (⊤ : T.Opens)) ≃ₗ[Γ(T, ⊤)]
      Γ((Scheme.Modules.pushforward T.isoSpec.hom).obj P, (⊤ : (Spec Γ(T, ⊤)).Opens)) where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := (smul_pushforward_isoSpec_hom P r x).symm
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A module over the global sections of an affine scheme is the module of global sections of
`Stacks.Modules.specModules`.** -/
noncomputable def specModulesEquiv (M : ModuleCat.{u} Γ(T, ⊤)) :
    M ≃ₗ[Γ(T, ⊤)] Γ(specModules M, (⊤ : T.Opens)) :=
  (tilde.isoTop M).toLinearEquiv.trans (pushforwardTopEquiv (tilde M))

/-- The underlying map of `Stacks.Modules.specModulesEquiv` is `AlgebraicGeometry.tilde.toOpen`
at `⊤`. -/
theorem specModulesEquiv_apply (M : ModuleCat.{u} Γ(T, ⊤)) (m : M) :
    specModulesEquiv M m = tilde.toOpen M ⊤ m :=
  rfl

/-- The morphism of sheaves of modules on `T` attached, through the adjunction between `~` and
global sections, to a `Γ(T, ⊤)`-linear map out of `M`. -/
noncomputable def specModulesLift (M : ModuleCat.{u} Γ(T, ⊤)) (P : T.Modules)
    (g : M →ₗ[Γ(T, ⊤)] Γ(P, (⊤ : T.Opens))) : specModules M ⟶ P :=
  (Scheme.Modules.pushforward T.isoSpec.inv).map
      ((tilde.adjunction.homEquiv M ((Scheme.Modules.pushforward T.isoSpec.hom).obj P)).symm
        (ModuleCat.ofHom
          (Y := Γ((Scheme.Modules.pushforward T.isoSpec.hom).obj P, (⊤ : (Spec Γ(T, ⊤)).Opens)))
          ((pushforwardHomTopEquiv P).toLinearMap ∘ₗ g))) ≫
    pushforwardIsoSpecCompIso.hom.app P

/-- **`Stacks.Modules.specModulesLift` induces the given linear map on global sections.** -/
theorem specModulesLift_app_top (M : ModuleCat.{u} Γ(T, ⊤)) (P : T.Modules)
    (g : M →ₗ[Γ(T, ⊤)] Γ(P, (⊤ : T.Opens))) (m : M) :
    (specModulesLift M P g).app ⊤ (specModulesEquiv M m) = g m := by
  let g' : M ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward T.isoSpec.hom).obj P) :=
    ModuleCat.ofHom
      (Y := Γ((Scheme.Modules.pushforward T.isoSpec.hom).obj P, (⊤ : (Spec Γ(T, ⊤)).Opens)))
      ((pushforwardHomTopEquiv P).toLinearMap ∘ₗ g)
  have key : ((tilde.adjunction.homEquiv M
      ((Scheme.Modules.pushforward T.isoSpec.hom).obj P)).symm g').app ⊤
        (tilde.toOpen M ⊤ m) = g' m := by
    have h := (tilde.adjunction.homEquiv M
      ((Scheme.Modules.pushforward T.isoSpec.hom).obj P)).apply_symm_apply g'
    rw [Adjunction.homEquiv_unit] at h
    exact congr($(h.symm) m).symm
  exact (congrArg (fun y ↦ ((pushforwardIsoSpecCompIso.hom.app P).app ⊤).hom y) key).trans
    (pushforwardIsoSpecCompIso_app_top P (g m))

/-- **Every module over the global sections of an affine scheme is the module of global sections
of a sheaf of modules, adjointly.** For `T` an affine scheme and `M` a `Γ(T, ⊤)`-module there is
a sheaf of modules `N` on `T` and an isomorphism `M ≃ Γ(N, ⊤)` of `Γ(T, ⊤)`-modules such that
every `Γ(T, ⊤)`-linear map from `M` to the global sections of a sheaf of modules `P` on `T` is
induced by a morphism `N ⟶ P`.

This is `AlgebraicGeometry.tilde.adjunction` together with `AlgebraicGeometry.tilde.isoTop`,
transported from `Spec Γ(T, ⊤)` to `T` along `AlgebraicGeometry.Scheme.isoSpec`. -/
theorem exists_modules_globalSections (T : Scheme.{u}) [IsAffine T] (M : Type u)
    [AddCommGroup M] [Module Γ(T, ⊤) M] :
    ∃ (N : T.Modules) (e : M ≃ₗ[Γ(T, ⊤)] Γ(N, (⊤ : T.Opens))),
      ∀ (P : T.Modules) (g : M →ₗ[Γ(T, ⊤)] Γ(P, (⊤ : T.Opens))),
        ∃ χ : N ⟶ P, ∀ m : M, χ.app ⊤ (e m) = g m :=
  ⟨specModules (ModuleCat.of Γ(T, ⊤) M), specModulesEquiv (ModuleCat.of Γ(T, ⊤) M),
    fun P g ↦ ⟨specModulesLift (ModuleCat.of Γ(T, ⊤) M) P g,
      specModulesLift_app_top (ModuleCat.of Γ(T, ⊤) M) P g⟩⟩

end Stacks.Modules

end
