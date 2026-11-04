module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Sections

/-!
# Functoriality of the affine module-sheaf identifications

For a commutative ring `R`, the sheaf `M̃` on `Spec R` associated to an `R`-module `M` varies
functorially with `M`, and the canonical localization identifications of its sections are
natural in `M`: on every open, in particular on a standard open, the map induced on sections by
a module map is the localized map, and the same holds on global sections and on stalks.

## Main results

* `AlgebraicGeometry.tilde.basicOpen_map`: the map induced on standard-open sections by a module
  map is its localization away from the defining element.
* `AlgebraicGeometry.tilde.toStalk_map`: the identification of a stalk of `M̃` with a
  localization at a prime is natural in `M`.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public section

open CategoryTheory

add_to_stacks 01HV "functorial_identifications" AlgebraicGeometry.tilde.functor
add_to_ega "I 1.3.5" AlgebraicGeometry.tilde.functor
add_to_ega "II 1.4.4" "partial" AlgebraicGeometry.tilde.functor
add_to_stacks 01HV "functorial_identifications" AlgebraicGeometry.tilde.toOpen_map_app
add_to_stacks 01HV "functorial_identifications" AlgebraicGeometry.tilde.toTildeΓNatIso
add_to_ega "I 1.3.7" AlgebraicGeometry.tilde.toTildeΓNatIso
add_to_ega "I 10.10.2" "(i), special case" AlgebraicGeometry.tilde.toTildeΓNatIso
add_to_stacks 01HV "tilde_exact"
  AlgebraicGeometry.instIsLeftAdjointModuleCatCarrierModulesSpecFunctor

universe u

namespace AlgebraicGeometry.tilde

section Helpers

open TopologicalSpace TopCat.Presheaf

private noncomputable def schemeStalkMap {X : Scheme.{u}} {F G : X.Modules}
    (α : F ⟶ G) (x : X) : F.presheaf.stalk x → G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor Ab x).map α.mapPresheaf

private theorem schemeStalkMap_ringSmul {X : Scheme.{u}} (F G : X.Modules)
    (α : F ⟶ G) (x : X) (a : X.presheaf.stalk x) (m : F.presheaf.stalk x) :
    schemeStalkMap α x (a • m) = a • schemeStalkMap α x m := by
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq m
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op r
  let sW : Γ(F, W) := F.presheaf.map (homOfLE inf_le_right).op s
  have hr : X.presheaf.germ U x hxU r = X.presheaf.germ W x hxW rW :=
    (X.presheaf.germ_res_apply (homOfLE inf_le_left) x hxW r).symm
  have hs : F.presheaf.germ V x hxV s = F.presheaf.germ W x hxW sW :=
    (F.presheaf.germ_res_apply (homOfLE inf_le_right) x hxW s).symm
  rw [hr, hs]
  have hF : X.presheaf.germ W x hxW rW • F.presheaf.germ W x hxW sW =
      F.presheaf.germ W x hxW (rW • sW) :=
    (PresheafOfModules.germ_smul F.val x W hxW rW sW).symm
  rw [hF]
  have hnat (t : Γ(F, W)) :
      schemeStalkMap α x (F.presheaf.germ W x hxW t) =
        G.presheaf.germ W x hxW ((α.app W) t) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW α.mapPresheaf t
  rw [hnat, α.app_smul]
  have hG : G.presheaf.germ W x hxW (rW • (α.app W sW)) =
      X.presheaf.germ W x hxW rW • G.presheaf.germ W x hxW ((α.app W) sW) :=
    PresheafOfModules.germ_smul G.val x W hxW rW ((α.app W) sW)
  rw [hG, hnat]

private theorem schemeStalkMap_smul {R : CommRingCat.{u}} (M N : ModuleCat R)
    (f : M ⟶ N) (x : PrimeSpectrum.Top (↑R)) (r : R)
    (m : (tilde M).presheaf.stalk x) :
    schemeStalkMap (tilde.map f) x (r • m) = r • schemeStalkMap (tilde.map f) x m := by
  let : Module ((structurePresheafInCommRingCat (↑R)).stalk x)
      ((tilde M).presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde M) x
  let : Module ((structurePresheafInCommRingCat (↑R)).stalk x)
      ((tilde N).presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde N) x
  show schemeStalkMap (tilde.map f) x
      (CommRingCat.Hom.hom (StructureSheaf.toStalk (↑R) x) r • m) =
    CommRingCat.Hom.hom (StructureSheaf.toStalk (↑R) x) r • schemeStalkMap (tilde.map f) x m
  exact schemeStalkMap_ringSmul (tilde M) (tilde N) (tilde.map f) x
    (CommRingCat.Hom.hom (StructureSheaf.toStalk (↑R) x) r) m

/-- The section of `M̃` over `⊤` attached to `y : M` is carried by `tilde.map f` to the section
attached to `f y`. -/
private theorem tildeTopSection_map {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (y : M) :
    (tilde.map f).app (⊤ : (Spec R).Opens)
      (StructureSheaf.toOpenₗ (↑R) (↑M) (⊤ : Opens (PrimeSpectrum.Top ↑R)) y) =
    StructureSheaf.toOpenₗ (↑R) (↑N) (⊤ : Opens (PrimeSpectrum.Top ↑R)) (f.hom y) :=
  StructureSheaf.comapₗ_const (R := (↑R : Type u)) (S := (↑R : Type u))
    (σ := RingHom.id (↑R : Type u)) (M := (↑M : Type u)) (N := (↑N : Type u))
    (ModuleCat.Hom.hom f) (⊤ : Opens (PrimeSpectrum.Top ↑R))
    (⊤ : Opens (PrimeSpectrum.Top ↑R)) (fun p hp => hp) y 1 (by simp)

/-- The map induced on stalks by `tilde.map f` carries the canonical image of `y : M` to the
canonical image of `f y`. -/
private theorem tildeStalkMap_toStalk {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : PrimeSpectrum.Top R) (y : M) :
    ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf (tilde.map f))) ((tilde.toStalk M x).hom y) =
    (tilde.toStalk N x).hom (f.hom y) := by
  have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := Ab) (F := (tilde M).presheaf) (G := (tilde N).presheaf)
    (⊤ : (Spec R).Opens) x (by trivial)
    (Scheme.Modules.Hom.mapPresheaf (tilde.map f))
    (StructureSheaf.toOpenₗ (↑R) (↑M) ⊤ y)
  have hsection : (Scheme.Modules.Hom.mapPresheaf (tilde.map f)).app
        (Opposite.op (⊤ : (Spec R).Opens))
        (StructureSheaf.toOpenₗ (↑R) (↑M) ⊤ y) =
      StructureSheaf.toOpenₗ (↑R) (↑N) ⊤ (f.hom y) :=
    tildeTopSection_map f y
  exact hgerm.trans (congrArg
    ((tilde N).presheaf.germ (⊤ : (Spec R).Opens) x (by trivial)) hsection)

/-- A linear map between localized modules that is compatible with a map `φ` on the unlocalized
modules is the induced map `IsLocalizedModule.map`. -/
private theorem eq_map_of_comp_apply {R : Type*} [CommRing R] {S : Submonoid R}
    {M M' N N' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
    [AddCommMonoid N'] [Module R M] [Module R M'] [Module R N] [Module R N']
    (fM : M →ₗ[R] M') (fN : N →ₗ[R] N') [IsLocalizedModule S fM] [IsLocalizedModule S fN]
    (φ : M →ₗ[R] N) (q : M' →ₗ[R] N') (h : ∀ y, q (fM y) = fN (φ y)) :
    q = IsLocalizedModule.map S fM fN φ :=
  IsLocalizedModule.ext S fM (IsLocalizedModule.map_units fN) (by
    ext y; simp [h, IsLocalizedModule.map_apply])

end Helpers

/-- Under the canonical localization identifications, the map on sections
over a standard open induced by a module map is its localization. -/
@[stacks 01HV "functorial_identifications"]
theorem basicOpen_map {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (a : R) (m : LocalizedModule.Away (R := R) a M) :
    ((modulesSpecToSheaf.map (tilde.map f)).1.app
        (.op (PrimeSpectrum.basicOpen a)))
      ((IsLocalizedModule.iso (Submonoid.powers a)
        (tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom) m) =
      (IsLocalizedModule.iso (Submonoid.powers a)
        (tilde.toOpen N (PrimeSpectrum.basicOpen a)).hom)
        (IsLocalizedModule.map (Submonoid.powers a)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) N) f.hom m) := by
  let U := PrimeSpectrum.basicOpen a
  let S := Submonoid.powers a
  let iM := IsLocalizedModule.iso S (tilde.toOpen M U).hom
  let iN := IsLocalizedModule.iso S (tilde.toOpen N U).hom
  let q := ((modulesSpecToSheaf.map (tilde.map f)).1.app (.op U)).hom
  have hmaps := eq_map_of_comp_apply (S := S) (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) f.hom (iN.symm.toLinearMap ∘ₗ q ∘ₗ iM.toLinearMap)
    (fun y => by
      have hnat : q ((tilde.toOpen M U).hom y) = (tilde.toOpen N U).hom (f.hom y) :=
        congrArg (fun g : M ⟶ _ => g.hom y) (tilde.toOpen_map_app f U)
      have h1 : iM (LocalizedModule.mk y 1) = (tilde.toOpen M U).hom y :=
        IsLocalizedModule.iso_mk_one S _ y
      have h2 : iN (LocalizedModule.mk (f.hom y) 1) = (tilde.toOpen N U).hom (f.hom y) :=
        IsLocalizedModule.iso_mk_one S _ _
      change iN.symm (q (iM (LocalizedModule.mk y 1))) = LocalizedModule.mk (f.hom y) 1
      rw [h1, hnat, ← h2, LinearEquiv.symm_apply_apply])
  have := congrArg iN (congrArg (fun g : _ →ₗ[R] _ => g m) hmaps)
  simpa using this

/-- The canonical identification of the stalk of an associated sheaf with
localization at a prime is natural in the module. -/
@[stacks 01HV "functorial_identifications"]
theorem toStalk_map {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : PrimeSpectrum.Top R)
    (m : (tilde M).presheaf.stalk x) :
    ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf (tilde.map f))) m =
      IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk M x).hom (tilde.toStalk N x).hom f.hom m := by
  let stalkMap := (TopCat.Presheaf.stalkFunctor Ab x).map
    (Scheme.Modules.Hom.mapPresheaf (tilde.map f))
  let lhs : (tilde M).presheaf.stalk x →ₗ[R] (tilde N).presheaf.stalk x := {
    toFun := stalkMap
    map_add' := by intros; exact stalkMap.hom.map_add _ _
    map_smul' := schemeStalkMap_smul M N f x }
  exact congrArg (fun g : _ →ₗ[R] _ => g m)
    (eq_map_of_comp_apply (S := x.asIdeal.primeCompl) (tilde.toStalk M x).hom
      (tilde.toStalk N x).hom f.hom lhs (tildeStalkMap_toStalk f x))

end AlgebraicGeometry.tilde

end
