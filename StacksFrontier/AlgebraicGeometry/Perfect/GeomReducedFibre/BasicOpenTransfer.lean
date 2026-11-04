module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.Assembly

/-!
# Passing a property of `R_h → R_h ⊗_R Γ(f⁻¹W, 𝒪)` to the basic open `D(h)` of the base

The affine case of [Stacks, Tag 0G7Y] is proved for `g : f⁻¹W ⟶ Spec Γ(S, W)`, with
`W ⊆ S` an affine open, and gives finite etaleness of `R_h → R_h ⊗_R Γ(f⁻¹W, 𝒪)` for
`R = Γ(S, W)`. This file identifies that ring map with `f.app (S.basicOpen h)`, up to isomorphism,
so that a property of ring maps respecting isomorphisms passes from one to the other
(`app_basicOpen_of_tensor`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- Restriction maps along equalities of opens commute with the map on sections. -/
theorem presheafMap_eqToHom_app_eqToHom_apply {X S : Scheme.{u}} (f : X ⟶ S) {W U' : S.Opens}
    (c : U' = W) {V₁ : X.Opens}
    (b : V₁ = f ⁻¹ᵁ U') (a : f ⁻¹ᵁ W = V₁) (r : Γ(S, W)) :
    (X.presheaf.map (eqToHom a).op).hom ((X.presheaf.map (eqToHom b).op).hom
      ((f.app U').hom ((S.presheaf.map (eqToHom c).op).hom r))) = (f.app W).hom r := by
  subst c b
  simp

/-- Over an affine open `W`, the global ring map of `f⁻¹W ⟶ Spec Γ(S, W)` is `f.app W`. -/
theorem topIso_globalRingHom_restrict_isoSpec_apply {X S : Scheme.{u}} (f : X ⟶ S) {W : S.Opens}
    (hW : IsAffineOpen W) (r : Γ(S, W)) :
    (f ⁻¹ᵁ W).topIso.hom ((Stacks.Cech.globalRingHom (f ∣_ W ≫ hW.isoSpec.hom)).hom r) =
      (f.app W).hom r := by
  have h1 (x) : (hW.isoSpec.hom.app ⊤).hom x =
      W.topIso.inv.hom ((Scheme.ΓSpecIso Γ(S, W)).hom.hom x) :=
    congrArg (fun φ => φ.hom x) hW.isoSpec_hom_appTop
  have h2 (x) : ((f ∣_ W).app ⊤).hom x = (X.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f W ⊤)).op).hom ((f.app (W.ι ''ᵁ ⊤)).hom x) :=
    congrArg (fun φ => φ.hom x) (morphismRestrict_appTop f W)
  show (f ⁻¹ᵁ W).topIso.hom.hom (((f ∣_ W).app ⊤).hom ((hW.isoSpec.hom.app ⊤).hom
    ((Scheme.ΓSpecIso Γ(S, W)).inv.hom r))) = _
  rw [h1, h2, Iso.inv_hom_id_apply]
  exact presheafMap_eqToHom_app_eqToHom_apply f (by simp) (by simp) (by simp) r

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

include P in
/-- A ring map `R_h → C`, with `C` a localization of an `R`-algebra `A` away from the image of
`h`, has every property respecting isomorphisms that `R_h → R_h ⊗_R A` has. -/
theorem of_algebraMap_localizationAway_tensor (hP : RingHom.RespectsIso @P) {R A A' C : Type u}
    [CommRing R] [CommRing A] [CommRing A'] [CommRing C] (ψ : R →+* A) (ι : A ≃+* A') (h : R)
    (a' : A') (ha' : ι (ψ h) = a')
    [Algebra A' C] [IsLocalization.Away a' C] (χ : Localization.Away h →+* C)
    (hχ : χ.comp (algebraMap R _) = (algebraMap A' C).comp (ι.toRingHom.comp ψ))
    (H : letI := ψ.toAlgebra
      P (algebraMap (Localization.Away h) (Localization.Away h ⊗[R] A))) : P χ := by
  let := ψ.toAlgebra
  let M := Algebra.algebraMapSubmonoid A (Submonoid.powers h)
  let T := Localization.tensorRightAlgEquiv (Submonoid.powers h) A
  have hM : M.map ι.toMonoidHom = Submonoid.powers a' := by
    show (Submonoid.map (algebraMap R A) (Submonoid.powers h)).map ι.toMonoidHom = _
    rw [← ha', Submonoid.map_powers, Submonoid.map_powers]
    rfl
  let e₂ : Localization M ≃+* C := IsLocalization.ringEquivOfRingEquiv (Localization M) C ι hM
  let e : Localization.Away h ⊗[R] A ≃+* C := T.toRingEquiv.trans e₂
  have : χ = e.toRingHom.comp (algebraMap (Localization.Away h) _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    rw [hχ]
    ext r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, T]
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply R (Localization.Away h),
      IsScalarTower.algebraMap_apply R A (Localization M), IsLocalization.ringEquivOfRingEquiv_eq]
    rfl
  rw [this]
  exact hP.1 _ e H

include P in
/-- **From the affine case to a basic open of the base.** If `R_h → R_h ⊗_R Γ(f⁻¹W, 𝒪)` has a
property respecting isomorphisms, for `R = Γ(S, W)` with `W` affine, then so has
`f.app (S.basicOpen h)`. -/
theorem app_basicOpen_of_tensor (hP : RingHom.RespectsIso @P) {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {W : S.Opens} (hW : IsAffineOpen W) (h : Γ(S, W))
    (H : letI := (Stacks.Cech.globalRingHom (f ∣_ W ≫ hW.isoSpec.hom)).hom.toAlgebra
      P (algebraMap (Localization.Away h) (Localization.Away h ⊗[Γ(S, W)] Γ(f ⁻¹ᵁ W, ⊤)))) :
    P (f.app (S.basicOpen h)).hom := by
  rw [app_basicOpen_iff_away_map f hP hW h]
  refine of_algebraMap_localizationAway_tensor hP
    (Stacks.Cech.globalRingHom (f ∣_ W ≫ hW.isoSpec.hom)).hom
    (f ⁻¹ᵁ W).topIso.commRingCatIsoToRingEquiv h ((f.app W).hom h)
    (topIso_globalRingHom_restrict_isoSpec_apply f hW h) _ ?_ H
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_comp]
  congr 1
  ext r
  exact (topIso_globalRingHom_restrict_isoSpec_apply f hW r).symm

end StacksDraft.Perfect.GeomReducedFibre

end
