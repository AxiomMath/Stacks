module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Quasi-coherence from localization on basic opens

Mathlib's `AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing` says that a module on `Spec R`
is quasi-coherent as soon as its sections over every basic open `D(a)` are the localization of
its global sections away from `a`. This file turns that into a criterion on an arbitrary
scheme: a module whose sections over the basic opens of each affine open are localizations of
its sections over that affine open is quasi-coherent. This is the converse of
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`.

## Main results

* `isQuasicoherent_spec_of_isLocalizedModule`: the criterion on `Spec R`, with the restriction
  maps written as the linear maps `specRestrictₗ`.
* `isQuasicoherent_restrict_fromSpec`: the criterion transported to the restriction of a module
  along `IsAffineOpen.fromSpec`.
* `isQuasicoherent_of_isLocalizedModule_restrictₗ`: the criterion on an arbitrary scheme.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.TorsionQuasicoherent

/-- A module on `Spec R` whose sections over each basic open `D(a)` are the localization of its
global sections away from `a` is quasi-coherent. -/
theorem isQuasicoherent_spec_of_isLocalizedModule {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (h : ∀ (a : R) (W : (Spec R).Opens), W = PrimeSpectrum.basicOpen a →
      IsLocalizedModule.Away a (specRestrictₗ M (le_top (a := W)))) :
    M.IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ M).mpr
    ((isIso_fromTildeΓ_iff_isLocalizing M).mpr fun a ↦ h a _ rfl)

variable {X : Scheme.{u}}

/-- If the sections of `N` over the basic opens of an affine open `U` are localizations of its
sections over `U`, then the restriction of `N` to `Spec Γ(X, U)` is quasi-coherent. -/
theorem isQuasicoherent_restrict_fromSpec (N : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (h : ∀ a : Γ(X, U),
      letI := moduleOfLE N (X.basicOpen_le a)
      IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a))) :
    (N.restrict hU.fromSpec).IsQuasicoherent := by
  refine isQuasicoherent_spec_of_isLocalizedModule _ fun a W hW ↦ ?_
  have hWb : (hU.fromSpec ⁻¹ᵁ X.basicOpen a) = PrimeSpectrum.basicOpen a :=
    hU.fromSpec_preimage_basicOpen a
  obtain rfl := hW.trans hWb.symm
  let := moduleOfLE N (X.basicOpen_le a)
  have hWimg : hU.fromSpec ''ᵁ (hU.fromSpec ⁻¹ᵁ X.basicOpen a) = X.basicOpen a := by
    rw [hWb, hU.fromSpec_image_basicOpen]
  have hTop : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec
  set ι₁ := (restrictSectionsEquiv N hU ⊤).trans
    (sectionsCongrSelf N hTop (fromSpec_image_le hU ⊤)) with hι₁
  set ι₂ := (restrictSectionsEquiv N hU (hU.fromSpec ⁻¹ᵁ X.basicOpen a)).trans
    (sectionsCongr N hWimg (fromSpec_image_le hU _) (X.basicOpen_le a)) with hι₂
  have h1 : IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a) ∘ₗ ι₁.toLinearMap) :=
    (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers a)
      ι₁.toLinearMap ι₁.bijective).mpr (h a)
  have heq : ι₂.toLinearMap ∘ₗ
      specRestrictₗ (N.restrict hU.fromSpec)
        (le_top (a := hU.fromSpec ⁻¹ᵁ X.basicOpen a)) =
      restrictₗ N (X.basicOpen_le a) ∘ₗ ι₁.toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ : ∃ y : Γ(N, hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)), y = x := ⟨x, rfl⟩
    change N.presheaf.map _ (N.presheaf.map _ y) = N.presheaf.map _ (N.presheaf.map _ y)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    rfl
  rw [← heq] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_left (S := Submonoid.powers a)
    ι₂.toLinearMap ι₂.bijective).mp h1

/-- **Quasi-coherence is detected by localization on basic opens.** A module whose sections over
each basic open of each affine open are the localization of its sections over that affine open
is quasi-coherent. -/
theorem isQuasicoherent_of_isLocalizedModule_restrictₗ (N : X.Modules)
    (h : ∀ (U : X.Opens), IsAffineOpen U → ∀ a : Γ(X, U),
      letI := moduleOfLE N (X.basicOpen_le a)
      IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a))) :
    N.IsQuasicoherent := by
  refine isQuasicoherent_of_presentations N (fun V : X.affineOpens ↦ (V : X.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) fun V ↦ ?_
  obtain ⟨U, hU'⟩ := V
  have hU : IsAffineOpen U := hU'
  have h1 : (N.restrict hU.fromSpec).IsQuasicoherent :=
    isQuasicoherent_restrict_fromSpec N hU (h U hU)
  have h2 : ((N.restrict hU.fromSpec).restrict hU.isoSpec.hom).IsQuasicoherent := inferInstance
  have iso : (N.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ N.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app N
  have : (N.restrict U.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso iso h2
  exact (nonempty_presentation_of_isoSpec hU.isoSpec _).some

end Stacks.AlgebraicGeometry.TorsionQuasicoherent

end
