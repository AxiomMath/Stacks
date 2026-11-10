module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Sheaf
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# The glued sheaf of a chart module system is quasi-coherent

Quasi-coherence is checked on each chart `V c` with a variant of the localization criterion
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`: the
sections over a basic open `D(a)` need to be the localization of the sections over `V c` only for
the `a` in a set whose basic opens form a basis of `V c`. For the glued sheaf those are the
refinements of `c`, over which the sections are the chart modules and the restriction maps are
localizations by the axiom of a chart module system.

## Main results

* `AlgebraicGeometry.isQuasicoherent_spec_of_isLocalizedModule_of_isBasis`: on `Spec R`,
  localization on a basis of basic opens suffices for quasi-coherence.
* `AlgebraicGeometry.isQuasicoherent_of_forall_exists_basis`: the same on an arbitrary scheme.
* `AlgebraicGeometry.ChartModuleSystem.isQuasicoherent_sheaf`: the glued sheaf is quasi-coherent.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

namespace AlgebraicGeometry

/-- **Quasi-coherence on `Spec R` from localization on a basis of basic opens.** If the basic opens
`D(a)`, `a ∈ s`, form a basis of the topology of `Spec R` and the sections of `M` over each of
them are the localization of its global sections away from `a`, then `M` is quasi-coherent. -/
theorem isQuasicoherent_spec_of_isLocalizedModule_of_isBasis {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (s : Set R)
    (hs : Opens.IsBasis (Set.range fun a : s => PrimeSpectrum.basicOpen (a : R)))
    (h : ∀ (a : R) (W : (Spec R).Opens), a ∈ s → W = PrimeSpectrum.basicOpen a →
      IsLocalizedModule.Away a (specRestrictₗ M (le_top (a := W)))) :
    M.IsQuasicoherent := by
  refine (isQuasicoherent_iff_isIso_fromTildeΓ M).mpr ?_
  rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
  let φ := modulesSpecToSheaf.map M.fromTildeΓ
  have htop : IsIso (φ.hom.app (op ⊤)) := by
    rw [← isIso_comp_left_iff (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) ⊤),
      Scheme.Modules.toOpen_fromTildeΓ_app]
    simpa using IsIso.id _
  refine TopCat.Sheaf.isIso_iff_isIso_basis (φ := φ) hs fun a => ?_
  refine ModuleCat.isIso_of_isLocalizedModule_comp (isLocalizing_tilde _ a.1) ?_
  rw [φ.hom.naturality]
  have : IsLocalizedModule (Submonoid.powers a.1)
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen a.1).leTop.op).hom :=
    h a.1 _ a.2 rfl
  exact IsLocalizedModule.of_linearEquiv_right _ _ (asIso (φ.hom.app (op ⊤))).toLinearEquiv

section Basis

variable {X : Scheme.{u}}

/-- Localization transfers along a commuting square with linear equivalences as horizontal maps. -/
private theorem isLocalizedModule_iff_of_comp_equiv_eq {R : Type*} [CommSemiring R]
    (S : Submonoid R) {M M' N N' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    [AddCommMonoid N] [AddCommMonoid N'] [Module R M] [Module R M'] [Module R N] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (e₁ : M ≃ₗ[R] N) (e₂ : M' ≃ₗ[R] N')
    (h : e₂.toLinearMap ∘ₗ f = g ∘ₗ e₁.toLinearMap) :
    IsLocalizedModule S f ↔ IsLocalizedModule S g := by
  rw [← IsLocalizedModule.comp_iff_of_bijective_left S e₂.toLinearMap e₂.bijective, h,
    IsLocalizedModule.comp_iff_of_bijective_right S e₁.toLinearMap e₁.bijective]

/-- If the sections of `N` over the basic opens `D(a)`, `a ∈ s`, of an affine open `U` are
localizations of its sections over `U`, and those basic opens form a basis of the topology of
`U`, then the restriction of `N` to `Spec Γ(X, U)` is quasi-coherent. -/
theorem isQuasicoherent_restrict_fromSpec_of_basis (N : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (s : Set Γ(X, U))
    (hs : ∀ y ∈ U, ∀ W : X.Opens, y ∈ W → ∃ a ∈ s, y ∈ X.basicOpen a ∧ X.basicOpen a ≤ W)
    (h : ∀ a ∈ s, letI := moduleOfLE N (X.basicOpen_le a)
      IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a))) :
    (N.restrict hU.fromSpec).IsQuasicoherent := by
  refine isQuasicoherent_spec_of_isLocalizedModule_of_isBasis _ s ?_ fun a W has hW => ?_
  · refine Opens.isBasis_iff_nbhd.mpr fun {W p} hp => ?_
    have hpU : hU.fromSpec p ∈ U := by
      have hp' : hU.fromSpec p ∈ Set.range hU.fromSpec := Set.mem_range_self p
      rwa [hU.range_fromSpec] at hp'
    obtain ⟨a, has, hya, haW⟩ := hs _ hpU (hU.fromSpec ''ᵁ W) ⟨p, hp, rfl⟩
    refine ⟨_, ⟨⟨a, has⟩, rfl⟩, ?_, ?_⟩
    · change p ∈ (PrimeSpectrum.basicOpen a : (Spec Γ(X, U)).Opens)
      rw [← hU.fromSpec_preimage_basicOpen]
      exact hya
    · change (PrimeSpectrum.basicOpen a : (Spec Γ(X, U)).Opens) ≤ W
      rw [← hU.fromSpec_preimage_basicOpen]
      exact (Scheme.Hom.preimage_mono _ haW).trans (hU.fromSpec.preimage_image_eq W).le
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
  have heq : ι₂.toLinearMap ∘ₗ
      specRestrictₗ (N.restrict hU.fromSpec)
        (le_top (a := hU.fromSpec ⁻¹ᵁ X.basicOpen a)) =
      restrictₗ N (X.basicOpen_le a) ∘ₗ ι₁.toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ : ∃ y : Γ(N, hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)), y = x := ⟨x, rfl⟩
    change N.presheaf.map _ (N.presheaf.map _ y) = N.presheaf.map _ (N.presheaf.map _ y)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    rfl
  exact (isLocalizedModule_iff_of_comp_equiv_eq (Submonoid.powers a) _ _ ι₁ ι₂ heq).mpr (h a has)

/-- **Quasi-coherence from localization on bases of basic opens of affine opens.** If every point
of `X` lies in an affine open `U` carrying a set `s` of functions whose basic opens form a basis of
the topology of `U`, and over each of which the sections of `N` are the localization of the
sections over `U`, then `N` is quasi-coherent. -/
theorem isQuasicoherent_of_forall_exists_basis (N : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, ∃ _ : IsAffineOpen U, x ∈ U ∧ ∃ s : Set Γ(X, U),
      (∀ y ∈ U, ∀ W : X.Opens, y ∈ W → ∃ a ∈ s, y ∈ X.basicOpen a ∧ X.basicOpen a ≤ W) ∧
      ∀ a ∈ s, letI := moduleOfLE N (X.basicOpen_le a)
        IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a))) :
    N.IsQuasicoherent := by
  choose U hU hxU s hs hloc using h
  refine isQuasicoherent_of_presentations N U
    (IsOpenCover.mk (top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩)) fun x => ?_
  have h1 : (N.restrict (hU x).fromSpec).IsQuasicoherent :=
    isQuasicoherent_restrict_fromSpec_of_basis N (hU x) (s x) (hs x) (hloc x)
  have iso : (N.restrict (hU x).fromSpec).restrict (hU x).isoSpec.hom ≅ N.restrict (U x).ι :=
    ((Scheme.Modules.restrictFunctorComp (hU x).isoSpec.hom (hU x).fromSpec).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (hU x).isoSpec_hom_fromSpec).app N
  have : (N.restrict (U x).ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U x).toScheme.ringCatSheaf).prop_of_iso iso inferInstance
  exact (nonempty_presentation_of_isoSpec (hU x).isoSpec _).some

end Basis

namespace ChartModuleSystem

variable {Y : Scheme.{u}} {I : Y.AffineChartIndex} (S : ChartModuleSystem I)

/-- The restriction of sections of the glued sheaf from a chart to a refinement `V e = D(a)` is
the localization away from `a`. -/
theorem isLocalizedModule_restrictₗ {e c : I.ι} (h : I.Refines e c) (a : Γ(Y, (I.V c).1))
    (ha : (I.V e).1 = Y.basicOpen a) :
    letI := moduleOfLE S.sheaf (I.le_of_refines h)
    IsLocalizedModule.Away a (restrictₗ S.sheaf (I.le_of_refines h)) := by
  let := moduleOfLE S.sheaf (I.le_of_refines h)
  let : Module Γ(Y, (I.V c).1) (S.M e) := Module.compHom _ (I.res h)
  have := S.isLocalizedModule_ρ h a ha
  let σe : S.M e ≃ₗ[Γ(Y, (I.V c).1)] Γ(S.sheaf, (I.V e).1) :=
    { (S.sectionsEquiv e).symm with
      map_smul' := fun r x => (S.sectionsEquiv e).symm.map_smul (I.res h r) x }
  have heq : restrictₗ S.sheaf (I.le_of_refines h) ∘ₗ (S.sectionsEquiv c).symm.toLinearMap =
      σe.toLinearMap ∘ₗ (S.ρ h).restrictScalarsAlong := by
    refine LinearMap.ext fun x => (S.sectionsEquiv e).injective ?_
    change S.sectionsEquiv e (S.sheaf.presheaf.map _ ((S.sectionsEquiv c).symm x)) =
      S.sectionsEquiv e ((S.sectionsEquiv e).symm (S.ρ h x))
    rw [sectionsEquiv_restrict, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact (isLocalizedModule_iff_of_comp_equiv_eq (Submonoid.powers a) _ _ (S.sectionsEquiv c).symm
    σe heq.symm).mp inferInstance

/-- `isLocalizedModule_restrictₗ`, for an open equal to the refinement. -/
theorem isLocalizedModule_restrictₗ_of_eq {e c : I.ι} (h : I.Refines e c) (a : Γ(Y, (I.V c).1))
    {W : Y.Opens} (hW : W ≤ (I.V c).1) (hWe : W = (I.V e).1) (ha : (I.V e).1 = Y.basicOpen a) :
    letI := moduleOfLE S.sheaf hW
    IsLocalizedModule.Away a (restrictₗ S.sheaf hW) := by
  subst hWe
  exact S.isLocalizedModule_restrictₗ h a ha

/-- **The glued sheaf of a chart module system is quasi-coherent.** On each chart `V c`, the
sections over the refinements of `c` — which form a basis of `V c` by basic opens — are the
localizations of the sections over `V c`. -/
instance isQuasicoherent_sheaf : S.sheaf.IsQuasicoherent := by
  refine isQuasicoherent_of_forall_exists_basis S.sheaf fun x => ?_
  obtain ⟨c, hc⟩ := I.exists_mem x
  refine ⟨(I.V c).1, (I.V c).2, hc, {a | ∃ e, I.Refines e c ∧ (I.V e).1 = Y.basicOpen a},
    fun y hy W hyW => ?_, fun a ⟨e, he, ha⟩ => ?_⟩
  · obtain ⟨e, he, hye, heW⟩ := I.exists_refines_le hy hyW
    obtain ⟨a, ha⟩ := I.exists_eq_basicOpen he
    exact ⟨a, ⟨e, he, ha⟩, ha ▸ hye, ha ▸ heW⟩
  · exact S.isLocalizedModule_restrictₗ_of_eq he a _ ha.symm ha

end ChartModuleSystem

end AlgebraicGeometry
