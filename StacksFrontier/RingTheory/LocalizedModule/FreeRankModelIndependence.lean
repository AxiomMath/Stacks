module

public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.Algebra.Module.RingEquivTransport

/-!
# Freeness of a fixed rank for a localized module is model-independent

A localization of a module is determined up to isomorphism by the submonoid it inverts, and so
is the localization of the base ring, so whether the localized module is free of a prescribed
finite rank over the localized ring depends on neither choice of model. This file records that,
and the companion statement for an isomorphism of the base ring.

## Main results

* `Module.nonempty_linearEquiv_pi_of_isLocalizedModule_of_isLocalization`: freeness of rank `r`
  of a localized module does not depend on the models chosen for the localized ring and the
  localized module; the models may lie in arbitrary universes.
* `Module.nonempty_linearEquiv_pi_localizedModule_away_of_ringEquiv`: freeness of rank `r` of an
  away-localization transports along an isomorphism of the base ring together with a compatible
  additive isomorphism of the module.

## Implementation notes

The first statement is the `Module.Free`-of-fixed-rank companion of
`Module.FinitePresentation.of_isLocalizedModule_of_isLocalization`, and is shorter: a linear
equivalence with a finite free module may be moved across the two comparison maps
`IsLocalization.algEquiv` and `IsLocalizedModule.linearEquiv` while only base-ring linear, and
`LinearEquiv.extendScalarsOfIsLocalization` then upgrades the composite, because a base-ring
linear map between two modules over a localization of the base is automatically linear over that
localization.

The second statement is deduced from the first by viewing the target data over the source ring
along the isomorphism: `IsLocalization.of_ringEquiv_left` makes the away-localization of the
target ring a localization of the source ring, and `IsLocalizedModule.of_ringEquiv` makes the
localization map of the target module a localization of the source module.
-/

@[expose] public section

universe u u' v v' w w'

/-- **Freeness of a fixed finite rank is a property of the localization, not of its model.** Let
`p` be a submonoid of `S`, let `A₁` and `A₂` be two localizations of `S` at `p`, and let
`f₁ : M →ₗ[S] N₁` and `f₂ : M →ₗ[S] N₂` exhibit two localizations of `M` at `p`. If `N₁` is free
of rank `r` over `A₁` then `N₂` is free of rank `r` over `A₂`. -/
public theorem Module.nonempty_linearEquiv_pi_of_isLocalizedModule_of_isLocalization
    {S : Type u} [CommRing S] (p : Submonoid S)
    {A₁ : Type u'} [CommRing A₁] [Algebra S A₁] [IsLocalization p A₁]
    {A₂ : Type v} [CommRing A₂] [Algebra S A₂] [IsLocalization p A₂]
    {M : Type v'} [AddCommGroup M] [Module S M]
    {N₁ : Type w} [AddCommGroup N₁] [Module S N₁] [Module A₁ N₁] [IsScalarTower S A₁ N₁]
    (f₁ : M →ₗ[S] N₁) [IsLocalizedModule p f₁]
    {N₂ : Type w'} [AddCommGroup N₂] [Module S N₂] [Module A₂ N₂] [IsScalarTower S A₂ N₂]
    (f₂ : M →ₗ[S] N₂) [IsLocalizedModule p f₂] (r : ℕ)
    (h : Nonempty (N₁ ≃ₗ[A₁] (Fin r → A₁))) :
    Nonempty (N₂ ≃ₗ[A₂] (Fin r → A₂)) := by
  obtain ⟨e⟩ := h
  let eA : A₂ ≃ₐ[S] A₁ := IsLocalization.algEquiv p A₂ A₁
  let g : N₂ ≃ₗ[S] N₁ := IsLocalizedModule.linearEquiv p f₂ f₁
  let ePi : (Fin r → A₁) ≃ₗ[S] (Fin r → A₂) :=
    LinearEquiv.piCongrRight fun _ ↦ eA.symm.toLinearEquiv
  let comp : N₂ ≃ₗ[S] (Fin r → A₂) :=
    g ≪≫ₗ (LinearEquiv.restrictScalars S e) ≪≫ₗ ePi
  exact ⟨comp.extendScalarsOfIsLocalization p A₂⟩

/-- **Freeness of a fixed finite rank of an away-localization transports along a bijective
structure map.** Let `C` be a `B`-algebra whose structure map is bijective, let `X` be a
`B`-module, `Y` a `C`-module and `φ : X ≃ₗ[B] Y` a `B`-linear isomorphism. If `X` becomes free
of rank `r` after inverting `g : B`, then `Y` becomes free of rank `r` after inverting the image
of `g` in `C`. -/
public theorem Module.nonempty_linearEquiv_pi_localizedModule_away_of_bijective
    {B : Type u} [CommRing B] {C : Type u'} [CommRing C] [Algebra B C]
    (hbij : Function.Bijective (algebraMap B C))
    {X : Type v} [AddCommGroup X] [Module B X]
    {Y : Type v'} [AddCommGroup Y] [Module B Y] [Module C Y] [IsScalarTower B C Y]
    (φ : X ≃ₗ[B] Y) (g : B) (r : ℕ)
    (h : Nonempty (LocalizedModule (Submonoid.powers g) X ≃ₗ[Localization.Away g]
      (Fin r → Localization.Away g))) :
    Nonempty (LocalizedModule (Submonoid.powers (algebraMap B C g)) Y
        ≃ₗ[Localization.Away (algebraMap B C g)]
      (Fin r → Localization.Away (algebraMap B C g))) := by
  set e : B ≃+* C := RingEquiv.ofBijective (algebraMap B C) hbij with he
  have hmap : (Submonoid.powers g).map e = Submonoid.powers (algebraMap B C g) :=
    Submonoid.map_powers e g
  have hA : ∀ b : B, algebraMap B (Localization.Away (algebraMap B C g)) b
      = algebraMap C (Localization.Away (algebraMap B C g)) (e b) := fun b ↦ by
    rw [IsScalarTower.algebraMap_apply B C (Localization.Away (algebraMap B C g))]
    rfl
  have : IsLocalization (Submonoid.powers g) (Localization.Away (algebraMap B C g)) :=
    IsLocalization.of_ringEquiv_left e hmap hA
  have hp : ∀ s : B, s ∈ Submonoid.powers g ↔ e s ∈ Submonoid.powers (algebraMap B C g) := by
    refine fun s ↦ ⟨fun hs ↦ hmap ▸ Submonoid.mem_map_of_mem _ hs, fun hs ↦ ?_⟩
    obtain ⟨y, hy, hye⟩ := hmap.symm.le hs
    exact e.injective hye ▸ hy
  let f₂ : X →ₗ[B] LocalizedModule (Submonoid.powers (algebraMap B C g)) Y :=
    (LinearMap.restrictScalars B
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap B C g)) Y)) ∘ₗ φ.toLinearMap
  have : IsLocalizedModule (Submonoid.powers g) f₂ :=
    IsLocalizedModule.of_ringEquiv e hp
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap B C g)) Y) f₂
      φ.toAddEquiv (AddEquiv.refl _)
      (fun b x ↦ by
        change φ (b • x) = (algebraMap B C b) • φ x
        rw [IsScalarTower.algebraMap_smul, map_smul])
      (fun b m ↦ by
        change b • m = (algebraMap B C b) • m
        rw [IsScalarTower.algebraMap_smul]) fun _ ↦ rfl
  exact Module.nonempty_linearEquiv_pi_of_isLocalizedModule_of_isLocalization
    (Submonoid.powers g) (LocalizedModule.mkLinearMap (Submonoid.powers g) X) f₂ r h

end
