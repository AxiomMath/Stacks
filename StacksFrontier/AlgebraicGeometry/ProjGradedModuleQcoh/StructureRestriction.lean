module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjLocalizedRingMap

/-!
# Restriction of the structure sheaf of Proj between standard opens

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and let `f`, `g` be homogeneous of positive degree
with `D₊(g) ⊆ D₊(f)`. Mathlib's `AlgebraicGeometry.Proj.awayToSection` identifies the
degree-zero localization `A₍f₎` with the sections of the structure sheaf over `D₊(f)`. This
file checks that under those identifications the restriction map of the structure sheaf is
the canonical degree-zero ring map `A₍f₎ → A₍g₎`.

The square is checked pointwise: a section over `D₊(f)` is the family of its images in the
degree-zero localizations at the points, so both routes become two maps out of `A_f` into a
localization of `A` at a homogeneous prime, and these agree because both are `A`-algebra maps
and `f` is already invertible in the target.

## Main results

* `ProjectiveSpectrum.awayToSection_degreeZeroRingMap`: the restriction square commutes.
* `ProjectiveSpectrum.val_mapId`: enlarging the denominator submonoid of a degree-zero
  fraction is the canonical localization map on the underlying localizations.
* `ProjectiveSpectrum.map_localizedRingMap`: the two canonical maps from `A_f` into a common
  further localization agree.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

namespace ProjectiveSpectrum

open CategoryTheory Opposite

variable {S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Enlarging the denominator submonoid of a degree-zero fraction is, on the underlying
localizations, the canonical localization map. -/
public lemma val_mapId {P Q : Submonoid S} (h : P ≤ Q)
    (z : HomogeneousLocalization 𝒜 P) :
    HomogeneousLocalization.val (HomogeneousLocalization.mapId 𝒜 h z) =
      IsLocalization.map (M := P) (S := Localization P) (T := Q) (Localization Q)
        (RingHom.id S) (by intro w hw; simpa using h hw)
        (HomogeneousLocalization.val z) := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  show HomogeneousLocalization.val
      (HomogeneousLocalization.map (.id 𝒜) (by intro w hw; simpa using h hw)
        (HomogeneousLocalization.mk c)) = _
  simp only [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

/-- Both canonical maps into a common further localization agree: the one through `S_g` after
the restriction `S_f → S_g`, and the one directly out of `S_f`. -/
public lemma map_localizedRingMap (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    {T : Submonoid S} (h₁ : Submonoid.powers g ≤ T.comap (RingHom.id S))
    (h₂ : Submonoid.powers f ≤ T.comap (RingHom.id S)) (w : Localization.Away f) :
    IsLocalization.map (M := Submonoid.powers g) (S := Localization.Away g)
        (T := T) (Localization T) (RingHom.id S) h₁
        ((localizedRingMap 𝒜 f g hf hg hfg) w) =
      IsLocalization.map (M := Submonoid.powers f) (S := Localization.Away f)
        (T := T) (Localization T) (RingHom.id S) h₂ w := by
  have key : (IsLocalization.map (M := Submonoid.powers g) (S := Localization.Away g)
        (T := T) (Localization T) (RingHom.id S) h₁).comp
        (localizedRingMap 𝒜 f g hf hg hfg).toRingHom =
      IsLocalization.map (M := Submonoid.powers f) (S := Localization.Away f)
        (T := T) (Localization T) (RingHom.id S) h₂ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext s
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgHom.commutes, IsLocalization.map_eq, RingHom.id_apply]
  exact DFunLike.congr_fun key w

/-- Restriction of the structure sheaf of `Proj` from `D₊(f)` to `D₊(g)` is, under the canonical
maps from the degree-zero localizations, the degree-zero ring map of Tag 01M4. -/
public theorem awayToSection_degreeZeroRingMap (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    CommRingCat.ofHom (degreeZeroRingMap 𝒜 f g hf hg hfg).toRingHom ≫
        AlgebraicGeometry.Proj.awayToSection 𝒜 g =
      AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hfg).op := by
  ext z
  apply Subtype.ext
  funext p
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  show HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr p.2)
      (degreeZeroRingMap 𝒜 f g hf hg hfg z) =
    HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr (hfg p.2)) z
  apply HomogeneousLocalization.val_injective
  rw [val_mapId, val_mapId, val_degreeZeroRingMap, map_localizedRingMap]

end ProjectiveSpectrum
