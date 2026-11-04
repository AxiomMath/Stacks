module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# Sections of birational universal homeomorphisms

Stacks Remark 0H5Y calls a locally Noetherian scheme `T` *weakly normal* if every birational
universal homeomorphism `T' ⟶ T` has a section. This file records that notion and proves that the
spectrum of an integrally closed domain has it: a universal homeomorphism is integral, hence
affine, and birationality identifies its ring with a subring of the fraction field integral over
the base, which is the base itself.

## Main definitions

* `AlgebraicGeometry.Scheme.HasBirationalUniversalHomeomorphismSections` — every birational
  universal homeomorphism to the scheme has a section.

## Main results

* `AlgebraicGeometry.Scheme.hasBirationalUniversalHomeomorphismSections_spec` — the spectrum of an
  integrally closed domain has the property.

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- **The weak normality of Stacks Remark 0H5Y.** A scheme `T` such that every birational
universal homeomorphism `T' ⟶ T` has a section. -/
def HasBirationalUniversalHomeomorphismSections (T : Scheme.{u}) : Prop :=
  ∀ ⦃T' : Scheme.{u}⦄ (g : T' ⟶ T), IsBirational g → UniversalHomeomorphism g →
    ∃ s : T ⟶ T', s ≫ g = 𝟙 T

/-- **The spectrum of an integrally closed domain is weakly normal** in the sense of Stacks Remark
0H5Y: every birational universal homeomorphism `g : T' ⟶ Spec A` has a section. The morphism `g`
is integral, so `T' = Spec A'` with `A ⟶ A'` integral; at a generic point of `T'` it induces an
isomorphism of local rings, through which `A'` maps to the fraction field of `A` with image
integral over `A`, hence contained in `A`. This map `A' ⟶ A` is a retraction of `A ⟶ A'`. -/
theorem hasBirationalUniversalHomeomorphismSections_spec (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] : HasBirationalUniversalHomeomorphismSections (Spec (.of A)) := by
  classical
  intro T' g hbir huh
  obtain ⟨hint, -, -⟩ := (universalHomeomorphism_iff_integral_universallyInjective_surjective g).mp
    huh
  have : IsAffine T' := isAffine_of_isAffineHom g
  set e := T'.isoSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (e.inv ≫ g)
  have hψint : ψ.hom.IsIntegral := by
    have : IsIntegralHom (Spec.map ψ) := by rw [hψ]; infer_instance
    exact IsIntegralHom.SpecMap_iff.mp this
  -- a generic point of `T'`, at which `g` is an isomorphism of local rings
  obtain ⟨ξ', hξ', -⟩ := hbir.1.surjOn
    (by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _ :
      genericPoint (Spec (.of A)) ∈ genericPoints (Spec (.of A)))
  set η := e.hom ξ'
  have hηξ : e.inv η = ξ' := by
    change (e.hom ≫ e.inv) ξ' = ξ'
    rw [Iso.hom_inv_id]
    rfl
  have hmem : e.inv η ∈ genericPoints T' := by rw [hηξ]; exact hξ'
  have hg : IsIso (g.stalkMap (e.inv η)) := hbir.2 _ hmem
  have : IsIso (e.inv.stalkMap η) := inferInstance
  have hstalk : IsIso ((Spec.map ψ).stalkMap η) := by
    rw [hψ, Scheme.Hom.stalkMap_comp]
    exact IsIso.comp_isIso' hg inferInstance
  -- the induced map of local rings is bijective
  set P := (η : PrimeSpectrum Γ(T', ⊤)).asIdeal
  set Q := (PrimeSpectrum.comap ψ.hom η).asIdeal
  have : P.IsPrime := PrimeSpectrum.isPrime (R := Γ(T', ⊤)) η
  have : Q.IsPrime := PrimeSpectrum.isPrime (R := A) (PrimeSpectrum.comap ψ.hom η)
  set L := Localization.localRingHom Q P ψ.hom rfl
  have hL : Function.Bijective L := by
    have h := Scheme.localRingHom_comp_stalkIso ψ η
    have hL' : CommRingCat.ofHom L = (Spec.stalkIso _ (PrimeSpectrum.comap ψ.hom η)).inv ≫
        (Spec.map ψ).stalkMap η ≫ (Spec.stalkIso _ η).hom := by
      rw [← h]
      simp
    have : IsIso (CommRingCat.ofHom L) := by
      rw [hL']
      exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hstalk inferInstance)
    exact (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom L)).mp this
  -- `A'` maps to the fraction field of `A`
  let K := FractionRing A
  let j : Localization.AtPrime Q →+* K :=
    IsLocalization.map K (RingHom.id A) (show Q.primeCompl ≤ (nonZeroDivisors A).comap _ from
      Q.primeCompl_le_nonZeroDivisors)
  let ι : Γ(T', ⊤) →+* K :=
    j.comp ((RingEquiv.ofBijective L hL).symm.toRingHom.comp
      (algebraMap Γ(T', ⊤) (Localization.AtPrime P)))
  have hcomp : ι.comp ψ.hom = algebraMap A K := by
    ext a
    change j ((RingEquiv.ofBijective L hL).symm (algebraMap _ _ (ψ a))) = _
    exact (congrArg j ((RingEquiv.ofBijective L hL).symm_apply_eq.mpr
      (Localization.localRingHom_to_map Q P ψ.hom rfl a).symm)).trans (IsLocalization.map_eq _ a)
  -- its image is integral over `A`, hence in `A`
  have hrange : ∀ a', ι a' ∈ (algebraMap A K).range := by
    intro a'
    obtain ⟨p, hp, hpa⟩ := hψint a'
    have hint' : _root_.IsIntegral A (ι a') := by
      refine ⟨p, hp, ?_⟩
      rw [← hcomp, ← Polynomial.hom_eval₂, hpa, map_zero]
    exact (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).mp hint'
  let eA : A ≃+* (algebraMap A K).range :=
    RingEquiv.ofBijective (algebraMap A K).rangeRestrict
      ⟨fun _ _ hab => IsFractionRing.injective A K (congrArg Subtype.val hab),
        (algebraMap A K).rangeRestrict_surjective⟩
  let ρ : Γ(T', ⊤) →+* A := eA.symm.toRingHom.comp (ι.codRestrict _ hrange)
  have hρψ : ∀ a, ρ (ψ a) = a := fun a =>
    eA.symm_apply_eq.mpr (Subtype.ext (RingHom.congr_fun hcomp a))
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ e.inv, ?_⟩
  rw [Category.assoc, ← hψ, ← Spec.map_comp]
  have hid : ψ ≫ CommRingCat.ofHom ρ = 𝟙 _ := by
    ext a
    exact hρψ a
  rw [hid, Spec.map_id]

end AlgebraicGeometry.Scheme

end
