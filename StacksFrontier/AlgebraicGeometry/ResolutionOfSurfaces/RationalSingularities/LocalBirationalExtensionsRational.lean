module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyExactness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.RationalStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SpreadOutModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.FlatBaseChangeFirstCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge
public import StacksFrontier.RingTheory.Nagata.EssFiniteTypeNormalModel
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineChart
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalSurfaceSingularPointsFinite
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.RationalSingularityResolution
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# Rational singularities pass to local birational extensions

[Stacks, Tag 0BG0]: let `(A, 𝔪)` be a two-dimensional local normal Nagata domain defining a
rational singularity and `A ⊆ B` a local extension of domains with the same fraction field which
is essentially of finite type, with `B` normal of dimension two. Then `B` defines a rational
singularity.

## Main results

* `AlgebraicGeometry.definesRationalSingularity_of_essFiniteType`: [Stacks, Tag 0BG0].

## Implementation notes

The source realizes `B` as the local ring `𝒪_{X, x}` of a normal proper modification
`X ⟶ Spec A` at a closed point. Here `B` is the localization of an integrally closed affine
blowup algebra `A[J/t]` at a prime
(`Stacks.Blowup.exists_affineBlowup_localization_of_essFiniteType`); the chart `Spec A[J/t]` of
the blowup of `Spec A` in `J` is a normal open, so the normalization of the blowup is an
isomorphism over it, and `B` is the local ring of the normalized blowup at the corresponding
point, which is closed because its local ring is two-dimensional.

The local-ring form `AlgebraicGeometry.definesRationalSingularity_stalk_of_isModification` then
concludes: for a normal modification `f : X ⟶ Spec A` and a closed point `x ∈ X` other than the
generic point, `𝒪_{X, x}` defines a rational singularity. Its proof follows the source. A normal
modification of `Spec 𝒪_{X, x}` spreads out to a proper `g : X' ⟶ X` which is an isomorphism
away from `x` ([Stacks, Tags 0B3X, 0BFN]), and `X'` is a normal modification of `Spec A` (Step 4,
`AlgebraicGeometry.isNormal_and_isModification_of_isPullback_fromSpecStalk`). So
`H¹(X', 𝒪_{X'}) = 0`, and the vanishing descends to the given modification
(`AlgebraicGeometry.isZeroFirstStructureSheafCohomology_of_isPullback_fromSpecStalk`, by
Mayer–Vietoris in place of the first conclusion of [Stacks, Tag 0AXF] and flat base change).

## References

* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0B3X](https://stacks.math.columbia.edu/tag/0B3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open GlueingNearPoint

/-- The ideal sheaf on `Spec A` of a nonzero ideal of a domain is nonzero. -/
theorem ofIdealTop_ne_bot {A : Type u} [CommRing A] {J : Ideal A} (hJ : J ≠ ⊥) :
    Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom J) ≠ ⊥ := by
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  intro h
  have htop := congrArg
    (fun I : (Spec (CommRingCat.of A)).IdealSheafData =>
      I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩) h
  have hbot : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom J = ⊥ := by
    simpa [Scheme.IdealSheafData.ofIdealTop_ideal] using htop
  exact hJ ((Ideal.map_eq_bot_iff_of_injective hinj).mp hbot)

/-- **Stacks Project, Tag 0BG0.** Let `(A, 𝔪)` be a two-dimensional local normal Nagata domain
defining a rational singularity, and let `A ⟶ B` be a local extension of normal local domains
with the same fraction field `K`, essentially of finite type, with `dim B = 2`. Then `B` defines
a rational singularity. -/
@[stacks 0BG0]
theorem definesRationalSingularity_of_essFiniteType (A B : Type u) [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (K : Type u) [Field K] [Algebra A K] [Algebra B K]
    [IsScalarTower A B K] [IsFractionRing A K] [IsFractionRing B K] (hN : IsNagataRing A)
    (hA : ringKrullDim A = 2) (hB : ringKrullDim B = 2) (hft : Algebra.EssFiniteType A B)
    (hrat : DefinesRationalSingularity A) : DefinesRationalSingularity B := by
  have : IsNoetherianRing A := hN.1
  obtain ⟨J, t, ht, ht0, hint, P, hP, ⟨eB⟩⟩ :=
    Stacks.Blowup.exists_affineBlowup_localization_of_essFiniteType A B K hN hft
  have hJ : J ≠ ⊥ := fun h => ht0 (by rw [h] at ht; exact (Submodule.mem_bot A).mp ht)
  set ℐ := Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom J) with hℐ
  have hℐ0 : ℐ ≠ ⊥ := ofIdealTop_ne_bot hJ
  have : IsNoetherianRing (CommRingCat.of A) := ‹IsNoetherianRing A›
  have : IsIntegral (blowUp ℐ) := isIntegral_blowUp _ hℐ0
  have hX₀ := finite_irreducibleComponents_blowUp_spec A ℐ
  have : IsFinite (Scheme.normalization (blowUp ℐ) hX₀) :=
    Scheme.isFinite_normalization
      (isNagataScheme_of_locallyOfFiniteType (blowUpToBase ℐ)
        (isNagataScheme_spec_of_isNagataRing A hN)) hX₀
  let X := Scheme.normalizationScheme (blowUp ℐ) hX₀
  let ν : X ⟶ blowUp ℐ := Scheme.normalization (blowUp ℐ) hX₀
  let f : X ⟶ Spec (.of A) := ν ≫ blowUpToBase ℐ
  have hf : IsModification f :=
    ⟨(Scheme.isBirational_normalization _ _).comp (isBirational_blowUpToBase _ hℐ0),
      inferInstance, inferInstance⟩
  have : IsNormal X := Scheme.isNormal_normalizationScheme _ _
  have : IsIntegral X := hf.source_isIntegral
  obtain ⟨e⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase (R := A) (K := J)
  let j : Spec (CommRingCat.of (affineBlowup J t)) ⟶ blowUp ℐ :=
    Stacks.Blowup.specAffineBlowupι J t ht ≫ e.hom.left
  have hei : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have heo : IsOpenImmersion e.hom.left := @IsOpenImmersion.of_isIso _ _ e.hom.left hei
  have : IsOpenImmersion j :=
    @IsOpenImmersion.comp _ _ _ (Stacks.Blowup.specAffineBlowupι J t ht) e.hom.left _ heo
  have : IsDomain (affineBlowup J t) :=
    Function.Injective.isDomain ((Stacks.Blowup.awayToFractionField (K := K) t ht0).toRingHom.comp
      (affineBlowup J t).val.toRingHom)
      ((Stacks.Blowup.awayToFractionField_injective t ht0).comp Subtype.val_injective)
  let W : (blowUp ℐ).Opens := j.opensRange
  have hW : IsNormal W.toScheme := by
    have : IsNormal (Spec (CommRingCat.of (affineBlowup J t))) :=
      isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)
    exact isNormal_of_iso (Scheme.Hom.isoOpensRange j).symm
  have hiso : IsIso (ν ∣_ W) := Scheme.isIso_normalization_restrict_of_isNormal _ hX₀ W hW
  let p₀ : Spec (CommRingCat.of (affineBlowup J t)) := ⟨P, hP⟩
  have hx₀W : j p₀ ∈ W := ⟨p₀, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x' : (ν ⁻¹ᵁ W).toScheme, (ν ∣_ W) x' = ⟨j p₀, hx₀W⟩ :=
    (ν ∣_ W).surjective _
  let x : X := x'.1
  have hxW : x ∈ ν ⁻¹ᵁ W := x'.2
  have hx : ν x = j p₀ := by
    have h := congrArg Subtype.val hx'
    rwa [morphismRestrict_base_coe] at h
  have hνst : IsIso (ν.stalkMap x) := isIso_stalkMap_of_isIso_morphismRestrict ν hiso hxW
  let eStalk : ↥(X.presheaf.stalk x) ≃+* B := by
    let : Algebra (affineBlowup J t)
        ((Spec (CommRingCat.of (affineBlowup J t))).presheaf.stalk p₀) :=
      StructureSheaf.stalkAlgebra _ p₀
    have : IsLocalization.AtPrime
        ((Spec (CommRingCat.of (affineBlowup J t))).presheaf.stalk p₀) P :=
      StructureSheaf.IsLocalization.to_stalk _ p₀
    let e₁ : Localization.AtPrime P ≃+*
        (Spec (CommRingCat.of (affineBlowup J t))).presheaf.stalk p₀ :=
      (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) _).toRingEquiv
    let e₂ := (asIso (j.stalkMap p₀)).commRingCatIsoToRingEquiv
    let e₃ := ((blowUp ℐ).presheaf.stalkCongr (Inseparable.of_eq hx)).commRingCatIsoToRingEquiv
    let e₄ := (asIso (ν.stalkMap x)).commRingCatIsoToRingEquiv
    exact ((e₄.symm.trans e₃).trans (e₂.trans e₁.symm)).trans eB.symm
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsProper f := hf.isProper
  have hdimX : topologicalKrullDim X = 2 := by
    rw [hf.1.topologicalKrullDim_eq_of_isClosedMap f.isClosedMap]
    change topologicalKrullDim (PrimeSpectrum A) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hA]
  have hdimx : ringKrullDim (X.presheaf.stalk x) = 2 := by
    rw [ringKrullDim_eq_of_ringEquiv eStalk, hB]
  have hx : IsClosed ({x} : Set X) :=
    isClosed_singleton_of_two_le_ringKrullDim_stalk X hdimX.le x hdimx.ge
  have hxη : let := hf.source_isIntegral; x ≠ genericPoint X := by
    intro _ h
    have h2 := hdimx
    rw [h] at h2
    change ringKrullDim X.functionField = 2 at h2
    rw [ringKrullDim_eq_zero_of_field] at h2
    exact (by norm_num : (0 : WithBot ℕ∞) ≠ 2) h2
  exact (definesRationalSingularity_stalk_of_isModification A hA hrat f hf x hx hxη).of_ringEquiv
    eStalk

end AlgebraicGeometry

end
