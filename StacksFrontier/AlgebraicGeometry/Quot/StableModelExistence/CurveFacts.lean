module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.StableFibres
public import StacksFrontier.AlgebraicGeometry.Curves.Models.Reduction
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal

/-!
# The generic fibre of a stable model

Let `R` be a discrete valuation ring with fraction field `K`, and let `X ⟶ Spec R` be a model of
a smooth scheme `C` over `K` which is a stable family of curves of genus `g`. Then `C` is a smooth
projective curve over `K` with `H⁰(C, 𝒪_C) = K` and of genus at least two, and the fibre of `X`
over the generic point of `Spec R` is smooth. These are the hypotheses on `C` which the source of
Stacks 0E97 lists and which follow from `X` being a stable model.

The generic fibre `X_K` of a stable family is proper, with `H⁰ = K`, genus at least two and of
dimension one (`AlgebraicGeometry.IsStableFamilyOfSchemesOfGenus.genericFibre`); `C ≅ X_K` over
`K`. Being smooth and proper with `H⁰ = K`, `C` is geometrically integral (Stacks 0FD3), hence a
curve; a proper scheme of dimension one over a field is H-projective (Stacks 0A26).

## Main results

* `Stacks.Models.curveFacts_of_isStableFamilyOfSchemesOfGenus`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDiscreteValuationRing R] in
/-- The image of the point of `Spec K` in `Spec R` is the generic point `⊥`. -/
theorem specMap_algebraMap_closedPoint_eq_bot :
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (IsLocalRing.closedPoint K) =
      (⊥ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)

/-- **The generic fibre of a stable model.** Let `C` be a smooth scheme over `K` and `X ⟶ Spec R`
a model of `C` which is a stable family of curves of genus `g`. Then `C` is a proper curve over
`K`, projective and H-projective, with `H⁰(C, 𝒪_C) = K` and genus at least two, and the fibre of
`X` over the generic point of `Spec R` is smooth. -/
theorem curveFacts_of_isStableFamilyOfSchemesOfGenus {B : BigFppfSite.{u}}
    {hZ : B.Contains integerBase} {hR : B.Contains (Spec (.of R))} {g : ℕ} {C X : Scheme.{u}}
    (C_to_K : C ⟶ Spec (.of K)) [Smooth C_to_K] {p : X ⟶ Spec (.of R)}
    {e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    (hmod : IsModel C_to_K p e) (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR) :
    IsCurve K C_to_K ∧ IsProper C_to_K ∧
      IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop) ∧ IsProjective C_to_K ∧
      Stacks.HProjective.IsHProjective C_to_K ∧ 2 ≤ genus C_to_K ∧
      Smooth (p.fiberToSpecResidueField (⊥ : PrimeSpectrum R)) := by
  obtain ⟨hgen, hH0⟩ := hst.genericFibre (K := K)
  have he : e.hom ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C_to_K :=
    hmod.2.2.2
  have : IsProper p := hst.isProper
  have hsnd : pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))) = e.inv ≫ C_to_K := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hw : e.inv ≫ C_to_K =
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ Spec.map (𝟙 _) := by
    rw [Spec.map_id, Category.comp_id, hsnd]
  have hprop : IsProper C_to_K := by
    rw [← he]
    infer_instance
  have hglob : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop) :=
    isIso_ΓSpecIso_inv_comp_appTop_of_iso (𝟙 _) C_to_K _ e.inv hw hH0
  -- the dimension of the generic fibre
  have := isIso_descResidueField_algebraMap_of_isFractionRing R K
  have : Nonempty (pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme.{u}) :=
    nonempty_of_isIso_globalSections K _ hH0
  obtain ⟨hdimK, -⟩ := topologicalKrullDim_pullback_eq_one_and_hasAtWorstNodalSingularities p
    (hst.isAtWorstNodalOfRelativeDimensionOne fun _ hF => hF.1.1)
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hdimC : topologicalKrullDim C = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).trans hdimK
  -- `C` is geometrically integral, hence a curve
  have : GeometricallyIntegral C_to_K :=
    ((isIso_globalSections_tfae_geometricallyConnected_irreducible_integral K C_to_K
      (isGeometricallyNormal_of_smooth C_to_K)).out 1 4).1 hglob
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton C_to_K
  -- projectivity (Stacks 0A26)
  have hPM : IsProjectiveMorphism C_to_K :=
    HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
      C_to_K hdimC.le
  -- the fibre over the generic point
  have hsm : Smooth (p.fiberToSpecResidueField
      ((Spec.map (CommRingCat.ofHom (algebraMap R K))) (IsLocalRing.closedPoint K))) := by
    obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField p
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    have : Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
      rw [hsnd]
      infer_instance
    rw [← hE]
    infer_instance
  rw [specMap_algebraMap_closedPoint_eq_bot] at hsm
  exact ⟨{ topologicalKrullDim_eq_one := hdimC }, hprop, hglob, hPM.isProjective, hPM,
    (HasGenusTwoNoRationalTailNoRationalBridge.of_iso (𝟙 _) C_to_K _ e.inv hw hgen).1, hsm⟩

end Stacks.Models

end
