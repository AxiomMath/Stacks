module

public import StacksFrontier.Homology.RelativelyPerfect.Fibrewise
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.Composition
public import StacksFrontier.Homology.TorAmplitude.Nilpotent
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso

/-!
# Tor amplitude at a generization from the derived fibre at a specialization

Let `A` be flat and of finite presentation over `R`, presented by `d` variables, let `q ⊆ q₀` be
primes of `A` and let `M` be a complex of `A`-modules which is pseudo-coherent. Write `p₀` for the
prime of `R` below `q₀`. Suppose that the derived base change of `M_{q₀}`, read over `R_{p₀}`,
along a ring map `h : R_{p₀} → R₀` has Tor amplitude in `[a, b]` over `R₀`, where `R₀` carries a
module `N` which, read over `R_{p₀}`, is the residue field `κ(p₀)`. Then `M_q` has Tor amplitude in
`[a - d, b]` over `R_{q ∩ R}`.

The hypothesis gives the vanishing of the cohomology of `M_{q₀} ⊗ᴸ_{R_{p₀}} κ(p₀)` outside
`[a, b]` by the projection formula, so Stacks 0DJH bounds the Tor amplitude of `M_{q₀}` over `R`
by `[a - d, b]`; the bound passes to the localisation `M_q` of `M_{q₀}`, which is a flat base
change, and then from `R` to `R_{q ∩ R}`.

## Main results

* `PseudoCoherence.hasTorAmplitudeAt_of_derivedFibre_of_le`: the statement above.

## References

* [Stacks Project, Lemma 15.85.9 (Tag 0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 37.71.3 (Tag 0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars StacksDraft.TorAmplitude

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Tor amplitude at the canonical derived tensor product, unfolded to the defining vanishing of
`StacksDraft.TorAmplitude.HasTorAmplitude` at the canonical certificate. -/
theorem hasTorAmplitudeCanonical_iff_hasTorAmplitude (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    HasTorAmplitudeCanonical R K a b ↔
      HasTorAmplitude (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
        (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R) K a b :=
  (hasTorAmplitudeIn_canonical_iff R K a b).symm.trans
    (hasTorAmplitudeIn_iff_hasTorAmplitude _ _ _ K a b)

/-! ### Change-of-rings isomorphisms on derived categories -/

/-- Restricting scalars twice along a composable pair is restricting along the composite, on
derived categories. -/
def restrictScalarsCompObjIso {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (K : DerivedCategory (ModuleCat.{u} T)) :
    (ModuleCat.restrictScalars f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars g).mapDerivedCategory.obj K) ≅
      (ModuleCat.restrictScalars (g.comp f)).mapDerivedCategory.obj K :=
  let F := ModuleCat.restrictScalars.{u} f
  let G := ModuleCat.restrictScalars.{u} g
  let H := ModuleCat.restrictScalars.{u} (g.comp f)
  let P := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  F.mapDerivedCategory.mapIso (G.mapDerivedCategory.mapIso e.symm) ≪≫
    F.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app P) ≪≫
    F.mapDerivedCategoryFactors.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp' f g (g.comp f) rfl).symm (ComplexShape.up ℤ)).app P) ≪≫
    (H.mapDerivedCategoryFactors.app P).symm ≪≫ H.mapDerivedCategory.mapIso e

/-- Deriving extension of scalars along `c` after restricting along a ring isomorphism `ε` is
deriving extension of scalars along `c ∘ ε⁻¹`. -/
def totalDerivedExtensionScalarsRestrictScalarsIso {R₁ R₂ R₀ : Type u} [CommRing R₁]
    [CommRing R₂] [CommRing R₀] (ε : R₁ ≃+* R₂) (c : R₁ →+* R₀)
    (Y : DerivedCategory (ModuleCat.{u} R₂)) :
    (totalDerivedExtensionScalars.{u, u, u} c).functor.obj
        ((ModuleCat.restrictScalars ε.toRingHom).mapDerivedCategory.obj Y) ≅
      (totalDerivedExtensionScalars.{u, u, u} (c.comp ε.symm.toRingHom)).functor.obj Y :=
  have hc : (c.comp ε.symm.toRingHom).comp ε.toRingHom = c := by
    ext r
    simp
  (eqToIso (congrArg (fun φ : R₁ →+* R₀ => (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
      ((ModuleCat.restrictScalars ε.toRingHom).mapDerivedCategory.obj Y)) hc)).symm ≪≫
    ((totalDerivedExtensionScalarsComp.{u, u} ε.toRingHom
      (c.comp ε.symm.toRingHom)).app _).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u} (c.comp ε.symm.toRingHom)).functor.mapIso
      ((totalDerivedRestrictExtendScalarsSelfIso.{u, u} ε).app Y)

/-- A surjection of local rings identifies the residue fields: the residue field of the target,
read over the source, is the residue field of the source. -/
def restrictScalarsResidueFieldIso {P R₀ : Type u} [CommRing P] [IsLocalRing P]
    [CommRing R₀] [IsLocalRing R₀] (h : P →+* R₀) (hh : Function.Surjective h) :
    (ModuleCat.restrictScalars h).obj (ModuleCat.of R₀ (IsLocalRing.ResidueField R₀)) ≅
      ModuleCat.of P (IsLocalRing.ResidueField P) := by
  let N := (ModuleCat.restrictScalars h).obj (ModuleCat.of R₀ (IsLocalRing.ResidueField R₀))
  let ψ : P →ₗ[P] N := LinearMap.toSpanSingleton P N (show IsLocalRing.ResidueField R₀ from 1)
  have hψ : ∀ r : P, (ψ r : IsLocalRing.ResidueField R₀) = IsLocalRing.residue R₀ (h r) :=
    fun r => (Algebra.smul_def (h r) (1 : IsLocalRing.ResidueField R₀)).trans (by
      rw [mul_one, IsLocalRing.ResidueField.algebraMap_eq])
  have hψs : Function.Surjective ψ := fun x => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, rfl⟩ := hh y
    exact ⟨r, hψ r⟩
  have hmax : (IsLocalRing.maximalIdeal R₀).comap h = IsLocalRing.maximalIdeal P :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective h hh (K := IsLocalRing.maximalIdeal R₀))
  have hkerψ : LinearMap.ker ψ = IsLocalRing.maximalIdeal P := by
    ext r
    rw [LinearMap.mem_ker, hψ, ← hmax, Ideal.mem_comap, ← IsLocalRing.ker_residue,
      RingHom.mem_ker]
    exact Iff.rfl
  let φ : P →ₗ[P] IsLocalRing.ResidueField P := Algebra.linearMap P _
  have hkerφ : LinearMap.ker φ = IsLocalRing.maximalIdeal P := by
    ext r
    rw [LinearMap.mem_ker, ← IsLocalRing.ker_residue, RingHom.mem_ker]
    rfl
  exact ((ψ.quotKerEquivOfSurjective hψs).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (hkerψ.trans hkerφ.symm) ≪≫ₗ
    φ.quotKerEquivOfSurjective IsLocalRing.residue_surjective).toModuleIso

/-- Tor amplitude of a complex `K`, from canonical Tor amplitude of an isomorphic derived object. -/
private theorem hasTorAmplitude_of_iso_canonical {S : Type u} [CommRing S]
    {X : DerivedCategory (ModuleCat.{u} S)} {K : CochainComplex (ModuleCat.{u} S) ℤ}
    (e : X ≅ DerivedCategory.Q.obj K) {a b : ℤ} (hX : HasTorAmplitudeCanonical S X a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b :=
  (AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
    _ _ _).mp (AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e _ _ hX)

/-- Tor amplitude of `M_{q₀}` over `R` gives Tor amplitude of `M` over `R` at any prime
`q ≤ q₀`. -/
private theorem hasTorAmplitudeAt_of_hasTorAmplitude_localization_of_le
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q₀ q : Ideal A) [q₀.IsPrime] [q.IsPrime] (hq : q ≤ q₀)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (hq₀ : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap R (Localization.AtPrime q₀))).obj
        ((CochainComplex.extendScalars (algebraMap A (Localization.AtPrime q₀))).obj M)) a b) :
    HasTorAmplitudeAt R M q a b := by
  let Aq₀ := Localization.AtPrime q₀
  let Aq := Localization.AtPrime q
  -- Localising further from `q₀` to `q`.
  have hle : q₀.primeCompl ≤ q.primeCompl := fun x hx hxq => hx (hq hxq)
  let _ : Algebra Aq₀ Aq :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Aq₀ Aq q₀.primeCompl q.primeCompl hle
  have : IsScalarTower A Aq₀ Aq :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Aq₀ Aq q₀.primeCompl
      q.primeCompl hle
  have : IsLocalization (q.primeCompl.map (algebraMap A Aq₀)) Aq :=
    IsLocalization.isLocalization_of_submonoid_le Aq₀ Aq q₀.primeCompl q.primeCompl hle
  have : Module.Flat Aq₀ Aq := IsLocalization.flat Aq (q.primeCompl.map (algebraMap A Aq₀))
  have : IsScalarTower R Aq₀ Aq := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R A Aq, IsScalarTower.algebraMap_eq R A Aq₀,
      IsScalarTower.algebraMap_eq A Aq₀ Aq, RingHom.comp_assoc])
  have eM : (CochainComplex.extendScalars (algebraMap Aq₀ Aq)).obj
      ((CochainComplex.extendScalars (algebraMap A Aq₀)).obj M) ≅
      (CochainComplex.extendScalars (algebraMap A Aq)).obj M :=
    ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp (algebraMap A Aq₀)
      (algebraMap Aq₀ Aq)) (ComplexShape.up ℤ)).app M).symm ≪≫
      eqToIso (by
        rw [← IsScalarTower.algebraMap_eq A Aq₀ Aq]
        rfl)
  exact hasTorAmplitudeAt_of_hasTorAmplitude_extendScalars R A M q _ _ <|
    hasTorAmplitude_of_iso_canonical
      (DerivedCategory.Q.mapIso ((CochainComplex.restrictScalars (algebraMap R Aq)).mapIso eM)) <|
    (AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
      _ _ _).mpr (hasTorAmplitude_restrictScalars_extendScalars_of_flat R Aq₀ Aq _ _ _ hq₀)

/-- Tor amplitude over `R` of the derived localization of `M` at `q₀` gives Tor amplitude of `M`
over `R` at any prime `q ≤ q₀`. -/
private theorem hasTorAmplitudeAt_of_hasTorAmplitudeCanonical_localization_of_le
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q₀ q : Ideal A) [q₀.IsPrime] [q.IsPrime] (hq : q ≤ q₀)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (hM : HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars ((algebraMap A (Localization.AtPrime q₀)).comp
        (algebraMap R A))).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A (Localization.AtPrime q₀))).functor.obj (DerivedCategory.Q.obj M))) a b) :
    HasTorAmplitudeAt R M q a b := by
  let Aq₀ := Localization.AtPrime q₀
  -- The bound read on the complex `M_{q₀}`, over `R`.
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A Aq₀)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Aq₀ q₀.primeCompl))
  let Mq₀ := (CochainComplex.extendScalars (algebraMap A Aq₀)).obj M
  let τ := (algebraMap A Aq₀).comp (algebraMap R A)
  have hτ : τ = algebraMap R Aq₀ := (IsScalarTower.algebraMap_eq R A Aq₀).symm
  let e₁ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A Aq₀)).functor.obj
      (DerivedCategory.Q.obj M) ≅ DerivedCategory.Q.obj Mq₀ :=
    (Dualizing.totalDerivedExtensionScalarsIsoExtendScalars (algebraMap A Aq₀)).app _ ≪≫
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A Aq₀)).mapDerivedCategoryFactors.app M
  have hq₀ : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars τ).obj Mq₀) a b :=
    hasTorAmplitude_of_iso_canonical
      ((ModuleCat.restrictScalars τ).mapDerivedCategory.mapIso e₁ ≪≫
        (ModuleCat.restrictScalars τ).mapDerivedCategoryFactors.app Mq₀) hM
  rw [hτ] at hq₀
  exact hasTorAmplitudeAt_of_hasTorAmplitude_localization_of_le q₀ q hq M _ _ hq₀

/-- **Tor amplitude at a generization from the derived fibre at a specialization.** Let `A` be
flat and of finite presentation over `R`, presented by `d` variables, let `q ⊆ q₀` be primes of
`A`, and let `M` be a complex of `A`-modules which is pseudo-coherent. Let `h : R_{p₀} → R₀` be a
ring map, `p₀ = q₀ ∩ R`, and let `N` be an `R₀`-module which, read over `R_{p₀}`, is the residue
field `κ(p₀)`. If the derived base change along `h` of `M_{q₀}`, read over `R_{p₀}`, has Tor
amplitude in `[a, b]` over `R₀`, then `M_q` has Tor amplitude in `[a - d, b]` over `R_{q ∩ R}`. -/
theorem hasTorAmplitudeAt_of_derivedFibre_of_le
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (d : ℕ) (presentation : MvPolynomial (Fin d) R →ₐ[R] A)
    (hpresentation : Function.Surjective presentation)
    (q₀ q : Ideal A) [q₀.IsPrime] [q.IsPrime] (hq : q ≤ q₀)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M)) (a b : ℤ)
    {R₀ : Type u} [CommRing R₀] (h : Localization.AtPrime (q₀.under R) →+* R₀)
    (N : ModuleCat.{u} R₀)
    (eN : (ModuleCat.restrictScalars h).obj N ≅
      ModuleCat.of (Localization.AtPrime (q₀.under R)) (q₀.under R).ResidueField)
    (hfib :
      letI : Algebra (Localization.AtPrime (q₀.under R)) (Localization.AtPrime q₀) :=
        Localization.AtPrime.algebraOfLiesOver (q₀.under R) q₀
      HasTorAmplitudeCanonical R₀
        ((totalDerivedExtensionScalars.{u, u, u} h).functor.obj
          ((ModuleCat.restrictScalars
            (algebraMap (Localization.AtPrime (q₀.under R))
              (Localization.AtPrime q₀))).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (Localization.AtPrime q₀))).functor.obj
                (DerivedCategory.Q.obj M)))) a b) :
    HasTorAmplitudeAt R M q (a - (d : ℤ)) b := by
  let : Algebra (Localization.AtPrime (q₀.under R)) (Localization.AtPrime q₀) :=
    Localization.AtPrime.algebraOfLiesOver (q₀.under R) q₀
  let Rp := Localization.AtPrime (q₀.under R)
  let Aq₀ := Localization.AtPrime q₀
  let Y := (ModuleCat.restrictScalars (algebraMap Rp Aq₀)).mapDerivedCategory.obj
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A Aq₀)).functor.obj
      (DerivedCategory.Q.obj M))
  let Dh := totalDerivedExtensionScalars.{u, u, u} h
  let cmp : DerivedCategory.Q ⋙ Dh.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q := Dh.comparison
  have : Dh.functor.IsLeftDerivedFunctor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{u} Rp) (ComplexShape.up ℤ)) := Dh.isLeftDerived
  -- The cohomology of `M_{q₀} ⊗ᴸ_{R_{p₀}} κ(p₀)` vanishes outside `[a, b]`.
  have hfibre : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Rp) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Rp).tensor.obj Y).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Rp) 0).obj
            (ModuleCat.of Rp (q₀.under R).ResidueField)))) := by
    intro i hi
    have h0 := (hasTorAmplitudeCanonical_iff_hasTorAmplitude R₀ _ a b).mp hfib N i
      (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)
    exact (isZero_homology_derivedTensor_restrictScalars_of_derivedExtensionScalars h
      Dh.functor cmp
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Rp)
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R₀) Y N i h0).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Rp) i).mapIso
      ((((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Rp).tensor.obj Y).mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Rp) 0).mapIso eN)).symm))
  -- Stacks 0DJH at `q₀`.
  have h0DJH : HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars ((algebraMap A Aq₀).comp (algebraMap R A))).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A Aq₀)).functor.obj
          (DerivedCategory.Q.obj M))) (a - (d : ℤ)) b :=
    (hasTorAmplitudeCanonical_iff_hasTorAmplitude R _ _ b).mpr <|
    hasTorAmplitude_localization_of_isZero_homology_fibre d presentation hpresentation q₀
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R)
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Rp).tensor
      (canonicalTensorComparison Rp) (canonicalTensorIsLeftDerived Rp)
      (DerivedCategory.Q.obj M) hM a b hfibre
  exact hasTorAmplitudeAt_of_hasTorAmplitudeCanonical_localization_of_le q₀ q hq M _ _ h0DJH

end PseudoCoherence

end
