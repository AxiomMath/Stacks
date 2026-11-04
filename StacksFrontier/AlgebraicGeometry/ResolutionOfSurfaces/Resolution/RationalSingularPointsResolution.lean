module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularPointBlowupChainResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepCompletedStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUpChainComp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUpsAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.RationalStalk
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoCriteria
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary

/-!
# Resolving rational singularities by normalized blowups

This file carries out the last paragraph of the proof of [Stacks, Tag 0BGM]: a singular point of
a normal surface whose local ring defines a rational singularity is resolved by normalized
blowups, granted [Stacks, Tag 0BBV] and [Stacks, Tag 0BGE].

Let `R` be an excellent two-dimensional local normal domain defining a rational singularity and
having a dualizing complex. Tag 0BBV gives a sequence of blowups in singular closed points with
normal stages, `Y ⟶ Spec R`, such that `Y` is Gorenstein. The local rings of `Y` at its singular
points are again excellent (they are essentially of finite type over `R`), define rational
singularities ([Stacks, Tag 0BG0]) and are Gorenstein, so Tag 0BGE resolves each of them by
blowups in singular closed points with normal stages; such a sequence is a sequence of normalized
blowups. The singular locus of `Y` is finite (`Y` is J-2 over the excellent `R`), so the local
resolutions globalize over `Y`, and composing with the sequence `Y ⟶ Spec R` resolves `Spec R`.

The two inputs enter as hypotheses `h0BBV` and `h0BGE`, in the form in which the proof uses
them; nothing here carries an attribute.

## Main results

* `AlgebraicGeometry.exists_isDualizingComplex_stalk_of_locallyOfFiniteType`: the local rings of a
  scheme locally of finite type over a Noetherian ring with a dualizing complex have dualizing
  complexes ([Stacks, Tag 0BFR] (5)).
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isExcellent`: an excellent
  two-dimensional local normal domain defining a rational singularity and having a dualizing
  complex has a resolution by normalized blowups, granted Tags 0BBV and 0BGE.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_stalk_of_definesRationalSingularity`: the
  same at a singular point of a normal modification of the spectrum of a two-dimensional complete
  local normal domain. This is the hypothesis `hrational` of
  `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_rational` and `rat` of
  the proof of [Stacks, Tag 0BGN].

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **The local rings of a scheme locally of finite type over a Noetherian ring with a dualizing
complex have dualizing complexes.** An affine open around the point has a ring of sections of
finite type over the base, and the local ring is a localization of it ([Stacks, Tag 0BFR] (5),
twice). -/
theorem exists_isDualizingComplex_stalk_of_locallyOfFiniteType (B : Type u) [CommRing B]
    [IsNoetherianRing B] (hB : ∃ K : DerivedCategory (ModuleCat.{u} B),
      Dualizing.IsDualizingComplex K)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [LocallyOfFiniteType f] (x : X) :
    ∃ (h : IsNoetherianRing (X.presheaf.stalk x))
      (L : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))),
      @Dualizing.IsDualizingComplex _ _ h _ L := by
  obtain ⟨K, hK⟩ := hB
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let φ : B →+* Γ(X, V) :=
    ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appLE ⊤ V le_top).hom
  have hφ : φ.FiniteType := by
    have h₁ : (f.appLE ⊤ V le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    exact h₁.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).inv).2)
  let : Algebra B Γ(X, V) := φ.toAlgebra
  have hft : Algebra.FiniteType B Γ(X, V) := hφ
  obtain ⟨hN, L, hL⟩ := Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType
    (Dualizing.isEssentiallyOfFiniteType_of_finiteType hft) K hK
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hess : IsEssentiallyOfFiniteType Γ(X, V) (X.presheaf.stalk x)
      (algebraMap Γ(X, V) (X.presheaf.stalk x)) :=
    ⟨Γ(X, V), inferInstance, Algebra.id _, inferInstance,
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl, inferInstance,
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl, hloc⟩
  exact Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType hess L hL

/-- The local ring of a normal scheme at a singular point of dimension two is not the local ring
at the generic point. -/
theorem ne_genericPoint_of_ringKrullDim_stalk_eq_two {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  rintro rfl
  have h0 : ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 :=
    ringKrullDim_eq_zero_of_field X.functionField
  rw [hx] at h0
  exact absurd h0 (by norm_num)

/-- **The singular points of a Gorenstein normal modification of a rational singularity are
resolved by normalized blowups**, granted [Stacks, Tag 0BGE]. Let `R` be an excellent
two-dimensional local normal domain defining a rational singularity, `W ⟶ Spec R` a modification
with `W` normal, and `w` a singular point of `W` at which the local ring is Gorenstein. Then the
spectrum of that local ring has a resolution by normalized blowups. -/
theorem hasResolutionByNormalizedBlowUps_stalk_of_isGorensteinLocalRing
    (h0BGE : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalDomain (AdicCompletion (maximalIdeal A) A) → Dualizing.IsGorensteinLocalRing A →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsRegular Y)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalDomain R]
    (hexc : IsExcellent R) (hdim : ringKrullDim R = 2) (hrat : DefinesRationalSingularity R)
    {W : Scheme.{u}} [IsNormal W] [IsLocallyNoetherian W] (k : W ⟶ Spec (.of R))
    (hk : IsModification k) (w : W)
    (hw : w ∈ singularLocus W)
    (hgor : Dualizing.IsGorensteinLocalRing (W.presheaf.stalk w)) :
    HasResolutionByNormalizedBlowUps (Spec (W.presheaf.stalk w)) := by
  have : IsProper k := hk.isProper
  have : IsIntegral W := hk.source_isIntegral
  have : IsLocallyNoetherian (Spec (.of R)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hdimW : topologicalKrullDim W = 2 := 
    (topologicalKrullDim_eq_of_isModification_spec R k hk).trans hdim
  have hw2 := ringKrullDim_stalk_eq_two_of_mem_singularLocus W hdimW.le w hw
  have hwclosed := isClosed_singleton_of_mem_singularLocus W hdimW.le w hw
  have : IsNormalDomain (W.presheaf.stalk w) := ⟨IsNormal.stalk_isDomain w, IsNormal.stalk_normal w⟩
  have hexcw := isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent R hexc k w
  have hNagata : IsNagataRing (W.presheaf.stalk w) := isNagataRing_of_isQuasiExcellent hexcw.1
  have hratw := definesRationalSingularity_stalk_of_isModification R hdim hrat k hk w hwclosed
    (ne_genericPoint_of_ringKrullDim_stalk_eq_two w hw2)
  have hcompl := isNormalDomain_adicCompletion_of_isExcellent _ hexcw
    (IsNormalRing.of_isIntegrallyClosed _)
  obtain ⟨Y, f, hchain, hreg⟩ := h0BGE (W.presheaf.stalk w) hNagata hw2 hratw hcompl hgor
  have : IsNormal (Spec (.of (W.presheaf.stalk w))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed _)
  exact hasResolutionByNormalizedBlowUps_of_singularPointBlowupChain (fun _ h ↦ h)
    (isNagataScheme_spec_of_isNagataRing _ hNagata) hchain hreg

/-- The local rings of a scheme isomorphic to a Gorenstein scheme are Gorenstein. -/
private theorem isGorensteinLocalRing_stalk_of_isIso {N Y : Scheme.{u}} [IsLocallyNoetherian N]
    [IsGorenstein Y] (φ : N ⟶ Y) [IsIso φ] (y : N) :
    Dualizing.IsGorensteinLocalRing (N.presheaf.stalk y) :=
  (Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff
    (asIso (φ.stalkMap y)).commRingCatIsoToRingEquiv).1 (IsGorenstein.isGorensteinLocalRing (φ y))

/-- **An excellent two-dimensional local normal domain defining a rational singularity and having
a dualizing complex has a resolution by normalized blowups**, granted [Stacks, Tag 0BBV] (as
`h0BBV`) and [Stacks, Tag 0BGE] (as `h0BGE`). This is the last paragraph of the proof of
[Stacks, Tag 0BGM]. -/
theorem hasResolutionByNormalizedBlowUps_of_isExcellent
    (h0BBV : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y)
    (h0BGE : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalDomain (AdicCompletion (maximalIdeal A) A) → Dualizing.IsGorensteinLocalRing A →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsRegular Y)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalDomain R]
    (hexc : IsExcellent R) (hdim : ringKrullDim R = 2) (hrat : DefinesRationalSingularity R)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} R), Dualizing.IsDualizingComplex K) :
    HasResolutionByNormalizedBlowUps (Spec (.of R)) := by
  have hNagataR : IsNagataRing R := isNagataRing_of_isQuasiExcellent hexc.1
  have hNagataS : IsNagataScheme (Spec (.of R)) := isNagataScheme_spec_of_isNagataRing _ hNagataR
  have : IsLocallyNoetherian (Spec (.of R)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsNormal (Spec (.of R)) := isNormal_spec_of_isNormalRing
    (IsNormalRing.of_isIntegrallyClosed R)
  have hdimS : topologicalKrullDim (Spec (.of R)) = 2 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R).trans hdim
  have hS := SemistableReduction.finite_irreducibleComponents_of_locallyNoetherian (Spec (.of R))
  obtain ⟨Y, f, hchain, hgor⟩ := h0BBV R hNagataR hdim hrat hdual
  obtain ⟨-, X, g, e, hseq, he⟩ :=
    exists_normalizedBlowUpSeq_of_singularPointBlowupChain (fun _ h ↦ h) hchain
  obtain ⟨W, k, e', hW, he'⟩ := exists_normalizedBlowUpChain_of_normalizedBlowUpSeq hNagataS hS hseq
  have hk : IsModification k := isModification_of_normalizedBlowUpChain hdimS hW
  have : IsProper k := hk.isProper
  have : IsIntegral W := hk.source_isIntegral
  have : IsNormal W := hW.isNormal
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian k
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace k
  have : IsNoetherian W := {}
  have hdimW : topologicalKrullDim W = 2 := 
    (topologicalKrullDim_eq_of_isModification_spec R k hk).trans hdim
  have hWc := SemistableReduction.finite_irreducibleComponents_of_locallyNoetherian W
  let N := W.normalizationScheme hWc
  let ν := Scheme.normalization W hWc
  have : IsIso ν := (Scheme.isIso_normalization_iff_isNormal W hWc).2 inferInstance
  have : IsNormal N := Scheme.isNormal_normalizationScheme W hWc
  have : IsLocallyNoetherian N := isLocallyNoetherian_of_isOpenImmersion ν
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace ν
  have : IsNoetherian N := {}
  have hνk : IsModification (ν ≫ k) :=
    ⟨(isBirational_of_iso (asIso ν)).comp hk.isBirational, inferInstance,
      IsIntegral.of_isIso (inv ν)⟩
  have hdimN : topologicalKrullDim N ≤ 2 := by
    rw [topologicalKrullDim_eq_of_isModification_spec R (ν ≫ k) hνk, hdim]
  have hJ2 : Scheme.IsJ2 N := Scheme.isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian
    ((Scheme.isJ2_Spec_iff R).mpr hexc.1.2.2) (ν ≫ k)
  have hsing : (singularLocus N).Finite := finite_singularLocus_of_isJ2 N hdimN hJ2
  have hWres : HasResolutionByNormalizedBlowUps W :=
    hasResolutionByNormalizedBlowUps_of_local W hWc hdimW
      (Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType k hNagataS) hWc)
      hsing fun y hy ↦
        hasResolutionByNormalizedBlowUps_stalk_of_isGorensteinLocalRing h0BGE R hexc hdim hrat
          (ν ≫ k) hνk y hy (isGorensteinLocalRing_stalk_of_isIso (ν ≫ (e ≪≫ e').inv) y)
  exact hasResolutionByNormalizedBlowUps_of_chain hW hWres

/-- **The singular points of a normal modification of a two-dimensional complete local normal
domain, at which the local ring defines a rational singularity, are resolved by normalized
blowups**, granted [Stacks, Tag 0BBV] (as `h0BBV`) and [Stacks, Tag 0BGE] (as `h0BGE`). The local
ring is excellent and has a dualizing complex, being essentially of finite type over the complete
base ([Stacks, Tags 07QW and 0BFR]).

This is the hypothesis `hrational` of
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_rational`. -/
theorem hasResolutionByNormalizedBlowUps_stalk_of_definesRationalSingularity
    (h0BBV : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y)
    (h0BGE : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalDomain (AdicCompletion (maximalIdeal A) A) → Dualizing.IsGorensteinLocalRing A →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsRegular Y)
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B] (hdimB : ringKrullDim B = 2)
    (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of B)) (hg : IsModification g) (z : Z)
    (hz : z ∈ singularLocus Z) (hrat : DefinesRationalSingularity (Z.presheaf.stalk z)) :
    HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z)) := by
  have : IsProper g := hg.isProper
  have : IsIntegral Z := hg.source_isIntegral
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have hdimZ : topologicalKrullDim Z = 2 := 
    (topologicalKrullDim_eq_of_isModification_spec B g hg).trans hdimB
  have : IsNormalDomain (Z.presheaf.stalk z) := ⟨IsNormal.stalk_isDomain z, IsNormal.stalk_normal z⟩
  obtain ⟨_, L, hL⟩ := exists_isDualizingComplex_stalk_of_locallyOfFiniteType B
    (Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal B) g z
  exact hasResolutionByNormalizedBlowUps_of_isExcellent h0BBV h0BGE (Z.presheaf.stalk z)
    (isExcellent_stalk_of_locallyOfFiniteType_of_isPrecomplete B g z)
    (ringKrullDim_stalk_eq_two_of_mem_singularLocus Z hdimZ.le z hz) hrat ⟨L, hL⟩

end AlgebraicGeometry

end
