module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.ExcellentStalks
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.NormalSurfaceAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUpChainComp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE

/-!
# Resolving a rational surface singularity by normalized blowups

Let `C` be a two-dimensional excellent Noetherian local normal domain with a dualizing complex
which defines a rational singularity. The proofs of [Stacks, Tags 0BGM and 0BGN] resolve such a
ring in two passes: [Stacks, Tag 0BBV] blows up singular closed points until every local ring is
Gorenstein, and then each remaining singular point, a rational double point, is resolved by
[Stacks, Tag 0BGE]; the local rings of the intermediate scheme still define rational
singularities by [Stacks, Tag 0BG0]. This file carries out that assembly.

## Main results

* `AlgebraicGeometry.DefinesRationalSingularity.of_ringEquiv`: defining a rational singularity
  is invariant under ring isomorphisms.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_definesRationalSingularity`: such a
  `C` has a resolution of singularities by normalized blowups.

## Implementation notes

The three tags the assembly consumes, [Stacks, Tags 0BBV, 0BGE and 0BG0], are the hypotheses
`hgorenstein`, `hdoublePoint` and `hrationalExt`. Every local ring met is essentially of finite
type over `C`, hence excellent, Nagata, with a dualizing complex and with normal completion
(`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.ExcellentStalks`).

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Defining a rational singularity is invariant under ring isomorphisms.** -/
theorem DefinesRationalSingularity.of_ringEquiv {A B : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (e : A ≃+* B) (h : DefinesRationalSingularity A) :
    DefinesRationalSingularity B := by
  intro X _ f hf
  let φ : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso φ := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (RingEquiv.toCommRingCatIso e).isIso_hom
    infer_instance
  have : IsProper f := hf.isProper
  exact h X (f ≫ φ) ⟨hf.1.comp (isBirational_of_iso (asIso φ)), inferInstance, hf.source_isIntegral⟩

/-- The local ring of a local ring `C` at its closed point is `C` itself. -/
noncomputable def ringEquivStalkOfAsIdealEq (C : Type u) [CommRing C] [IsLocalRing C]
    (p : PrimeSpectrum C) (hp : p.asIdeal = maximalIdeal C) :
    C ≃+* (Spec (.of C)).presheaf.stalk p :=
  ((IsLocalization.atUnits C p.asIdeal.primeCompl (S := Localization.AtPrime p.asIdeal)
    fun _ hx => IsLocalRing.notMem_maximalIdeal.mp (hp ▸ hx)).toRingEquiv).trans
    (Spec.stalkIso (.of C) p).symm.commRingCatIsoToRingEquiv

/-- **Rational surface singularities have resolutions by normalized blowups.** Let `C` be a
two-dimensional excellent Noetherian local normal domain with a dualizing complex which defines
a rational singularity. Then `Spec C` has a resolution of singularities by normalized blowups.

This is the part of the proof of [Stacks, Tag 0BGM] after the rationality of the singular points
has been established. -/
theorem hasResolutionByNormalizedBlowUps_of_definesRationalSingularity
    (hgorenstein : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y))
    (hdoublePoint : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalRing (AdicCompletion (maximalIdeal A) A) →
      (letI := hN.1; Dualizing.IsGorensteinLocalRing A) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y)
    (hrationalExt : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [CommRing B]
      [IsLocalRing B] [IsNormalDomain B] [Algebra A B] [IsLocalHom (algebraMap A B)]
      (K : Type u) [Field K] [Algebra A K] [Algebra B K] [IsScalarTower A B K]
      [IsFractionRing A K] [IsFractionRing B K], IsNagataRing A → ringKrullDim A = 2 →
      ringKrullDim B = 2 → Algebra.EssFiniteType A B → DefinesRationalSingularity A →
      DefinesRationalSingularity B)
    (C : Type u) [CommRing C] [IsLocalRing C] [IsNormalDomain C] (hexc : IsExcellent C)
    (hdual : letI : IsNoetherianRing C := hexc.1.1
      ∃ K : DerivedCategory (ModuleCat.{u} C), Dualizing.IsDualizingComplex K)
    (hdim : ringKrullDim C = 2) (hrat : DefinesRationalSingularity C) :
    HasResolutionByNormalizedBlowUps (Spec (.of C)) := by
  have hN : IsNagataRing C := isNagataRing_of_isQuasiExcellent hexc.1
  have : IsNoetherianRing C := hexc.1.1
  have : IsNormal (Spec (.of C)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed C)
  have : IsLocallyNoetherian (Spec (.of C)) := isLocallyNoetherian_Spec.mpr inferInstance
  obtain ⟨Y, f, hchain, hgor⟩ := hgorenstein C hN hdim hrat hdual
  have hseq := normalizedBlowUpSeq_of_normalizedPointBlowupChain
    (hchain.mono (Set.subset_univ _))
  obtain ⟨hfmod, _, _, hYdim⟩ := isModification_of_normalizedBlowUpSeq C hN hdim hseq
  have : IsIntegral Y := hfmod.source_isIntegral
  have : IsProper f := hfmod.isProper
  have : IsDominant f := hfmod.isBirational.isDominant
  have hsing := finite_singularLocus_of_locallyOfFiniteType_of_isExcellent hexc f hYdim.le
  have hYres : HasResolutionByNormalizedBlowUps Y := by
    refine hasResolutionByNormalizedBlowUps_of_isNormal_of_singularLocus Y hYdim hsing
      fun y hy => ?_
    have hyc : IsClosed ({y} : Set Y) := isClosed_singleton_of_mem_singularLocus Y hYdim.le y hy
    have hfyc : IsClosed ({f.base y} : Set (Spec (.of C))) := by
      simpa only [Set.image_singleton] using f.isClosedMap _ hyc
    have hp : (f.base y).asIdeal = maximalIdeal C :=
      IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hfyc)
    let A := (Spec (.of C)).presheaf.stalk (f.base y)
    let e : C ≃+* A := ringEquivStalkOfAsIdealEq C (f.base y) hp
    have : IsNormalDomain A := ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
    have hAexc : IsExcellent A :=
      isExcellent_stalk_of_locallyOfFiniteType hexc (𝟙 (Spec (.of C))) (f.base y)
    have hAN : IsNagataRing A := isNagataRing_of_isQuasiExcellent hAexc.1
    have hAdim : ringKrullDim A = 2 := (ringKrullDim_eq_of_ringEquiv e).symm.trans hdim
    have hArat : DefinesRationalSingularity A := hrat.of_ringEquiv e
    let O := Y.presheaf.stalk y
    have : IsNormalDomain O := ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
    have hOexc : IsExcellent O := isExcellent_stalk_of_locallyOfFiniteType hexc f y
    have hON : IsNagataRing O := isNagataRing_of_isQuasiExcellent hOexc.1
    have hOdim : ringKrullDim O = 2 :=
      ringKrullDim_stalk_eq_two_of_mem_singularLocus Y hYdim.le y hy
    let : Algebra A O := (f.stalkMap y).hom.toAlgebra
    let : Algebra A Y.functionField := stalkFunctionFieldAlgebraOfHom f y
    have : IsScalarTower A O Y.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsFractionRing A Y.functionField :=
      isFractionRing_stalk_of_isBirational f hfmod.isBirational y
    have : IsLocalHom (algebraMap A O) := inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
    have hOrat : DefinesRationalSingularity O :=
      hrationalExt A O Y.functionField hAN hAdim hOdim (LocallyOfFiniteType.stalkMap f y) hArat
    have hOcompl : IsNormalRing (AdicCompletion (maximalIdeal O) O) :=
      isNormalRing_adicCompletion_of_isExcellent_of_isNormalRing O hOexc
        (IsNormalRing.of_isIntegrallyClosed O)
    obtain ⟨_, hOgor⟩ := hgor y
    obtain ⟨Z, g, hchainZ, hreg⟩ := hdoublePoint O hON hOdim hOrat hOcompl hOgor
    have : IsNormal (Spec (.of O)) :=
      isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed O)
    exact hasResolutionByNormalizedBlowUps_of_normalizedBlowUpSeq
      (isNagataScheme_spec_of_isNagataRing O hON)
      (normalizedBlowUpSeq_of_normalizedPointBlowupChain (hchainZ.mono (Set.subset_univ _)))
      hreg
  obtain ⟨W, g, e, hchainW, he⟩ := exists_normalizedBlowUpChain_of_normalizedBlowUpSeq
    (isNagataScheme_spec_of_isNagataRing C hN)
    (finite_irreducibleComponents_of_isCompact (Spec (.of C))) hseq
  have : IsProper g := hchainW.isProper
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNormal W := isNormal_of_iso (Y := W) e.symm
  exact hasResolutionByNormalizedBlowUps_of_chain hchainW (hYres.of_iso e)

end AlgebraicGeometry

end
