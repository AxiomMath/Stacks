module

public import StacksFrontier.AlgebraicGeometry.Divisors.ExceptionalDivisorTrivialSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationIsoInCodimensionOne
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.BlowUpStage
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.GorensteinBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.RationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalDualizingSheafNormalized
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Minimal

/-!
# [Stacks, Tag 0EA2], second sentence: for a minimal resolution, `E = 0`

Let `A` be a two-dimensional Noetherian normal local Nagata domain with a dualizing module `ω_A`
and `f : X ⟶ Spec(A)` a resolution with `ω_X ≅ 𝒪_X(E)`, `E` an effective Cartier divisor on the
exceptional fibre. By the first sentence `A` is a rational singularity and `ω_A ≅ A`, so `A` is
Gorenstein and `Spec(A)` is resolved by a chain of blowups `g : Y ⟶ Spec(A)` in rational double
points ([Stacks, Tag 0BGE]). Each blowup has trivial twisted inverse image
(`hasTrivialTwistedInverseImage_blowUpToBase`, the repeated application of [Stacks, Tag 0B64]),
hence `g^×(𝒪[0]) ≅ 𝒪_Y[0]`. If `f` is minimal, `g = k ≫ f` with `k` a modification which is an
isomorphism over an open `V ⊆ X` containing every point of codimension at most one; flat base
change along `V ⟶ X` gives `f^×(𝒪[0])|_V ≅ 𝒪_V[0]`, so `ω_X|_V = H^{-2}(f^×(ω_A[2]))|_V ≅ 𝒪_V`,
and `𝒪_X(E)` trivial in codimension one forces `E = 0`
(`Stacks.Divisors.eq_top_of_nonempty_pullback_iso_unit`).

## Main results

* `DualizingDivisor.eq_top_of_isMinimalResolution_of_relativeDualizingModule_iso`: if `f` is a
  minimal resolution and `ω_X ≅ 𝒪_X(E)`, then `E = 0`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory Stacks.Duality DerivedCategory IsLocalRing

universe u

namespace AlgebraicGeometry.DualizingDivisor

/-- `A` in degree `-n`, sheafified, is `𝒪_{Spec A}[0]⟦n⟧`. -/
noncomputable def unitQCShiftIso (A : Type u) [CommRing A] (n : ℤ) :
    (unitQC (Spec (.of A)))⟦n⟧ ≅ (derivedTilde (CommRingCat.of A)).obj
      ((singleFunctor (ModuleCat.{u} A) (-n)).obj (ModuleCat.of A A)) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (((ObjectProperty.ι _).commShiftIso n).app (unitQC (Spec (.of A))) ≪≫
      ((DerivedCategory.singleFunctors (Spec (CommRingCat.of A)).Modules).shiftIso n (-n) 0
        (by omega)).app ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A A)) ≪≫
      (derivedTildeSingleIso (CommRingCat.of A) (ModuleCat.of A A) (-n)).symm)

/-- **[Stacks, Tag 0EA2], second sentence.** Let `A` be a Noetherian normal local domain of
dimension two which is Nagata and has a dualizing module `ω_A`, and let `f : X ⟶ Spec(A)` be a
minimal resolution of singularities. Let `ω_X = H^{-2}(f^×(ω_A[2]))` be as in
[Stacks, Remark 0B4R] (`Stacks.Duality.relativeDualizingModule` at `ω_A[2]^~`, as in the first
sentence, `definesRationalSingularity_of_relativeDualizingModule_iso`). If `ω_X ≅ 𝒪_X(E)` for an
effective Cartier divisor `E ⊆ X` supported on the exceptional fibre, then `E = 0`, i.e. the ideal
sheaf of `E` is the unit ideal `⊤`. The hypotheses are those of the first sentence with
`IsMinimalResolution f` in place of `IsResolution f`; properness of `f` and quasi-compactness and
quasi-separatedness of `X`, needed to form `f^×`, are derived from it inside the statement. -/
@[stacks 0EA2 "second sentence: if f is a minimal resolution, then E = 0"]
theorem eq_top_of_isMinimalResolution_of_relativeDualizingModule_iso (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    (hNagata : IsNagataRing A) (ωA : ModuleCat.{u} A)
    (hω : Stacks.Duality.IsDualizingRingModule A ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsMinimalResolution f)
    (E : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E]
    (hE : ∀ x : X, x ∈ E.support → f x = closedPoint A)
    (e : haveI : IsProper f := hf.1.1.isProper
      haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        ((derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)) ≅
          (Stacks.Divisors.invertibleSheaf' E : X.Modules))) :
    E = ⊤ := by
  have hfr : IsResolution f := hf.isResolution
  have : IsProper f := hfr.1.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨eω⟩ := nonempty_iso_of_relativeDualizingModule_iso A hdim ωA hω f hfr E hE e
  have hrat := definesRationalSingularity_of_relativeDualizingModule_iso A hdim hNagata ωA hω f
    hfr E hE e
  obtain ⟨Y, g, hch, hreg⟩ := exists_singularPointBlowupChain_isRegular_of_iso_dualizingModule A
    hNagata hdim hrat f hfr ωA hω eω
  have hgmod : IsModification g := SingularPointBlowupChain.isModification hch
  obtain ⟨_, _, htg⟩ := SingularPointBlowupChain.hasTrivialTwistedInverseImage
    (SingularPointBlowupChain.and_isIntegral hch) (fun W _ hP w hw hsing => by
      obtain ⟨⟨hn, -, hrdp⟩, hi⟩ := hP
      have := hn
      have := hi
      obtain ⟨S, ⟨eS⟩⟩ := hrdp w hsing
      exact hasTrivialTwistedInverseImage_blowUpToBase hw hsing S eS)
  obtain ⟨tg⟩ := htg
  obtain ⟨k, hk⟩ := hf.2 Y g ⟨hgmod, hreg⟩
  have : IsIntegral X := hfr.1.source_isIntegral
  have : IsNormal X := isNormal_of_isRegular X hfr.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  have hkmod : IsModification k := IsModification.of_comp_eq hfr.1 hgmod hk
  obtain ⟨V, hVi, hV⟩ := IsModification.exists_isIso_morphismRestrict_of_isNormal k hkmod
  have : IsProper k := hkmod.isProper
  have : CompactSpace V := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian V.toScheme := ⟨⟩
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward k
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward g
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (k ≫ f)
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (k ∣_ V)
  let Kf := (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
    (unitQC (Spec (.of A)))
  let tk : (twistedInverseImage k (isQuasicoherent_homology_derivedPushforward_of_qcqs k)).obj Kf ≅
      unitQC Y :=
    ((twistedInverseImageCompIsoOfQcqs k f).app _).symm ≪≫
      (twistedInverseImageCongr hk _ _).app _ ≪≫ tg
  have sqV : IsPullback (k ⁻¹ᵁ V).ι (k ∣_ V) k V.ι := (isPullback_morphismRestrict k V).flip
  have fV := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right sqV Kf
    (isBoundedBelow_twistedInverseImage_obj f _ (isBoundedBelow_unitQC _))
  let t1 : (quasiCoherentDerivedPullback' (k ∣_ V)).obj
      ((quasiCoherentDerivedPullback' V.ι).obj Kf) ≅ unitQC _ :=
    ((twistedInverseImageIsoPullbackOfIsIso (k ∣_ V)).app _).symm ≪≫
      (@asIso _ _ _ _ _ fV).symm ≪≫ (quasiCoherentDerivedPullback' _).mapIso tk ≪≫
      quasiCoherentDerivedPullbackUnitIso _
  obtain ⟨tV⟩ := nonempty_iso_unitQC_of_pullback_of_isIso (k ∣_ V) _ t1
  -- the dualizing module
  have hdimX : topologicalKrullDim X = 2 := by
    have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
    rw [IsBirational.topologicalKrullDim_eq_of_isClosedMap hfr.1.isBirational f.isClosedMap]
    change topologicalKrullDim (PrimeSpectrum A) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  have hidx : (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) = -2 := by
    rw [hdimX]
    rfl
  let := (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).rightAdjointCommShift ℤ
  let eΩ : (derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA) ≅
      (unitQC (Spec (.of A)))⟦(2 : ℤ)⟧ :=
    (derivedTilde _).mapIso ((singleFunctor _ (-2)).mapIso eω) ≪≫ (unitQCShiftIso A 2).symm
  let eH : relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      ((derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)) ≅
      (homologyFunctor X.Modules 0).obj Kf.obj :=
    eqToIso (by rw [relativeDualizingModule, hidx]; rfl) ≪≫
      (homologyFunctor X.Modules (-2)).mapIso ((ObjectProperty.ι _).mapIso
        ((twistedInverseImage f _).mapIso eΩ ≪≫
          ((twistedInverseImage f _).commShiftIso (2 : ℤ)).app _) ≪≫
        ((ObjectProperty.ι _).commShiftIso (2 : ℤ)).app Kf) ≪≫
      (derivedCategoryHomologyShiftNatIso X.Modules 2 (-2) 0 (by norm_num)).app Kf.obj
  let eVω : (Scheme.Modules.pullback V.ι).obj
      (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        ((derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA))) ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    (Scheme.Modules.pullback V.ι).mapIso eH ≪≫
      (homologyQuasiCoherentDerivedPullbackIso V.ι Kf 0).symm ≪≫
      (homologyFunctor _ 0).mapIso ((ObjectProperty.ι _).mapIso tV) ≪≫
      (singleFunctorCompHomologyFunctorIso _ 0).app _
  obtain ⟨eE⟩ := e
  exact Stacks.Divisors.eq_top_of_nonempty_pullback_iso_unit hdim f hfr.1 E hE V hV
    ⟨(Scheme.Modules.pullback V.ι).mapIso eE.symm ≪≫ eVω ≪≫
      (Scheme.Modules.pullbackUnitIso _).symm⟩

end AlgebraicGeometry.DualizingDivisor

end
