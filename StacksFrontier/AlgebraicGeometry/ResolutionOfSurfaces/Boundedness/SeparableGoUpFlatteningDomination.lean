module

public import StacksFrontier.RingTheory.Flat.LocalizationDedekind
public import StacksFrontier.AlgebraicGeometry.Flatness.Applications.FiniteLocallyFreeStrictTransformNoetherian
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PuncturedSpectrumIsomorphism
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationNormalization
public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ToProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpFirstCohomologyInjective
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Dominating a modification by one finite over a modification of the base

Let `A ⟶ B` be a finite injective local map of two-dimensional local normal domains with `A`
Nagata. This file proves that every modification `Y ⟶ Spec B` is dominated by a normal
modification of `Spec B` which is finite and surjective over a normal modification of `Spec A`.
It also proves that `Spec B ⟶ Spec A` is finite locally free over the punctured spectrum of `A`,
and that a modification of a normal integral scheme pushes the structure sheaf forward to the
structure sheaf.

## Main results

* `AlgebraicGeometry.SeparableGoUp.isFiniteLocallyFree_morphismRestrict_puncturedSpectrum`:
  `Spec B ⟶ Spec A` is finite locally free over the punctured spectrum of `A`.
* `AlgebraicGeometry.SeparableGoUp.exists_isFinite_dominating_of_isModification`: every
  modification of `Spec B` is dominated by a normal modification finite over a normal
  modification of `Spec A`.
* `AlgebraicGeometry.SeparableGoUp.isIso_c_of_isModification_of_isNormal`: a modification of a
  normal integral scheme pushes the structure sheaf forward to the structure sheaf.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0B49](https://stacks.math.columbia.edu/tag/0B49)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry.SeparableGoUp

variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/-- The inverse image of the punctured spectrum along a local homomorphism lies in the punctured
spectrum. -/
theorem preimage_puncturedSpectrum_le (φ : A →+* B) [IsLocalHom φ] :
    Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ Stacks.puncturedSpectrum A ≤
      Stacks.puncturedSpectrum B := by
  intro q hq hqB
  apply hq
  show PrimeSpectrum.comap φ q = closedPoint A
  rw [show q = closedPoint B from hqB]
  exact IsLocalRing.comap_closedPoint φ

omit [IsLocalRing B] in
/-- **A finite injective local map of a two-dimensional Noetherian normal local domain is finite
locally free over the punctured spectrum.** -/
theorem isFiniteLocallyFree_morphismRestrict_puncturedSpectrum [IsNoetherianRing A]
    [IsNormalDomain A] [IsDomain B] (hdim : ringKrullDim A = 2) (φ : A →+* B) [IsLocalHom φ]
    (hφ : Function.Injective φ) (hfin : φ.Finite) :
    Stacks.Morphisms.IsFiniteLocallyFree
      (Spec.map (CommRingCat.ofHom φ) ∣_ Stacks.puncturedSpectrum A) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom φ)) := (IsFinite.SpecMap_iff _).mpr hfin
  have : IsNoetherianRing (CommRingCat.of A) := ‹IsNoetherianRing A›
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ)) := inferInstance
  refine (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    _).mpr ⟨inferInstance, ?_, inferInstance⟩
  rw [Flat.iff_flat_stalkMap]
  intro x
  refine (RingHom.Flat.respectsIso.arrow_mk_iso_iff
    ((morphismRestrictStalkMap _ _ x).trans
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom φ) x.1))).mpr ?_
  have : x.1.asIdeal.IsPrime := x.1.isPrime
  have hx : x.1.asIdeal.comap φ ≠ maximalIdeal A := fun h =>
    x.2 (PrimeSpectrum.ext h)
  have := Stacks.Flat.isDedekindDomain_localization_atPrime _
    (Stacks.Flat.height_le_one_of_ne_maximalIdeal hdim _ hx)
  exact Stacks.Flat.flat_localRingHom_of_isDedekindDomain φ hφ x.1.asIdeal

/-- A point of the source of a birational morphism of integral schemes mapping to the generic
point of the target is the generic point. -/
private theorem eq_genericPoint_of_isBirational {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : IsBirational f) {z : X} (hz : f z = genericPoint Y) :
    z = genericPoint X := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  have hz' : z ∈ f ⁻¹' genericPoints Y := by
    rw [genericPoints_eq_singleton]; exact hz
  rwa [preimage_genericPoints_eq_genericPoints_of_isBirational f hf, genericPoints_eq_singleton]
    at hz'

/-- Let `A ⟶ B` be a finite injective local map of two-dimensional local domains with `A`
Noetherian, normal and Nagata and `B` normal. Every modification `Y ⟶ Spec B` is dominated by a
normal modification `Y' ⟶ Spec B` which is finite and surjective over a normal modification
`X' ⟶ Spec A`, compatibly with `Spec B ⟶ Spec A`. -/
theorem exists_isFinite_dominating_of_isModification {A B : Type u} [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsNagataRing A] [CommRing B] [IsLocalRing B] [IsNormalDomain B]
    [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    (hinj : Function.Injective (algebraMap A B)) {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ Spec (.of B)) (hg : IsModification g) :
    ∃ (Y' X' : Scheme.{u}) (g' : Y' ⟶ Spec (.of B)) (f' : X' ⟶ Spec (.of A)) (π : Y' ⟶ X')
      (q : Y' ⟶ Y), IsNormal Y' ∧ IsNormal X' ∧ IsModification g' ∧ IsModification f' ∧
        IsModification q ∧ IsFinite π ∧ Surjective π ∧
          π ≫ f' = g' ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ q ≫ g = g' := by
  classical
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsNoetherianRing (CommRingCat.of B) := inferInstanceAs (IsNoetherianRing B)
  have : IsDomain (CommRingCat.of A) := inferInstanceAs (IsDomain A)
  have : IsDomain (CommRingCat.of B) := inferInstanceAs (IsDomain B)
  set φ := algebraMap A B
  set sB : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
  set h : Y ⟶ Spec (.of A) := g ≫ sB with hh
  have : IsProper g := hg.isProper
  have hfin : φ.Finite := RingHom.finite_algebraMap.mpr inferInstance
  have : IsFinite sB := (IsFinite.SpecMap_iff _).mpr hfin
  have : IsProper h := inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hsBdom : IsDominant sB := isDominant_Spec_map_of_injective (CommRingCat.ofHom φ) hinj
  have hhgen : h (genericPoint Y) = genericPoint (Spec (.of A)) := by
    rw [hh, Scheme.Hom.comp_apply, IsBirational.genericPoint_eq g hg.isBirational]
    exact genericPoint_eq_of_isDominant sB
  have hgU : IsIso (g ∣_ Stacks.puncturedSpectrum B) := by
    have := finite_irreducibleComponents_fiber_closedPoint B g
    exact VanishingSituation.isIso_morphismRestrict_puncturedSpectrumOpen
      { A := B, dimension_two := hdimB, X := Y, f := g, modification := hg,
        numberOfComponents := Nat.card {Z : Set (g.fiber (IsLocalRing.closedPoint B)) //
          Z ∈ irreducibleComponents (g.fiber (IsLocalRing.closedPoint B))}
        components := (Finite.equivFin _).symm }
  have : IsIso (g ∣_ (sB ⁻¹ᵁ Stacks.puncturedSpectrum A)) :=
    isIso_morphismRestrict_of_le g (preimage_puncturedSpectrum_le φ) hgU
  have hsBU : Stacks.Morphisms.IsFiniteLocallyFree (sB ∣_ Stacks.puncturedSpectrum A) :=
    isFiniteLocallyFree_morphismRestrict_puncturedSpectrum hdimA φ hinj hfin
  obtain ⟨hsBUfin, hsBUflat, hsBUlfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      hsBU
  have : IsFinite (g ∣_ (sB ⁻¹ᵁ Stacks.puncturedSpectrum A)) := inferInstance
  have : Flat (g ∣_ (sB ⁻¹ᵁ Stacks.puncturedSpectrum A)) := inferInstance
  have : LocallyOfFinitePresentation (g ∣_ (sB ⁻¹ᵁ Stacks.puncturedSpectrum A)) :=
    inferInstance
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree
      (pullback.snd h (Stacks.puncturedSpectrum A).ι) := by
    rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation,
      ← pullbackRestrictIsoRestrict_hom_morphismRestrict h, hh, morphismRestrict_comp]
    set e := (pullbackRestrictIsoRestrict (g ≫ sB) (Stacks.puncturedSpectrum A)).hom
    set k := g ∣_ sB ⁻¹ᵁ Stacks.puncturedSpectrum A ≫ sB ∣_ Stacks.puncturedSpectrum A
    have h₁ : IsFinite k := inferInstance
    have h₂ : Flat k := inferInstance
    have h₃ : LocallyOfFinitePresentation k := inferInstance
    exact ⟨MorphismProperty.comp_mem (W := @IsFinite) e k inferInstance h₁,
      MorphismProperty.comp_mem (W := @Flat) e k inferInstance h₂,
      MorphismProperty.comp_mem (W := @LocallyOfFinitePresentation) e k inferInstance h₃⟩
  have : NoetherianSpace (Spec (.of A)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum A))
  have hU : IsCompact (Stacks.puncturedSpectrum A : Set (Spec (.of A))) :=
    NoetherianSpace.isCompact _
  obtain ⟨I, hadm, hIflf⟩ :=
    exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isLocallyNoetherian h
      (Stacks.puncturedSpectrum A) hU
  have hUne : genericPoint (Spec (.of A)) ∈ Stacks.puncturedSpectrum A := by
    intro hgen
    have hbot : (⊥ : Ideal A) = IsLocalRing.maximalIdeal A := by
      have := congrArg PrimeSpectrum.asIdeal hgen
      rwa [genericPoint_eq_bot_of_affine] at this
    have := ringKrullDim_eq_zero_of_isField
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot.symm)
    rw [hdimA] at this
    exact absurd this (by decide)
  obtain ⟨J, -, hJdisj, e, -⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff _ _).mp hadm
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    have : genericPoint (Spec (.of A)) ∈ ((⊥ : (Spec (.of A)).IdealSheafData).support :
        Set (Spec (.of A))) := by
      rw [Scheme.IdealSheafData.support_bot]; trivial
    exact Set.disjoint_left.mp hJdisj hUne this
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    have := isIntegral_blowUp J hJ0
    have := isEmpty_blowUp_bot (Spec (.of A))
    exact IsEmpty.false (e.inv (Nonempty.some inferInstance))
  have : IsIntegral (blowUp I) := isIntegral_blowUp I hI0
  have hmodX : IsModification (blowUpToBase I) :=
    ⟨isBirational_blowUpToBase I hI0, inferInstance, inferInstance⟩
  have hIY0 : I.comap h ≠ ⊥ := by
    intro hbot
    have hmem : genericPoint Y ∈ ((I.comap h).support : Set Y) := by
      rw [hbot, Scheme.IdealSheafData.support_bot]; trivial
    rw [Scheme.IdealSheafData.support_comap] at hmem
    exact genericPoint_notMem_supportSet I hI0 (hhgen ▸ hmem)
  set bY := blowUpToBase (I.comap h)
  have : IsIntegral (blowUp (I.comap h)) := isIntegral_blowUp (I.comap h) hIY0
  have hmodbY : IsModification bY :=
    ⟨isBirational_blowUpToBase (I.comap h) hIY0, inferInstance, inferInstance⟩
  set π₁ : blowUp (I.comap h) ⟶ blowUp I :=
    inv (pullback.snd (𝟙 Y) bY) ≫ strictTransformBlowUpι h I ≫
      pullback.snd h (blowUpToBase I) with hπ₁
  have hπ₁fin : IsFinite π₁ := by
    have : IsFinite (strictTransformToBlowUp h I) :=
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        _).mp hIflf).1
    rw [hπ₁, strictTransformBlowUpι_comp_snd]
    infer_instance
  have hπ₁comm : π₁ ≫ blowUpToBase I = bY ≫ h := by
    have hfst : inv (pullback.snd (𝟙 Y) bY) ≫ pullback.fst (𝟙 Y) bY = bY := by
      rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
    rw [hπ₁, Category.assoc, Category.assoc, ← pullback.condition,
      ← Category.assoc (strictTransformBlowUpι h I), strictTransformBlowUpι_fst,
      ← Category.assoc, hfst]
  have hX₁N : IsNagataScheme (blowUp I) := isNagataScheme_of_isNagataRing (blowUpToBase I) ‹_›
  have hX₁ := Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
    _ hX₁N
  have hY₁N : IsNagataScheme (blowUp (I.comap h)) :=
    isNagataScheme_of_isNagataRing (bY ≫ h) ‹_›
  have hY₁ := Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
    _ hY₁N
  set νX := (blowUp I).normalization hX₁
  set νY := (blowUp (I.comap h)).normalization hY₁
  have : IsFinite νX := Scheme.isFinite_normalization hX₁N hX₁
  have : IsNormal ((blowUp (I.comap h)).normalizationScheme hY₁) :=
    Scheme.isNormal_normalizationScheme _ hY₁
  have hf' : IsModification (νX ≫ blowUpToBase I) :=
    isModification_normalization_comp_of_isNagataScheme _ hmodX hX₁N hX₁
  have hq : IsModification (νY ≫ bY) :=
    isModification_normalization_comp_of_isNagataScheme _ hmodbY hY₁N hY₁
  have : IsProper (νY ≫ bY) := hq.isProper
  have hg' : IsModification ((νY ≫ bY) ≫ g) :=
    ⟨IsBirational.comp hq.isBirational hg.isBirational, inferInstance, inferInstance⟩
  have : IsFinite νY := Scheme.isFinite_normalization hY₁N hY₁
  have hgenY' : (νY ≫ π₁) (genericPoint _) = genericPoint (blowUp I) := by
    refine eq_genericPoint_of_isBirational (blowUpToBase I) hmodX.isBirational ?_
    have hk : (νY ≫ π₁) ≫ blowUpToBase I = (νY ≫ bY) ≫ h := by
      rw [Category.assoc, hπ₁comm, Category.assoc]
    have e1 : ∀ x, blowUpToBase I ((νY ≫ π₁) x) = h ((νY ≫ bY) x) := fun x => by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk]
    rw [e1, IsBirational.genericPoint_eq _ hq.isBirational]
    exact hhgen
  obtain ⟨π, hπ, -⟩ := Scheme.existsUnique_lift_normalization hX₁ (νY ≫ π₁) fun η => by
    obtain ⟨η, hη⟩ := η
    have hη' : η = genericPoint _ := by simpa [genericPoints_eq_singleton] using hη
    show (νY ≫ π₁) η ∈ _
    rw [hη', hgenY', genericPoints_eq_singleton]
    rfl
  have hπfin : IsFinite π := by
    have : IsFinite (π ≫ νX) := by rw [hπ]; infer_instance
    exact IsFinite.of_comp π νX
  have hπdom : IsDominant π := by
    refine ((tfae_isDominant_of_isIntegral π).out 1 2).mpr ?_
    refine eq_genericPoint_of_isBirational νX ((blowUp I).isBirational_normalization hX₁) ?_
    rw [← Scheme.Hom.comp_apply, hπ, hgenY']
  refine ⟨_, _, (νY ≫ bY) ≫ g, νX ≫ blowUpToBase I, π, νY ≫ bY, inferInstance,
    Scheme.isNormal_normalizationScheme _ hX₁, hg', hf', hq, hπfin,
    surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range, ?_, rfl⟩
  rw [← Category.assoc, hπ, Category.assoc, hπ₁comm]
  simp only [Category.assoc]
  rfl

/-- **The structure sheaf pushes forward to the structure sheaf along a modification of a normal
integral scheme**: for a modification `q : Y' ⟶ Y` with `Y` normal and integral, the map
`𝒪_Y ⟶ q_* 𝒪_{Y'}` is an isomorphism. -/
theorem isIso_c_of_isModification_of_isNormal {Y Y' : Scheme.{u}} [IsIntegral Y] [IsNormal Y]
    (q : Y' ⟶ Y) (hq : IsModification q) : IsIso q.c := by
  have : IsProper q := hq.isProper
  have : IsIntegral Y' := hq.source_isIntegral
  have hfib : IsIso (q.fiberToSpecResidueField (genericPoint Y)) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational q hq.isBirational
  have : IsIso (q.fiberToSpecResidueField (genericPoint Y)).appTop := by
    have : IsIso (q.fiberToSpecResidueField (genericPoint Y)).c :=
      PresheafedSpace.c_isIso_of_iso (q.fiberToSpecResidueField (genericPoint Y)).toPshHom
    exact NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  refine Stacks.SteinFactorization.isIso_c_of_isNormal q (fun x hx => ?_) inferInstance
  have hmem := hq.isBirational.bijOn.mapsTo hx
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem

end AlgebraicGeometry.SeparableGoUp

end
