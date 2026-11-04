module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.RingTheory.Flat.FaithfullyFlatComp
import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locality of Tor amplitude

Tor amplitude is a local condition. A complex of `R`-modules has Tor amplitude in `[a, b]` as soon
as it does so after localisation at each member of a family generating the unit ideal; it may
equally be tested after a faithfully flat base change, or prime by prime.

Except in `hasTorAmplitude_of_faithfullyFlat`, Tor amplitude is the projective-resolution predicate
`StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude` of Stacks 0DJF: the vanishing of
`Hⁱ(K ⊗ P)` for `P` a chosen projective resolution of the test module, for test modules in the
ring's own universe. `hasTorAmplitude_of_faithfullyFlat` is stated for the certified derived Tor
amplitude `StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks 0652. The two agree at a bounded
above complex of flat modules (`hasTorAmplitude_iff_hasTorAmplitude0DJF`).

## Main definitions

* `StacksDraft.TorAmplitude.HasTorAmplitudeAt`: Tor amplitude of the localisation of a complex of
  `B`-modules at a prime of `B`, measured over the corresponding localisation of `A`.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitude_of_localizationSpan`: Tor amplitude descends from a
  principal-open cover, Stacks 066N.
* `StacksDraft.TorAmplitude.hasTorAmplitude_of_faithfullyFlat`: certified derived Tor amplitude
  descends along a faithfully flat ring map, Stacks 068S, with the two rings and the ambient module
  universe independent.
* `StacksDraft.TorAmplitude.hasTorAmplitude0DJF_of_faithfullyFlat`: the same descent for the
  projective-resolution Tor amplitude of Stacks 0DJF, with the two rings and the modules in one
  universe; `hasTorAmplitude0DJF_of_faithfullyFlat_ulift` is its independent-ring-universe form.
* `StacksDraft.TorAmplitude.hasTorAmplitude_restrictScalars_extendScalars_of_flat`: Tor amplitude
  over `A` of a complex of `B`-modules is preserved by a flat base change `B → C`.
* `StacksDraft.TorAmplitude.hasTorAmplitudeAt_of_hasTorAmplitude_extendScalars`: Tor amplitude over
  `A` of the localisation at a prime `q` of `B` gives Tor amplitude over `A_{q ∩ A}`.
* `StacksDraft.TorAmplitude.hasTorAmplitude_iff_localized_at_primes_iff_maximals`: Tor amplitude
  over `A` of a complex of `B`-modules may be tested at all primes, or at all maximal ideals, of
  `B`, Stacks 0B67.

## Implementation notes

Localisation of a complex is termwise extension of scalars, to `Localization.Away` for a principal
cover and to `Localization.AtPrime` for a prime; this computes the derived localisation because
localisation is flat. The family in Stacks 066N is a finite list of elements generating the unit
ideal; here it is an arbitrary set spanning the unit ideal.

## References

* [Stacks Project, Tag 066N](https://stacks.math.columbia.edu/tag/066N)
* [Stacks Project, Tag 068S](https://stacks.math.columbia.edu/tag/068S)
* [Stacks Project, Tag 0B67](https://stacks.math.columbia.edu/tag/0B67)
-/

open CategoryTheory Limits MonoidalCategory

namespace StacksDraft.TorAmplitude

universe u

@[expose] public section

set_option backward.isDefEq.respectTransparency false


/-! ## Flat base change of derived-tensor cohomology -/

/-- Extension of scalars along a flat ring map is additive, preserves finite limits and homology,
and preserves projective objects. -/
private theorem extendScalars_instances_of_flat
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] :
    letI F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
    F.Additive ∧ PreservesFiniteLimits F ∧ F.PreservesHomology ∧ F.PreservesProjectiveObjects := by
  have h1 : (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).left_adjoint_additive
  have h2 : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat R S›)
  exact ⟨h1, h2, Functor.preservesHomologyOfExact _,
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R S))⟩

/-- For a flat ring map `R → B`, the degree-`i` derived-tensor cohomology of the base change of `K`
against the base change of `M` is the base change of the degree-`i` derived-tensor cohomology of
`K` against `M`. -/
private theorem derivedTensorHomology_extendScalars_iso
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    Nonempty (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology
      ((CochainComplex.extendScalars (algebraMap R B)).obj K)
      ((ModuleCat.extendScalars (algebraMap R B)).obj M) i ≅
      (ModuleCat.extendScalars (algebraMap R B)).obj
        (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology K M i)) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} B := ModuleCat.extendScalars (algebraMap R B)
  obtain ⟨_, _, _, _⟩ := extendScalars_instances_of_flat R B
  let Q := F.mapProjectiveResolution (ProjectiveResolution.of M)
  let P := ProjectiveResolution.of (F.obj M)
  let ePQ' := FaithfullyFlat.homotopyEquivExtendDownNat (ProjectiveResolution.homotopyEquiv P Q)
  let eT := TotalTensorComplex.tensorHomotopyEquiv (HomotopyEquiv.refl
    ((CochainComplex.extendScalars (algebraMap R B)).obj K)) ePQ'
  let eTK := StacksDraft.TorAmplitude.FaithfullyFlat.extendTensorLeftIso R B K
    (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)
  let eMap := (HomologicalComplex.mapHomologicalComplexExtendIso F
    (ProjectiveResolution.of M).complex ComplexShape.embeddingDownNat).symm
  exact ⟨eT.toHomologyIso i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) i).mapIso
      ((tensorLeft ((CochainComplex.extendScalars (algebraMap R B)).obj K)).mapIso eMap.symm)
    ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) i).mapIso
      eTK.symm ≪≫ ShortComplex.mapHomologyIso
        (((tensorLeft K).obj (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)).sc i) F⟩

/-- A module that vanishes after localization at every member of a set generating the unit ideal
vanishes. -/
private theorem isZero_of_isZero_localizations
    (R : Type u) [CommRing R] (s : Set R) (hs : Ideal.span s = ⊤) (N : ModuleCat.{u} R)
    (hN : ∀ f : s, IsZero ((ModuleCat.extendScalars
      (algebraMap R (Localization.Away (f : R)))).obj N)) : IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hzero (x : (N : Type u)) : x = 0 := by
    apply Module.eq_zero_of_isLocalized_span s hs
      (fun f => TensorProduct R (Localization.Away (f : R)) (N : Type u))
      (fun f => TensorProduct.mk R (Localization.Away (f : R)) (N : Type u) 1)
    intro f
    have := (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv R
      (Localization.Away (f : R)) N).toEquiv.subsingleton_congr.mp
        (ModuleCat.isZero_iff_subsingleton.mp (hN f))
    exact Subsingleton.elim _ _
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- If a complex has Tor amplitude in `[a, b]` after localization at every member of a set
generating the unit ideal, then it has Tor amplitude in `[a, b]`. -/
@[stacks 066N]
theorem hasTorAmplitude_of_localizationSpan
    {R : Type u} [CommRing R] (s : Set R) (hs : Ideal.span s = ⊤)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hK : ∀ f : s, StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.extendScalars
        (algebraMap R (Localization.Away (f : R)))).obj K) a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b := by
  intro M i hi
  exact isZero_of_isZero_localizations R s hs _ fun f =>
    (derivedTensorHomology_extendScalars_iso R (Localization.Away (f : R)) K M i).some.isZero_iff.mp
      (hK f _ i hi)

/-! ## Faithfully flat descent -/

/-- Restriction of scalars along a flat ring map preserves a Tor-amplitude bound: this is the
projective-resolution form of Stacks 066J. -/
private theorem hasTorAmplitude_restrictScalars_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (L : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude L a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap R S)).obj L) a b := by
  intro M i hi
  let G := ModuleCat.extendScalars (algebraMap R S)
  let P := ProjectiveResolution.of M
  obtain ⟨_, _, _, _⟩ := extendScalars_instances_of_flat R S
  let Q : ProjectiveResolution (G.obj M) := G.mapProjectiveResolution P
  let ee := FaithfullyFlat.homotopyEquivExtendDownNat (ProjectiveResolution.homotopyEquiv
    (ProjectiveResolution.of (G.obj M)) Q)
  let te := TotalTensorComplex.tensorHomotopyEquiv (HomotopyEquiv.refl L) ee
  let em := (HomologicalComplex.mapHomologicalComplexExtendIso G P.complex
    ComplexShape.embeddingDownNat).symm
  let eS := (te.toHomologyIso i).trans
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso ((tensorLeft L).mapIso em.symm))
  rw [← (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyARestrictIso R S L M
    i).isZero_iff,
    StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff]
  exact (h (G.obj M) i hi).of_iso eS.symm

/-- Projective-resolution Tor amplitude descends along a faithfully flat ring map: if the base
change of `K` along `R → S` has Tor amplitude in `[a, b]`, then so does `K`. Here the two rings and
the module carriers share the universe `u`. -/
theorem hasTorAmplitude0DJF_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.extendScalars (algebraMap R S)).obj K) a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b := by
  exact (StacksDraft.TorAmplitude.FaithfullyFlat.hasTorAmplitudeIn_iff_extendScalars R R S K a
    b).mpr (hasTorAmplitude_restrictScalars_of_flat _ a b h)

section IndependentUniverses

universe v w

/-- The lifted ring map `f.ulift` of a faithfully flat ring map makes the target a faithfully flat
algebra. -/
private theorem faithfullyFlat_ulift_algebra
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FaithfullyFlat) :
    letI : Algebra (ULift.{max v w} R) (ULift.{max u w} S) :=
      (f.ulift.{max v w, max u w}).toAlgebra
    Module.FaithfullyFlat (ULift.{max v w} R) (ULift.{max u w} S) := by
  have hd : (ULift.ringEquiv : ULift.{max v w} R ≃+* R).toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective ULift.ringEquiv.bijective
  have hu : (ULift.ringEquiv : ULift.{max u w} S ≃+* S).symm.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective ULift.ringEquiv.symm.bijective
  exact RingHom.FaithfullyFlat.comp (RingHom.FaithfullyFlat.comp hd hf) hu

/-- Faithfully flat descent of projective-resolution Tor amplitude with the two rings in
independent universes: if `f : R →+* S` is faithfully flat and the base change along the lifted
ring map `f.ulift` of a complex `K` of `ULift R`-modules has Tor amplitude in `[a, b]`, then so
does `K`. -/
@[sga "6 I 5.7" "Exercise 5.7 a)"]
theorem hasTorAmplitude0DJF_of_faithfullyFlat_ulift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{max u v w} (ULift.{max v w} R)) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.extendScalars (f.ulift.{max v w, max u w})).obj K) a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b := by
  let : Algebra (ULift.{max v w} R) (ULift.{max u w} S) :=
    (f.ulift.{max v w, max u w}).toAlgebra
  have := faithfullyFlat_ulift_algebra.{u, v, w} f hf
  exact hasTorAmplitude0DJF_of_faithfullyFlat K a b h

end IndependentUniverses

/-! ## Faithfully flat descent of the certified derived Tor amplitude -/

section Certified

universe v w

attribute [local instance] HasDerivedCategory.standard

/-- Faithfully flat descent of the certified derived Tor amplitude of Stacks 0652, for arbitrary
certified derived tensor products over `A` and over `B`, with the two rings and the modules in one
universe. -/
@[sga "4½ Arcata 1.4.2" "more general", sga "6 I 5.7" "a)"]
private theorem hasTorAmplitude_certified_of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {derivedTensorA : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A)}
    (comparisonA : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙ derivedTensorA.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedA : ∀ N : ModuleCat.{u} A,
      (derivedTensorA.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
          (comparisonA N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    {derivedTensorB : DerivedCategory (ModuleCat.{u} B) ⥤
      DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B)}
    (comparisonB : ∀ N : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ derivedTensorB.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedB : ∀ N : ModuleCat.{u} B,
      (derivedTensorB.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N)).IsLeftDerivedFunctor
          (comparisonB N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (h : HasTorAmplitude derivedTensorB comparisonB isLeftDerivedB
      (DerivedCategory.Q.obj ((CochainComplex.extendScalars (algebraMap A B)).obj K)) a b) :
    HasTorAmplitude derivedTensorA comparisonA isLeftDerivedA (DerivedCategory.Q.obj K) a b := by
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} B := ModuleCat.extendScalars (algebraMap A B)
  obtain ⟨_, _, _, _⟩ := extendScalars_instances_of_flat A B
  have hcoh : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (DerivedCategory.Q.obj K)) := by
    intro i hi
    have hz : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i) :=
      isZero_homology_of_hasTorAmplitude comparisonB isLeftDerivedB _ a b h i (Or.inr hi)
    have hzA : IsZero (K.homology i) := by
      rw [← StacksDraft.TorAmplitude.FaithfullyFlat.isZero_extendScalars_iff (B := B) (K.homology
        i)]
      exact hz.of_iso ((K.sc i).mapHomologyIso F).symm
    exact hzA.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app K)
  obtain ⟨P, hproj, hPLE, ⟨eP⟩⟩ :=
    exists_projective_representative_of_isLE (DerivedCategory.Q.obj K) b hcoh
  have := hPLE
  have hflatP : ∀ i : ℤ, Module.Flat A (P.X i) := fun i => by
    have := hproj i
    infer_instance
  have hbddP : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨b, fun i hi => P.isZero_of_isStrictlyLE b i hi⟩
  have hKFlatP : P.KFlat := kFlat_of_isStrictlyLE_projective P b hproj
  let FP : CochainComplex (ModuleCat.{u} B) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hprojFP : ∀ i : ℤ, Projective (FP.X i) :=
    fun i => F.projective_obj_of_projective (hproj i)
  have hzFP : ∀ i : ℤ, b < i → IsZero (FP.X i) :=
    fun i hi => F.map_isZero (P.isZero_of_isStrictlyLE b i hi)
  have hFPLE : FP.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff FP b).2 hzFP
  have := hFPLE
  have hKFlatFP : FP.KFlat := kFlat_of_isStrictlyLE_projective FP b hprojFP
  have hflatFP : ∀ i : ℤ, Module.Flat B (FP.X i) := fun i => by
    have := hprojFP i
    infer_instance
  have hB : HasTorAmplitude derivedTensorB comparisonB isLeftDerivedB
      (DerivedCategory.Q.obj FP) a b :=
    (hasTorAmplitude_of_iso ((F.mapDerivedCategoryFactors.app K).symm ≪≫
      F.mapDerivedCategory.mapIso eP ≪≫ F.mapDerivedCategoryFactors.app P) a b).1 h
  exact (hasTorAmplitude_of_iso eP a b).2
    ((hasTorAmplitude_iff_hasTorAmplitude0DJF comparisonA isLeftDerivedA P hKFlatP hbddP
        hflatP a b).2
      (hasTorAmplitude0DJF_of_faithfullyFlat P a b
        ((hasTorAmplitude_iff_hasTorAmplitude0DJF comparisonB isLeftDerivedB FP hKFlatFP
            ⟨b, hzFP⟩ hflatFP a b).1 hB)))

/-- The general form of Stacks 068S: Tor amplitude descends along a faithfully flat ring map
`f : R →+* S`, so that if the base change of `K` along `f` has Tor amplitude in `[a, b]`, then so
does `K`.

Tor amplitude is the certified derived Tor amplitude of Stacks 0652: on each side an arbitrary
derived tensor product on the derived category, equipped with its comparison map to termwise
tensoring and the universal property making it a total left derived functor in the first variable.
The two rings live in independent universes `u` and `v`, and the module carriers in any universe
`max u v w` above both. Each ring acts on the modules through its `ULift` to that universe, and the
base change is extension of scalars along the lifted ring map `f.ulift`. -/
theorem hasTorAmplitude_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    {derivedTensorR : DerivedCategory (ModuleCat.{max u v w} (ULift.{max v w} R)) ⥤
      DerivedCategory (ModuleCat.{max u v w} (ULift.{max v w} R)) ⥤
        DerivedCategory (ModuleCat.{max u v w} (ULift.{max v w} R))}
    (comparisonR : ∀ N : ModuleCat.{max u v w} (ULift.{max v w} R),
      DerivedCategory.Q ⋙ derivedTensorR.flip.obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{max u v w} (ULift.{max v w} R)) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedR : ∀ N : ModuleCat.{max u v w} (ULift.{max v w} R),
      (derivedTensorR.flip.obj
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max u v w} (ULift.{max v w} R)) 0).obj N)).IsLeftDerivedFunctor
          (comparisonR N)
          (HomologicalComplex.quasiIso (ModuleCat.{max u v w} (ULift.{max v w} R))
            (ComplexShape.up ℤ)))
    {derivedTensorS : DerivedCategory (ModuleCat.{max u v w} (ULift.{max u w} S)) ⥤
      DerivedCategory (ModuleCat.{max u v w} (ULift.{max u w} S)) ⥤
        DerivedCategory (ModuleCat.{max u v w} (ULift.{max u w} S))}
    (comparisonS : ∀ N : ModuleCat.{max u v w} (ULift.{max u w} S),
      DerivedCategory.Q ⋙ derivedTensorS.flip.obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{max u v w} (ULift.{max u w} S)) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedS : ∀ N : ModuleCat.{max u v w} (ULift.{max u w} S),
      (derivedTensorS.flip.obj
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max u v w} (ULift.{max u w} S)) 0).obj N)).IsLeftDerivedFunctor
          (comparisonS N)
          (HomologicalComplex.quasiIso (ModuleCat.{max u v w} (ULift.{max u w} S))
            (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{max u v w} (ULift.{max v w} R)) ℤ) (a b : ℤ)
    (h : HasTorAmplitude derivedTensorS comparisonS isLeftDerivedS
      (DerivedCategory.Q.obj
        ((CochainComplex.extendScalars (f.ulift.{max v w, max u w})).obj K)) a b) :
    HasTorAmplitude derivedTensorR comparisonR isLeftDerivedR (DerivedCategory.Q.obj K) a b := by
  let : Algebra (ULift.{max v w} R) (ULift.{max u w} S) :=
    (f.ulift.{max v w, max u w}).toAlgebra
  have := faithfullyFlat_ulift_algebra.{u, v, w} f hf
  exact hasTorAmplitude_certified_of_faithfullyFlat comparisonR isLeftDerivedR
    comparisonS isLeftDerivedS K a b h

end Certified

/-! ## Localisation -/

/-- The projective resolution of `Y` given by a projective resolution of `X` and an isomorphism
`X ≅ Y`, with the isomorphism composed into the augmentation map. -/
private noncomputable def projectiveResolutionOfIso {C : Type*} [Category C] [Abelian C]
    {X Y : C} (P : ProjectiveResolution X) (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := by
    have : IsIso ((ChainComplex.single₀ C).map e.hom) :=
      (ChainComplex.single₀ C).map_isIso e.hom
    infer_instance

/-- Derived-tensor cohomology only depends on the isomorphism class of the test module. -/
private theorem derivedTensorHomology_congr_module
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : ModuleCat.{u} R} (e : M ≅ N) (i : ℤ) :
    Nonempty (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology K M i ≅
      StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology K N i) := by
  let h : HomotopyEquiv (ProjectiveResolution.of M).complex
      (ProjectiveResolution.of N).complex :=
    ProjectiveResolution.homotopyEquiv (ProjectiveResolution.of M)
      (projectiveResolutionOfIso (ProjectiveResolution.of N) e.symm)
  exact ⟨(TotalTensorComplex.tensorHomotopyEquiv (HomotopyEquiv.refl K)
    (FaithfullyFlat.homotopyEquivExtendDownNat h)).toHomologyIso i⟩

/-- A module over a localisation `S` of `R` is its own base change along `R → S`. -/
private noncomputable def extendRestrictLocalizationSelfIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (P : Submonoid R) [IsLocalization P S] (N : ModuleCat.{u} S) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
      ((ModuleCat.restrictScalars (algebraMap R S)).obj N) ≅ N := by
  let N' := (ModuleCat.restrictScalars (algebraMap R S)).obj N
  let _ : Module S (N' : Type u) := inferInstanceAs (Module S (N : Type u))
  let _ : IsScalarTower R S (N' : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact LinearEquiv.toModuleIso ((StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv
    R S N').trans
    (IsLocalization.moduleLid P S (N' : Type u)))

/-- Base change to a localisation preserves a Tor-amplitude bound. -/
private theorem hasTorAmplitude_extendScalars_of_isLocalization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (P : Submonoid R) [IsLocalization P S]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude C a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.extendScalars (algebraMap R S)).obj C) a b := by
  have : Module.Flat R S := IsLocalization.flat S P
  intro N i hi
  obtain ⟨e1⟩ := derivedTensorHomology_congr_module
    ((CochainComplex.extendScalars (algebraMap R S)).obj C)
    (extendRestrictLocalizationSelfIso R S P N).symm i
  obtain ⟨e2⟩ := derivedTensorHomology_extendScalars_iso R S C
    ((ModuleCat.restrictScalars (algebraMap R S)).obj N) i
  exact (e1.trans e2).isZero_iff.mpr
    ((ModuleCat.extendScalars (algebraMap R S)).map_isZero (h _ i hi))

/-- The `S`-module lift of derived-tensor cohomology against an `R`-module `M` is the
derived-tensor cohomology against the base change of `M`. -/
private theorem derivedTensorHomologyA_extend_iso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (M : ModuleCat.{u} R) (i : ℤ) :
    Nonempty (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyA R S C M i ≅
      StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology C
        ((ModuleCat.extendScalars (algebraMap R S)).obj M) i) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars (algebraMap R S)
  obtain ⟨_, _, _, _⟩ := extendScalars_instances_of_flat R S
  let Q := F.mapProjectiveResolution (ProjectiveResolution.of M)
  let ePQ := FaithfullyFlat.homotopyEquivExtendDownNat
    (ProjectiveResolution.homotopyEquiv Q (ProjectiveResolution.of (F.obj M)))
  let eMap := (HomologicalComplex.mapHomologicalComplexExtendIso F
    (ProjectiveResolution.of M).complex ComplexShape.embeddingDownNat).symm
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) i).mapIso
      ((tensorLeft C).mapIso eMap) ≪≫
      (TotalTensorComplex.tensorHomotopyEquiv
        (HomotopyEquiv.refl C) ePQ).toHomologyIso i⟩

/-- Restriction of scalars along a localisation detects Tor amplitude: if the restriction of a
complex of `S`-modules to `R` has Tor amplitude in `[a, b]`, so has the complex itself. -/
private theorem hasTorAmplitude_of_restrictScalars_isLocalization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (P : Submonoid R) [IsLocalization P S]
    (C : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap R S)).obj C) a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude C a b := by
  have : Module.Flat R S := IsLocalization.flat S P
  intro N i hi
  let M := (ModuleCat.restrictScalars (algebraMap R S)).obj N
  obtain ⟨e1⟩ := derivedTensorHomology_congr_module C
    (extendRestrictLocalizationSelfIso R S P N).symm i
  obtain ⟨e2⟩ := derivedTensorHomologyA_extend_iso R S C M i
  refine (e1.trans e2.symm).isZero_iff.mpr ?_
  rw [← StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff (algebraMap R S),
    (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyARestrictIso R S C M
      i).isZero_iff]
  exact h M i hi

/-- Tor amplitude is invariant under isomorphism of complexes. -/
private theorem hasTorAmplitude_of_isoComplex {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude L a b :=
  fun M i hi => (h M i hi).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      ((tensorRight (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)).mapIso e)).symm

/-- The localisation of a complex of `B`-modules at a prime `q` of `B` has Tor amplitude in
`[a, b]` over `A_p`, where `p = q ∩ A` is the inverse image of `q` in `A`. -/
public abbrev HasTorAmplitudeAt (A : Type u) {B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (K : CochainComplex (ModuleCat.{u} B) ℤ) (q : Ideal B) [q.IsPrime]
    (a b : ℤ) : Prop :=
  letI : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under A) q
  StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
    ((CochainComplex.restrictScalars
      (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))).obj
      ((CochainComplex.extendScalars (algebraMap B (Localization.AtPrime q))).obj K)) a b

/-- The scalar-tower comparison on complexes: restriction along `A → B_q` is restriction along
`A → A_p` after restriction along `A_p → B_q`. -/
private noncomputable def restrictTowerComplexIso (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (q : Ideal B) [q.IsPrime]
    (X : CochainComplex (ModuleCat.{u} (Localization.AtPrime q)) ℤ) :
    letI : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver (q.under A) q
    (CochainComplex.restrictScalars (algebraMap A (Localization.AtPrime q))).obj X ≅
      (CochainComplex.restrictScalars
        (algebraMap A (Localization.AtPrime (q.under A)))).obj
        ((CochainComplex.restrictScalars
          (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))).obj X) := by
  letI : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under A) q
  exact (NatIso.mapHomologicalComplex
    (ModuleCat.restrictScalarsComp'
      (algebraMap A (Localization.AtPrime (q.under A)))
      (algebraMap (Localization.AtPrime (q.under A)) (Localization.AtPrime q))
      (algebraMap A (Localization.AtPrime q))
      (IsScalarTower.algebraMap_eq A (Localization.AtPrime (q.under A))
        (Localization.AtPrime q))) (ComplexShape.up ℤ)).app X

/-- Tor amplitude over `A` passes from `K` to its base change along a flat ring map `B → C`. -/
private theorem hasTorAmplitude_restrictScalars_extendScalars_aux
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Module.Flat B C]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A B)).obj K) a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A C)).obj
        ((CochainComplex.extendScalars (algebraMap B C)).obj K)) a b := by
  intro M i hi
  have hN : IsZero (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyA A B K M i) := by
    rw [← StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff (algebraMap A B),
      (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyARestrictIso A B K M
        i).isZero_iff]
    exact h M i hi
  refine (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyBIso A B C K M
    i).isZero_iff.mpr ?_
  rw [StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff]
  exact (ModuleCat.extendScalars (algebraMap B C)).map_isZero hN

/-- If the localisation of `K` at a prime `q` of `B`, read over `A`, has Tor amplitude in
`[a, b]`, then it has Tor amplitude in `[a, b]` over `A_{q ∩ A}`. -/
private theorem hasTorAmplitudeAt_of_restrictScalars
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (q : Ideal B) [q.IsPrime] (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A (Localization.AtPrime q))).obj
        ((CochainComplex.extendScalars (algebraMap B (Localization.AtPrime q))).obj K)) a b) :
    HasTorAmplitudeAt A K q a b := by
  let _ : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under A) q
  let L := (CochainComplex.extendScalars (algebraMap B (Localization.AtPrime q))).obj K
  refine hasTorAmplitude_of_restrictScalars_isLocalization A
    (Localization.AtPrime (q.under A)) (q.under A).primeCompl _ a b ?_
  exact hasTorAmplitude_of_isoComplex (restrictTowerComplexIso A B q L) a b h

/-- Tor amplitude over `A` survives a flat base change of the coefficient ring: let `A → B → C` be
a tower with `C` flat over `B`, and let `K` be a complex of `B`-modules. If `K`, read over `A`, has
Tor amplitude in `[a, b]`, then so has `C ⊗_B K`, read over `A`. -/
@[ega "0 6.3.1" "more general"]
theorem hasTorAmplitude_restrictScalars_extendScalars_of_flat
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Module.Flat B C]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A B)).obj K) a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A C)).obj
        ((CochainComplex.extendScalars (algebraMap B C)).obj K)) a b := by
  exact hasTorAmplitude_restrictScalars_extendScalars_aux A B C K a b h

/-- If the localisation `K_q` of a complex of `B`-modules at a prime `q` of `B`, read over `A`, has
Tor amplitude in `[a, b]`, then it has Tor amplitude in `[a, b]` over `A_{q ∩ A}`. -/
theorem hasTorAmplitudeAt_of_hasTorAmplitude_extendScalars
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (q : Ideal B) [q.IsPrime] (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A (Localization.AtPrime q))).obj
        ((CochainComplex.extendScalars (algebraMap B (Localization.AtPrime q))).obj K)) a b) :
    HasTorAmplitudeAt A K q a b := by
  exact hasTorAmplitudeAt_of_restrictScalars A B K q a b h

/-- The base change of a `B`-module to `B_q` is its localisation at `q`, as an equivalence of the
underlying types. -/
private noncomputable def extendScalarsLocalizedModuleEquiv
    (B : Type u) [CommRing B] (q : Ideal B) [q.IsPrime] (N : ModuleCat.{u} B) :
    ((ModuleCat.extendScalars (algebraMap B (Localization.AtPrime q))).obj N : Type u) ≃
      LocalizedModule q.primeCompl (N : Type u) :=
  ((StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv B (Localization.AtPrime q)
    N).trans
    (LocalizedModule.equivTensorProduct q.primeCompl (N : Type u)).symm).toEquiv

/-- Tor amplitude over `A` may be tested at the maximal ideals of `B`. -/
private theorem hasTorAmplitude_of_hasTorAmplitudeAt_maximals
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ)
    (h : ∀ (m : Ideal B) (hm : m.IsMaximal),
      letI : m.IsPrime := hm.isPrime
      HasTorAmplitudeAt A K m a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A B)).obj K) a b := by
  intro M i hi
  let N := StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyA A B K M i
  have hN : IsZero N := by
    rw [ModuleCat.isZero_iff_subsingleton]
    apply Module.subsingleton_of_localization_maximal
      (fun (m : Ideal B) (_ : m.IsMaximal) => LocalizedModule m.primeCompl (N : Type u))
      (fun (m : Ideal B) (_ : m.IsMaximal) =>
        LocalizedModule.mkLinearMap m.primeCompl (N : Type u))
    intro m hm
    let _ : m.IsPrime := hm.isPrime
    let _ : Algebra (Localization.AtPrime (m.under A)) (Localization.AtPrime m) :=
      Localization.AtPrime.algebraOfLiesOver (m.under A) m
    have : Module.Flat A (Localization.AtPrime (m.under A)) :=
      IsLocalization.flat (Localization.AtPrime (m.under A)) (m.under A).primeCompl
    have : Module.Flat B (Localization.AtPrime m) :=
      IsLocalization.flat (Localization.AtPrime m) m.primeCompl
    have hbase : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
        ((CochainComplex.restrictScalars (algebraMap A (Localization.AtPrime m))).obj
          ((CochainComplex.extendScalars
            (algebraMap B (Localization.AtPrime m))).obj K)) a b :=
      hasTorAmplitude_of_isoComplex (restrictTowerComplexIso A B m _).symm a b
        (hasTorAmplitude_restrictScalars_of_flat (R := A)
          (S := Localization.AtPrime (m.under A)) _ a b (h m hm))
    have hz := (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyBIso A B
      (Localization.AtPrime m)
      K M i).isZero_iff.mp (hbase M i hi)
    rw [StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff,
      ModuleCat.isZero_iff_subsingleton] at hz
    exact (extendScalarsLocalizedModuleEquiv B m N).subsingleton_congr.mp hz
  exact (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyARestrictIso A B K M
    i).isZero_iff.mp
    ((StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff (algebraMap A B) N).mpr hN)

/-- A complex of `B`-modules has Tor amplitude in `[a, b]` over `A` if and only if its localisation
at every prime ideal `q` of `B` has Tor amplitude in `[a, b]` over `A_{q ∩ A}`; equivalently, it is
enough to test this at every maximal ideal of `B`. -/
@[stacks 0B67]
theorem hasTorAmplitude_iff_localized_at_primes_iff_maximals
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ) :
    (StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
        ((CochainComplex.restrictScalars (algebraMap A B)).obj K) a b ↔
      ∀ (q : Ideal B) [q.IsPrime], HasTorAmplitudeAt A K q a b) ∧
    ((∀ (q : Ideal B) [q.IsPrime], HasTorAmplitudeAt A K q a b) ↔
      ∀ (m : Ideal B) (hm : m.IsMaximal),
        letI : m.IsPrime := hm.isPrime
        HasTorAmplitudeAt A K m a b) := by
  refine ⟨⟨fun h q _ => hasTorAmplitudeAt_of_restrictScalars A B K q a b
      (hasTorAmplitude_restrictScalars_extendScalars_aux A B _ K a b h),
    fun h => hasTorAmplitude_of_hasTorAmplitudeAt_maximals A B K a b fun m _ => h m⟩,
    ⟨fun h m _ => h m, fun h q _ => ?_⟩⟩
  exact hasTorAmplitudeAt_of_restrictScalars A B K q a b
    (hasTorAmplitude_restrictScalars_extendScalars_aux A B _ K a b
      (hasTorAmplitude_of_hasTorAmplitudeAt_maximals A B K a b h))

end

end StacksDraft.TorAmplitude
