module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.SyntomicScheme
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel

/-!
# Perfectness descends along a faithfully flat extension of the source

A perfect morphism stays perfect when a surjective syntomic morphism is removed from in front of
it, and consequently perfectness of morphisms of schemes may be tested after a syntomic — in
particular after an étale — covering of the source.

## Main results

* `AlgebraicGeometry.finiteTorDimensionRingHom_of_faithfullyFlat`: the algebra content, that
  finite Tor dimension of a ring map `R → A` can be read off the composite `R → B` whenever
  `A → B` is faithfully flat.
* `RingHom.Perfect.of_comp_of_faithfullyFlat`: a pseudo-coherent ring map `R → A` is perfect
  when its composite with a faithfully flat `A → B` is.
* `AlgebraicGeometry.Perfect.respectsLeft_syntomic`: precomposition with a syntomic morphism
  preserves perfectness.
* `AlgebraicGeometry.perfect_of_comp_surjective_syntomic_of_isAffine`: the affine case, that a
  perfect composite `g ≫ f` with `g` a surjective syntomic morphism of affine schemes forces `f`
  perfect.
* `AlgebraicGeometry.Perfect.isLocalAtSource_syntomicPrecoverage` and
  `AlgebraicGeometry.Perfect.isLocalAtSource_etalePrecoverage`: perfectness of morphisms of
  schemes is local on the source for the syntomic, hence for the étale, topology.

## Implementation notes

Perfectness of a ring map splits into pseudo-coherence and finite Tor dimension of the target
(inside the proof of `RingHom.Perfect.of_comp_of_faithfullyFlat`), and the two halves descend for
different reasons. Pseudo-coherence is Tag 0698, in the geometric form
`AlgebraicGeometry.pseudoCoherent_of_comp_surjective_syntomic_of_isAffine`. Finite Tor dimension
is Tag 0DJF: for ring maps `R → A → B` with `A → B` faithfully flat, a complex of `A`-modules
has the same Tor amplitude over `R` as its base change to `B`, and the complex to apply this to
is `A` itself placed in degree zero, whose base change is `B`.

Tag 0DJF is stated for the projective-resolution rendering of Tor amplitude,
`StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude`, whereas
`AlgebraicGeometry.HasFiniteTorDimensionRingHom` is stated at the canonical derived tensor
product of Tag 0BYI. For a module placed in degree zero the two agree, both being the vanishing
of the cohomology of the tensor product with a projective resolution of the test module; that
comparison is `hasTorAmplitude0DJF_single_iff_canonical` below, and it rests on
`StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF`, which needs a K-flat,
bounded above, termwise flat model and gets one from the projective resolution.

Once the affine case is available, the passage to arbitrary schemes is the syntomic case of the
criterion of Tag 036H, `AlgebraicGeometry.isLocalAtSource_syntomic_of_affine_descent`, whose
three instance hypotheses are precomposition with a syntomic morphism and the two Zariski
localities of perfectness.

## References

* [The Stacks Project, Lemma 37.60.13 (0698)](https://stacks.math.columbia.edu/tag/0698)
* [The Stacks Project, Lemma 35.26.4 (036H)](https://stacks.math.columbia.edu/tag/036H)
* [The Stacks Project, Lemma 15.68.18 (0DJF)](https://stacks.math.columbia.edu/tag/0DJF)
* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StacksDraft.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Faithfully flat descent of finite Tor dimension -/

section Algebra

variable {R : Type u} [CommRing R]

/-- The chosen projective resolution of a module, placed in nonpositive degrees, is concentrated
in degrees at most zero. -/
private lemma projResComplex_isStrictlyLE (M : ModuleCat.{u} R) :
    (FaithfullyFlat.projResComplex M).IsStrictlyLE 0 := by
  change CochainComplex.IsStrictlyLE
    ((CategoryTheory.ProjectiveResolution.of M).complex.extend
      ComplexShape.embeddingDownNat) 0
  infer_instance

/-- Every term of the chosen projective resolution of a module is projective. -/
private lemma projResComplex_projective (M : ModuleCat.{u} R) (i : ℤ) :
    Projective ((FaithfullyFlat.projResComplex M).X i) := by
  change Projective
    (((CategoryTheory.ProjectiveResolution.of M).complex.extend
      ComplexShape.embeddingDownNat).X i)
  infer_instance

/-- The augmentation of the chosen projective resolution of a module, as a map to the module
placed in degree zero. -/
private noncomputable abbrev projResComplexπ (M : ModuleCat.{u} R) :
    FaithfullyFlat.projResComplex M ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M :=
  (CategoryTheory.ProjectiveResolution.of M).π'

/-- The augmentation of the chosen projective resolution of a module is a quasi-isomorphism. -/
private lemma projResComplexπ_quasiIso (M : ModuleCat.{u} R) :
    QuasiIso (projResComplexπ M) := by
  change QuasiIso
    (HomologicalComplex.extendMap (CategoryTheory.ProjectiveResolution.of M).π
      ComplexShape.embeddingDownNat ≫ _)
  have : QuasiIso (HomologicalComplex.extendMap
      (CategoryTheory.ProjectiveResolution.of M).π ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2
      (CategoryTheory.ProjectiveResolution.quasiIso _)
  infer_instance

/-- For a module placed in degree zero the projective-resolution Tor amplitude of Stacks 0DJF
agrees with the Tor amplitude read at the canonical derived tensor product of Stacks 0BYI.

Both are compared with the Tor amplitude of a projective resolution of the module, which is a
K-flat bounded above complex of flat modules, so that
`StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF` applies to it. -/
private theorem hasTorAmplitude0DJF_single_iff_canonical
    (M : ModuleCat.{u} R) (a b : ℤ) :
    FaithfullyFlat.HasTorAmplitude
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) a b ↔
      HasTorAmplitudeCanonical R
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))
        a b := by
  set P := FaithfullyFlat.projResComplex M
  have hPKF : P.KFlat := (projResComplex_kFlat R M).1
  have hPflat : ∀ i : ℤ, Module.Flat R (P.X i) := fun i => by
    have := projResComplex_projective M i
    infer_instance
  have hPbound : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, fun i hi => by
      have hPle := projResComplex_isStrictlyLE M
      rw [CochainComplex.isStrictlyLE_iff] at hPle
      exact hPle i hi⟩
  have hq : QuasiIso (projResComplexπ M) := projResComplexπ_quasiIso M
  have eQ : DerivedCategory.Q.obj P ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
    asIso (DerivedCategory.Q.map (projResComplexπ M))
  have hsingle : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) a b ↔
      FaithfullyFlat.HasTorAmplitude P a b := by
    refine forall_congr' fun N => forall_congr' fun i => imp_congr_right fun _ => ?_
    have := quasiIso_tensorRight_map (projResComplex_kFlat R N).1 (projResComplexπ M)
    exact (homologyIsoOfQuasiIso
      ((tensorRight (FaithfullyFlat.projResComplex N)).map (projResComplexπ M)) i).isZero_iff.symm
  have hcanon : HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) a b ↔
      HasTorAmplitudeCanonical R (DerivedCategory.Q.obj P) a b := by
    rw [hasTorAmplitudeCanonical_iff_hasFlatRepresentative,
      hasTorAmplitudeCanonical_iff_hasFlatRepresentative]
    exact ⟨hasFlatRepresentative_of_iso eQ.symm, hasFlatRepresentative_of_iso eQ⟩
  rw [hsingle, hcanon, hasTorAmplitudeCanonical_iff_hasFlatRepresentative,
    ← hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R)]
  exact (hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) P hPKF hPbound hPflat a b).symm

/-- The base change of a ring along itself is the ring: `B ⊗_A A ≅ B`. -/
private noncomputable def extendScalarsUnitIso {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) : (ModuleCat.extendScalars g).obj (ModuleCat.of A A) ≅ ModuleCat.of B B :=
  letI := g.toAlgebra
  (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso

/-- An algebra is the restriction of scalars of the algebra viewed over itself. -/
private noncomputable def restrictScalarsUnitIso {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) ≅ ModuleCat.of R A :=
  (FaithfullyFlat.restrictScalarsSelfEquiv R A).toModuleIso


/-- Restricting the algebra `A`, placed in degree zero as a complex of `A`-modules, to `R` gives
the `R`-module `A` placed in degree zero. -/
private noncomputable def restrictScalarsSingleIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    (CochainComplex.restrictScalars (algebraMap R A)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R A) :=
  (Functor.mapCochainComplexSingleFunctor
      (ModuleCat.restrictScalars (algebraMap R A)) 0).app (ModuleCat.of A A) ≪≫
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).mapIso
      (FaithfullyFlat.restrictScalarsSelfEquiv R A).toModuleIso

/-- **Faithfully flat descent of finite Tor dimension.** Let `f : R →+* A` and `g : A →+* B` be
ring maps with `g` faithfully flat. If the composite `g.comp f` has finite Tor dimension, then
so has `f`.

By Stacks 0DJF the complex `A`, placed in degree zero, has the same Tor amplitude over `R` as
its base change `B` along the faithfully flat map `g`. -/
theorem finiteTorDimensionRingHom_of_faithfullyFlat {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] (f : R →+* A) (g : A →+* B) (hg : g.FaithfullyFlat)
    (h : HasFiniteTorDimensionRingHom (g.comp f)) : HasFiniteTorDimensionRingHom f := by
  let : Algebra R A := f.toAlgebra
  let : Algebra A B := g.toAlgebra
  let : Algebra R B := (g.comp f).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat A B := hg
  obtain ⟨a, b, hB⟩ := h
  have hB0 : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R B)) a b :=
    (hasTorAmplitude0DJF_single_iff_canonical (ModuleCat.of R B) a b).mpr hB
  set K : CochainComplex (ModuleCat.{u} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  have hflat : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap A B)) :=
    preservesFiniteLimits_extendScalars hflat
  have : (ModuleCat.extendScalars (algebraMap A B)).Additive := additive_extendScalars hflat
  have eExt : (CochainComplex.extendScalars (algebraMap A B)).obj K ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) :=
    (Functor.mapCochainComplexSingleFunctor
        (ModuleCat.extendScalars (algebraMap A B)) 0).app (ModuleCat.of A A) ≪≫
      (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).mapIso
        (extendScalarsUnitIso (algebraMap A B))
  have hExt : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap R B)).obj
        ((CochainComplex.extendScalars (algebraMap A B)).obj K)) a b :=
    hasTorAmplitude0DJF_of_isoComplex
      ((CochainComplex.restrictScalars (algebraMap R B)).mapIso eExt ≪≫
        restrictScalarsSingleIso R B).symm hB0
  exact ⟨a, b, (hasTorAmplitude0DJF_single_iff_canonical (ModuleCat.of R A) a b).mp
    (hasTorAmplitude0DJF_of_isoComplex (restrictScalarsSingleIso R A)
      ((FaithfullyFlat.hasTorAmplitudeIn_iff_extendScalars R A B K a b).2 hExt))⟩

/-- **Faithfully flat descent of perfectness.** Let `f : R →+* A` and `g : A →+* B` be ring maps
with `g` faithfully flat. If `f` is pseudo-coherent and the composite `g.comp f` is perfect, then
`f` is perfect: finite Tor dimension descends by
`AlgebraicGeometry.finiteTorDimensionRingHom_of_faithfullyFlat`. -/
theorem _root_.RingHom.Perfect.of_comp_of_faithfullyFlat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] (f : R →+* A) (g : A →+* B) (hg : g.FaithfullyFlat)
    (hf : f.PseudoCoherent) (h : (g.comp f).Perfect) : f.Perfect := by
  have htor : HasFiniteTorDimensionRingHom (g.comp f) := by
    algebraize [g.comp f]
    exact (hasFiniteTorDimensionRingHom_iff_forall _).mpr fun D =>
      Algebra.Perfect.moduleHasFiniteTorDimension (h := h) D.comparison D.isLeftDerived
  algebraize [f]
  let D := canonicalCertifiedDerivedTensoring R
  exact (Algebra.perfect_iff_pseudoCoherent_and_moduleHasFiniteTorDimension D.comparison
    D.isLeftDerived).mpr ⟨hf, (hasFiniteTorDimensionRingHom_iff_forall f).mp
      (finiteTorDimensionRingHom_of_faithfullyFlat f g hg htor) D⟩

end Algebra

/-! ### Source locality of perfectness -/

/-- Precomposition with a syntomic morphism preserves perfectness of morphisms of schemes.

A syntomic morphism is flat and locally of finite presentation, hence perfect by Tag 068A, and
perfect morphisms compose by Tag 0689. -/
theorem Perfect.respectsLeft_syntomic :
    MorphismProperty.RespectsLeft (@Perfect.{u} : MorphismProperty Scheme.{u})
      (@Syntomic.{u} : MorphismProperty Scheme.{u}) where
  precomp i hi f hf := by
    have : Flat i := flat hi
    have : LocallyOfFinitePresentation i := locallyOfFinitePresentation hi
    have : Perfect f := hf
    infer_instance

/-- If `g : X' ⟶ X` is a surjective syntomic morphism of affine schemes and `g ≫ f : X' ⟶ Y` is
perfect, then `f : X ⟶ Y` is perfect.

On global sections `g` is a faithfully flat ring map. Pseudo-coherence of `f` is then Tag 0698,
and finite Tor dimension of `f` is faithfully flat descent of Tor amplitude. -/
theorem perfect_of_comp_surjective_syntomic_of_isAffine {X' X Y : Scheme.{u}}
    [IsAffine X'] [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    (hgsurj : Surjective g) (hg : Syntomic g) (hcomp : Perfect (g ≫ f)) : Perfect f := by
  have hpc : PseudoCoherent f :=
    pseudoCoherent_of_comp_surjective_syntomic_of_isAffine g f hgsurj hg
      (@pseudoCoherent_of_perfect _ _ (g ≫ f) hcomp)
  have hff : (g.appTop).hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨flat hg, hgsurj⟩
  have hcomp' : (g.appTop.hom.comp f.appTop.hom).Perfect := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      HasRingHomProperty.appTop (P := @Perfect) (g ≫ f) hcomp
  rw [HasRingHomProperty.iff_of_isAffine (P := @Perfect) (Q := @RingHom.Perfect)]
  exact .of_comp_of_faithfullyFlat _ _ hff (HasRingHomProperty.appTop (P := @PseudoCoherent) f hpc)
    hcomp'

/-- Perfectness of morphisms of schemes is local on the source for the syntomic topology: a
morphism is perfect exactly when its composites with the members of a syntomic covering of its
source are.

This is the syntomic case of the criterion of Tag 036H applied to perfectness, with the affine
case discharged by
`AlgebraicGeometry.perfect_of_comp_surjective_syntomic_of_isAffine`. -/
instance Perfect.isLocalAtSource_syntomicPrecoverage :
    MorphismProperty.IsLocalAtSource (@Perfect.{u} : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic.{u})) :=
  letI := Perfect.respectsLeft_syntomic.{u}
  isLocalAtSource_syntomic_of_affine_descent (@Perfect.{u}) fun g f hgsurj hg hcomp =>
    perfect_of_comp_surjective_syntomic_of_isAffine g f hgsurj hg hcomp

/-- Perfectness of morphisms of schemes is local on the source for the étale topology, an étale
covering family being a syntomic covering family. -/
instance Perfect.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource (@Perfect.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  MorphismProperty.IsLocalAtSource.of_le Scheme.etalePrecoverage_le_syntomicPrecoverage

end AlgebraicGeometry

end
