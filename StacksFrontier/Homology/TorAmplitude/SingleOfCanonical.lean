module

public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel

/-!
# Tor amplitude of a module in degree zero, in the two renderings

For a module placed in cohomological degree zero, Tor amplitude against the canonical derived
tensor product (Stacks 0652) implies the projective-resolution Tor amplitude of Stacks 0DJF.
The chosen projective resolution is a K-flat, bounded-above, termwise flat model of the module,
so `StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF` applies to it, and the
resolution map is a quasi-isomorphism, which carries the conclusion to the module itself.
-/

@[expose] public section

namespace StacksDraft.TorAmplitude

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

/-- For a module placed in cohomological degree zero, Tor amplitude in `[a, b]` against the
canonical derived tensor product (Stacks 0652) is the projective-resolution Tor amplitude of
Stacks 0DJF, read on the single complex of the module. -/
public theorem hasTorAmplitude0DJF_single_of_canonical
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (a b : ℤ)
    (h : HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R)
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) a b) :
    FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) a b := by
  let P := FaithfullyFlat.projResComplex M
  have hPle : P.IsStrictlyLE 0 := by
    show CochainComplex.IsStrictlyLE
      ((CategoryTheory.ProjectiveResolution.of M).complex.extend
        ComplexShape.embeddingDownNat) 0; infer_instance
  have hPKF : P.KFlat := FaithfullyFlat.projResComplex_kFlat M
  have hPflat : ∀ i : ℤ, Module.Flat R (P.X i) := FaithfullyFlat.projResComplex_flat_X M
  have hPbound : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, fun i hi => by rw [CochainComplex.isStrictlyLE_iff] at hPle; exact hPle i hi⟩
  let q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M :=
    (CategoryTheory.ProjectiveResolution.of M).π'
  have hq : QuasiIso q := by
    dsimp [q]
    show QuasiIso
      (HomologicalComplex.extendMap (CategoryTheory.ProjectiveResolution.of M).π
        ComplexShape.embeddingDownNat ≫ _)
    have hπ' : QuasiIso (HomologicalComplex.extendMap
        (CategoryTheory.ProjectiveResolution.of M).π ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2
        (CategoryTheory.ProjectiveResolution.quasiIso _)
    infer_instance
  have eQ : DerivedCategory.Q.obj P ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
    asIso (DerivedCategory.Q.map q)
  have hPcanonical : HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R) (DerivedCategory.Q.obj P) a b :=
    (hasTorAmplitude_of_iso
      (derivedTensor := (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor)
      (comparison := canonicalTensorComparison R)
      (isLeftDerived := canonicalTensorIsLeftDerived R)
      eQ.symm a b).mp h
  have hPtor : FaithfullyFlat.HasTorAmplitude P a b :=
    (hasTorAmplitude_iff_hasTorAmplitude0DJF
      (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R)
      P hPKF hPbound hPflat a b).mp hPcanonical
  intro N i hi
  have hN : IsZero (FaithfullyFlat.derivedTensorHomology P N i) := hPtor N i hi
  have hNres : (FaithfullyFlat.projResComplex N).KFlat := FaithfullyFlat.projResComplex_kFlat N
  have hqN := quasiIso_tensorRight_map hNres q
  have hisoN : IsIso (HomologicalComplex.homologyMap
      ((tensorRight (FaithfullyFlat.projResComplex N)).map q) i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).mp (hqN.quasiIsoAt i)
  exact (asIso (HomologicalComplex.homologyMap
    ((tensorRight (FaithfullyFlat.projResComplex N)).map q) i)).isZero_iff.mp hN

end StacksDraft.TorAmplitude

end
