module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.Homology.TorAmplitude.SingleOfCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksCore.Tactic.StacksAttribute
import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat
import StacksFrontier.Homology.TorAmplitude.ChangeOfRings
import StacksFrontier.Homology.TorAmplitude.Composition
import StacksFrontier.Homology.TorAmplitude.CompositionCanonical
import StacksFrontier.Homology.TorAmplitude.GlobalDimension
import StacksFrontier.Homology.TorAmplitude.Local
import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel

/-!
# Perfectness of a morphism of schemes is affine-local

For a morphism of schemes locally of finite type, perfectness of the maps on sections may be
tested on a single affine open cover of the target together with affine open covers of the
preimages, and then holds on *every* compatible pair of affine opens.

## Main definitions

* `AlgebraicGeometry.HasFiniteTorDimensionRingHom`: a ring homomorphism whose target has finite
  Tor dimension as a module over its source.

## Main results

* `AlgebraicGeometry.finiteTorDimensionRingHom_propertyIsLocal`: finite Tor dimension of a ring
  homomorphism is a local property of ring maps.
* `AlgebraicGeometry.hasFiniteTorDimensionRingHom_iff_forall`: finite Tor dimension of a ring
  homomorphism agrees with the Tor-dimension half of `RingHom.IsPerfectRingMap`.
* `AlgebraicGeometry.exists_affine_openCover_perfect_iff_forall`: Stacks 0686, the equivalence
  of its conditions (1) and (2).
* `AlgebraicGeometry.perfect_iff_exists_affine_openCover`: the same equivalence read against
  `AlgebraicGeometry.Perfect`, which Stacks 0687 defines by condition (2).

## Implementation notes

Perfectness of a ring map splits into pseudo-coherence and finite Tor dimension, and each half is
local for a different reason. Pseudo-coherence is handled by Stacks 067Y, already available as
`AlgebraicGeometry.pseudoCoherent_tfae`. Finite Tor dimension is turned into a
`RingHom.PropertyIsLocal` here, in the sense of Stacks 01SR, which is what lets the affine-local
machinery of `AlgebraicGeometry.HasRingHomProperty` transport it; its four clauses are supplied
by Stacks 066J, 066M and 066N, through
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_derivedTensorProduct`,
`StacksDraft.TorAmplitude.hasTorDimensionLECanonical_iff_hasFlatRepresentative` and the
localisation descent of `StacksFrontier.Homology.TorAmplitude.Local`.

Finite Tor dimension is recorded against the canonical derived tensor product, while
`RingHom.IsPerfectRingMap` quantifies over an arbitrary certified one; the two agree, by
`StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalCertified_iff`, so the quantified form is
reached from the canonical one at the end of the argument.

The derived categories of modules come from `HasDerivedCategory.standard`, which is only ever a
local instance, so it is re-declared here.

## References

* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Lemma 37.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Definition 29.17.1 (01SR)](https://stacks.math.columbia.edu/tag/01SR)
* [The Stacks Project, Lemma 15.66.8 (066J)](https://stacks.math.columbia.edu/tag/066J)
* [The Stacks Project, Lemma 15.66.11 (066M)](https://stacks.math.columbia.edu/tag/066M)
* [The Stacks Project, Lemma 15.66.12 (066N)](https://stacks.math.columbia.edu/tag/066N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory
open StacksDraft.TorAmplitude
open CochainComplex.DerivedTensor
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- A ring homomorphism `f : R → S` has finite Tor dimension when `S`, as a module over `R`
through `f`, has Tor amplitude in some bounded interval. -/
public def HasFiniteTorDimensionRingHom {R : Type u} {S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  let := f.toAlgebra
  ∃ a b : ℤ, HasTorAmplitudeCanonical R
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R S))) a b


private lemma hasTorAmplitudeIn_of_iso {R : Type u} [CommRing R]
    (D : Stacks.TorAmplitudeTriangle.DerivedTensoring R)
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) {a b : ℤ}
    (h : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D K a b) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn D L a b := by
  intro M i hi
  exact (h M i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso ((D.derTensor M).mapIso e.symm))

private lemma hasTorAmplitudeCanonical_of_iso (R : Type u) [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) (a b : ℤ)
    (h : HasTorAmplitudeCanonical R K a b) : HasTorAmplitudeCanonical R L a b :=
  (hasTorAmplitudeIn_canonical_iff R L a b).mp
    (hasTorAmplitudeIn_of_iso _ e ((hasTorAmplitudeIn_canonical_iff R K a b).mpr h))

/-- Homology is invariant under a quasi-isomorphism of complexes. -/
public noncomputable def homologyIsoOfQuasiIso {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (q : K ⟶ L) [QuasiIso q]
    (i : ℤ) : K.homology i ≅ L.homology i := by
  have h : IsIso (HomologicalComplex.homologyMap q i) :=
    (quasiIsoAt_iff_isIso_homologyMap q i).mp (inferInstance : QuasiIsoAt q i)
  exact asIso (HomologicalComplex.homologyMap q i)

private lemma projResComplexProjective {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (i : ℤ) : Projective ((FaithfullyFlat.projResComplex M).X i) := by
  change Projective
    (((CategoryTheory.ProjectiveResolution.of M).complex.extend
      ComplexShape.embeddingDownNat).X i)
  infer_instance

/-- The projective resolution of a module, read as a cochain complex in non-positive degrees, is
K-flat and termwise flat: it is termwise projective, and a bounded-above complex of projectives is
K-flat. -/
public theorem projResComplex_kFlat (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    (FaithfullyFlat.projResComplex M).KFlat ∧
      ∀ i : ℤ, Module.Flat R ((FaithfullyFlat.projResComplex M).X i) :=
  ⟨FaithfullyFlat.projResComplex_kFlat M, FaithfullyFlat.projResComplex_flat_X M⟩

private lemma projResComplexQuasiIso {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) :
    QuasiIso ((CategoryTheory.ProjectiveResolution.of M).π') := by
  change QuasiIso
    (HomologicalComplex.extendMap (CategoryTheory.ProjectiveResolution.of M).π
      ComplexShape.embeddingDownNat ≫ _)
  have hπ : QuasiIso (CategoryTheory.ProjectiveResolution.of M).π :=
    CategoryTheory.ProjectiveResolution.quasiIso _
  have hπ' : QuasiIso (HomologicalComplex.extendMap
      (CategoryTheory.ProjectiveResolution.of M).π ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 hπ
  infer_instance

/-- Projective-resolution Tor amplitude, in the sense of Stacks 0DJF, is invariant under
isomorphism of complexes. -/
public lemma hasTorAmplitude0DJF_of_isoComplex {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) {a b : ℤ}
    (h : FaithfullyFlat.HasTorAmplitude K a b) : FaithfullyFlat.HasTorAmplitude L a b := by
  intro M i hi
  exact (h M i hi).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      ((tensorRight (FaithfullyFlat.projResComplex M)).mapIso e.symm))

/-- The module `S` over `R` is the restriction of scalars of `S` over itself; this is
`StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv`, read as an isomorphism in
the other direction. -/
private noncomputable abbrev algebraModule_restrictScalarsIso {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] : ModuleCat.of R S ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) :=
  (FaithfullyFlat.restrictScalarsSelfEquiv R S).toModuleIso.symm

private noncomputable def restrictScalarsSingleIso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    let F := ModuleCat.restrictScalars (algebraMap A B)
    F.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B C)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A C) := by
  let F := ModuleCat.restrictScalars (algebraMap A B)
  let eBC := algebraModule_restrictScalarsIso (R := B) (S := C)
  let eAC := algebraModule_restrictScalarsIso (R := A) (S := C)
  let eComp := ModuleCat.restrictScalarsComp'App (algebraMap A B) (algebraMap B C)
    (algebraMap A C) (IsScalarTower.algebraMap_eq A B C) (ModuleCat.of C C)
  let e := (F.mapIso eBC) ≪≫ eComp.symm ≪≫ eAC.symm
  exact (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of B C) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e

private instance extendScalarsAdditive {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

private theorem hasTorAmplitudeCanonical_extendScalars_of_flat
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (h : HasTorAmplitudeCanonical A K a b) :
    have := preservesFiniteLimits_extendScalars hf
    have := additive_extendScalars hf
    HasTorAmplitudeCanonical B
      ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj K) a b := by
  apply (hasTorAmplitudeCanonical_iff_hasFlatRepresentative B _ a b).mpr
  apply hasFlatRepresentative_extendScalars (f := f) hf
  exact (hasTorAmplitudeCanonical_iff_hasFlatRepresentative A K a b).mp h


/-- Tor amplitude of a module placed in degree `0` does not depend on whether it is read in the
derived category through a complex of modules or directly. -/
private theorem hasTorAmplitudeCanonical_Q_single_iff (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) (a b : ℤ) :
    HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) a b ↔
    HasTorAmplitudeCanonical R ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) a b :=
  let e := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M
  ⟨hasTorAmplitudeCanonical_of_iso R e a b, hasTorAmplitudeCanonical_of_iso R e.symm a b⟩

/-- If `T` is an `S`-algebra, `S` an `R`-algebra, `T` has Tor amplitude `[a₁, b₁]` over `S` and `S`
has Tor amplitude `[a₂, b₂]` over `R`, then `T` has Tor amplitude `[a₁ + a₂, b₁ + b₂]` over `R`. -/
private theorem hasTorAmplitudeCanonical_single_of_tower
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] {a₁ b₁ a₂ b₂ : ℤ}
    (hK : HasTorAmplitudeCanonical S
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
        (ModuleCat.of S T))) a₁ b₁)
    (hL : HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R S))) a₂ b₂) :
    HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R T))) (a₁ + a₂) (b₁ + b₂) := by
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S T)
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)
  let F := ModuleCat.restrictScalars (algebraMap R S)
  have eQL : DerivedCategory.Q.obj L ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app (ModuleCat.of S S)
  have hB : HasTorAmplitudeCanonical R
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) a₂ b₂ :=
    hasTorAmplitudeCanonical_of_iso R
      ((F.mapDerivedCategory.mapIso eQL) ≪≫
        restrictScalarsSingleIso (A := R) (B := S) (C := S)).symm
      a₂ b₂ ((hasTorAmplitudeCanonical_Q_single_iff R _ a₂ b₂).1 hL)
  have hTensor := StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_derivedTensorProduct
    R S K L a₁ b₁ a₂ b₂ hK hB
  have eUnit : (((canonicalDerivedTensorProduct S).tensor.obj (DerivedCategory.Q.obj K)).obj
      (DerivedCategory.Q.obj L)) ≅ DerivedCategory.Q.obj K :=
    ((canonicalDerivedTensorProduct S).tensor.obj (DerivedCategory.Q.obj K)).mapIso eQL ≪≫
      (canonicalDerivedTensorProduct S).rightUnitor.app (DerivedCategory.Q.obj K)
  have eOut : F.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R T) :=
    F.mapDerivedCategory.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app (ModuleCat.of S T)) ≪≫
      restrictScalarsSingleIso (A := R) (B := S) (C := T)
  exact (hasTorAmplitudeCanonical_Q_single_iff R _ _ _).2
    (hasTorAmplitudeCanonical_of_iso R eOut _ _
      (hasTorAmplitudeCanonical_of_iso R (F.mapDerivedCategory.mapIso eUnit) _ _ hTensor))

private theorem finiteTorDimensionRingHom_comp_localizationTarget
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra S T]
    (f : R →+* S) (s : S) [IsLocalization.Away s T]
    (h : HasFiniteTorDimensionRingHom f) :
    HasFiniteTorDimensionRingHom ((algebraMap S T).comp f) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R T := ((algebraMap S T).comp f).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  obtain ⟨a, b, hab⟩ := h
  have hflat : Module.Flat S T := IsLocalization.flat T (Submonoid.powers s)
  have hK : HasTorAmplitudeCanonical S
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj
        (ModuleCat.of S T))) 0 0 :=
    (hasTorAmplitudeCanonical_Q_single_iff S _ 0 0).2
      ((hasTorDimensionLECanonical_iff_hasFlatRepresentative S (ModuleCat.of S T) 0).2.mpr hflat)
  exact ⟨0 + a, 0 + b, hasTorAmplitudeCanonical_single_of_tower hK hab⟩

private theorem finiteTorDimensionRingHom_comp_localizationSource
    {R T S : Type u} [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T]
    (r : R) [IsLocalization.Away r T] (g : T →+* S)
    (h : HasFiniteTorDimensionRingHom g) :
    HasFiniteTorDimensionRingHom (g.comp (algebraMap R T)) := by
  let : Algebra T S := g.toAlgebra
  let f := g.comp (algebraMap R T)
  let : Algebra R S := f.toAlgebra
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  obtain ⟨a, b, hab⟩ := h
  have hflat : Module.Flat R T := IsLocalization.flat T (Submonoid.powers r)
  have hB0 : HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R T))) 0 0 :=
    (hasTorAmplitudeCanonical_Q_single_iff R _ 0 0).2
      ((hasTorDimensionLECanonical_iff_hasFlatRepresentative R (ModuleCat.of R T) 0).2.mpr hflat)
  exact ⟨a + 0, b + 0, hasTorAmplitudeCanonical_single_of_tower hab hB0⟩

private theorem finiteTorDimensionRingHom_localizationAway
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (r : R) [Algebra R R'] [Algebra S S']
    [IsLocalization.Away r R'] [IsLocalization.Away (f r) S']
    (h : HasFiniteTorDimensionRingHom f) :
    HasFiniteTorDimensionRingHom (IsLocalization.Away.map R' S' f r) := by
  let f' : R' →+* S' := IsLocalization.Away.map R' S' f r
  let : Algebra R S := f.toAlgebra
  let : Algebra R' S' := f'.toAlgebra
  let : Algebra R S' := ((algebraMap R' S').comp (algebraMap R R')).toAlgebra
  have hmap (x : R) : f' (algebraMap R R' x) = algebraMap S S' (f x) := by
    simp [f', IsLocalization.Away.map]
  let : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq hmap
  let : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, f', IsLocalization.Away.map]
  have hlocS : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) S' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact ‹IsLocalization.Away (f r) S'›
  let : Algebra.IsPushout R S R' S' :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers r) R').mp hlocS
  obtain ⟨a, b, hab⟩ := h
  have hDerived : HasTorAmplitudeCanonical R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R S)) a b :=
    (hasTorAmplitudeCanonical_Q_single_iff R _ a b).1 hab
  have hflat : (algebraMap R R').Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat R' (Submonoid.powers r))
  have := preservesFiniteLimits_extendScalars hflat
  have := additive_extendScalars hflat
  have hExt := hasTorAmplitudeCanonical_extendScalars_of_flat
    (algebraMap R R') hflat
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R S)) a b hDerived
  have : Algebra.IsPushout R R' S S' :=
    (Algebra.IsPushout.comm R S R' S').mp (inferInstance : Algebra.IsPushout R S R' S')
  let eAlg := Algebra.IsPushout.equiv R R' S S'
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R R')
  let eLin : F.obj (ModuleCat.of R S) ≃ₗ[R'] S' :=
    (FaithfullyFlat.extendScalarsCarrierEquiv R R' (ModuleCat.of R S)).trans eAlg.toLinearEquiv
  let e := eLin.toModuleIso
  have eF : F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R S)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (F.obj (ModuleCat.of R S)) :=
    (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of R S)
  have hExt' : HasTorAmplitudeCanonical R'
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (F.obj (ModuleCat.of R S))) a b :=
    hasTorAmplitudeCanonical_of_iso R' eF a b hExt
  have hTarget : HasTorAmplitudeCanonical R'
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' S')) a b :=
    hasTorAmplitudeCanonical_of_iso R'
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).mapIso e) a b hExt'
  exact ⟨a, b, (hasTorAmplitudeCanonical_Q_single_iff R' _ a b).2 hTarget⟩

private theorem hasTorAmplitudeCanonical_single_of_0DJF
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (a b : ℤ)
    (h : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) a b) :
    HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) a b := by
  let P := FaithfullyFlat.projResComplex M
  have hPle : P.IsStrictlyLE 0 := by
    change CochainComplex.IsStrictlyLE
      ((CategoryTheory.ProjectiveResolution.of M).complex.extend
        ComplexShape.embeddingDownNat) 0
    infer_instance
  have hPKF : P.KFlat := (projResComplex_kFlat R M).1
  have hPproj : ∀ i : ℤ, Projective (P.X i) := projResComplexProjective M
  have hPflat : ∀ i : ℤ, Module.Flat R (P.X i) := fun _ => inferInstance
  have hPbound : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, fun i hi => by
      rw [CochainComplex.isStrictlyLE_iff] at hPle
      exact hPle i hi⟩
  let q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M :=
    (CategoryTheory.ProjectiveResolution.of M).π'
  have hq : QuasiIso q := projResComplexQuasiIso M
  have eQ : DerivedCategory.Q.obj P ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
    asIso (DerivedCategory.Q.map q)
  have hPtor : FaithfullyFlat.HasTorAmplitude P a b := by
    intro N i hi
    have hN : IsZero (FaithfullyFlat.derivedTensorHomology
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) N i) := h N i hi
    have := quasiIso_tensorRight_map (projResComplex_kFlat R N).1 q
    exact (homologyIsoOfQuasiIso
      ((tensorRight (FaithfullyFlat.projResComplex N)).map q) i).isZero_iff.mpr hN
  have hPcanonical : HasTorAmplitude
        (canonicalDerivedTensorProduct R).tensor (canonicalTensorComparison R)
        (canonicalTensorIsLeftDerived R) (DerivedCategory.Q.obj P) a b :=
      (hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison R)
        (canonicalTensorIsLeftDerived R) P hPKF hPbound hPflat a b).mpr hPtor
  have hPrep := (hasTorAmplitude_iff_hasFlatRepresentative
      (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R)
      (DerivedCategory.Q.obj P) a b).mp hPcanonical
  exact (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) a b).mpr
    (hasFlatRepresentative_of_iso eQ hPrep)


private theorem isZero_of_isZero_finiteAwayLocalizations
    (R : Type u) [CommRing R] (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (N : ModuleCat.{u} R)
    (hN : ∀ r : s, IsZero
      ((ModuleCat.extendScalars (algebraMap R (Localization.Away (r : R)))).obj N)) :
    IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hz (x : (N : Type u)) : x = 0 := by
    apply Module.eq_zero_of_isLocalized_span (s : Set R) hs
      (fun r : s => TensorProduct R (Localization.Away (r : R)) (N : Type u))
      (fun r => TensorProduct.mk R (Localization.Away (r : R)) (N : Type u) 1) x
    intro r
    have : Subsingleton (TensorProduct R (Localization.Away (r : R)) (N : Type u)) :=
      (FaithfullyFlat.extendScalarsCarrierEquiv R (Localization.Away (r : R)) N).toEquiv
        |>.subsingleton_congr.mp (ModuleCat.isZero_iff_subsingleton.mp (hN r))
    exact Subsingleton.elim _ _
  exact subsingleton_of_forall_eq 0 hz


private theorem hasTorAmplitudeCanonical_mono
    (R : Type u) [CommRing R] {K : DerivedCategory (ModuleCat.{u} R)}
    {a b c d : ℤ} (ha : a ≤ c) (hb : d ≤ b)
    (h : HasTorAmplitudeCanonical R K c d) : HasTorAmplitudeCanonical R K a b := by
  obtain ⟨E, hflat, hGE, hLE, e⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K c d).mp h
  exact (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).mpr
    ⟨E, hflat, E.isStrictlyGE_of_ge a c ha, E.isStrictlyLE_of_le d b hb, e⟩

private theorem finiteTorDimensionRingHom_of_localizationFiniteSpanTargetInterval
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Finset S) (hs : Ideal.span (s : Set S) = ⊤)
    (h : ∀ r : s, HasFiniteTorDimensionRingHom
      ((algebraMap S (Localization.Away (r : S))).comp f)) :
    HasFiniteTorDimensionRingHom f := by
  let : Algebra R S := f.toAlgebra
  let aLoc : s → ℤ := fun r => Classical.choose (h r)
  let bLoc : s → ℤ := fun r => Classical.choose (Classical.choose_spec (h r))
  have hLoc (r : s) :
      let C := Localization.Away (r : S)
      let g := (algebraMap S C).comp f
      let : Algebra R C := g.toAlgebra
      let : Module R C := g.toAlgebra.toModule
      HasTorAmplitudeCanonical R
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R C))) (aLoc r) (bLoc r) :=
    Classical.choose_spec (Classical.choose_spec (h r))
  obtain ⟨lo, hlo⟩ := (Set.finite_range aLoc).bddBelow
  obtain ⟨hi, hhi⟩ := (Set.finite_range bLoc).bddAbove
  have htorRestrict : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap R S)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S))) lo hi := by
    intro M i hiOut
    let K : CochainComplex (ModuleCat.{u} S) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)
    have hN := isZero_of_isZero_finiteAwayLocalizations S s hs
      (FaithfullyFlat.derivedTensorHomologyA R S K M i) fun r => by
        let C := Localization.Away (r : S)
        let g := (algebraMap S C).comp (algebraMap R S)
        let : Algebra R C := g.toAlgebra
        let : @IsScalarTower R S C Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
          IsScalarTower.of_algebraMap_eq' rfl
        let : Module R C := g.toAlgebra.toModule
        have hBound := hasTorAmplitude0DJF_single_of_canonical R (ModuleCat.of R C)
          lo hi ((hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
            (canonicalTensorIsLeftDerived R) _ lo hi).mpr
              ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative R _ lo hi).mp
                (hasTorAmplitudeCanonical_mono R (hlo (Set.mem_range_self r))
                  (hhi (Set.mem_range_self r)) (hLoc r))))
        let FSB := ModuleCat.extendScalars (algebraMap S C)
        let MBS := FSB.obj (ModuleCat.of S S)
        let eB : (MBS : Type u) ≃ₗ[C] C :=
          (FaithfullyFlat.extendScalarsCarrierEquiv S C (ModuleCat.of S S)).trans
            (TensorProduct.AlgebraTensorModule.rid S C C)
        let : FSB.Additive :=
          (ModuleCat.extendRestrictScalarsAdj (algebraMap S C)).left_adjoint_additive
        let eExt := FSB.mapCochainComplexSingleFunctor 0
        let FRB := ModuleCat.restrictScalars (algebraMap R C)
        let eRmod := FRB.mapIso eB.toModuleIso
        let eResRB := FRB.mapCochainComplexSingleFunctor 0
        let eLoc := (CochainComplex.restrictScalars (algebraMap R C)).mapIso
            (eExt.app (ModuleCat.of S S)) ≪≫
          eResRB.app MBS ≪≫
          (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).mapIso eRmod
        have hLocAmp : FaithfullyFlat.HasTorAmplitude
            ((CochainComplex.restrictScalars (algebraMap R C)).obj
              ((CochainComplex.extendScalars (algebraMap S C)).obj K)) lo hi :=
          hasTorAmplitude0DJF_of_isoComplex eLoc.symm hBound
        have hflat : Module.Flat S C := IsLocalization.flat C (Submonoid.powers (r : S))
        exact (FaithfullyFlat.isZero_restrictScalars_iff (algebraMap R C) _).mp
          ((FaithfullyFlat.derivedTensorHomologyBIso R S C K M i).isZero_iff.mp
            (hLocAmp M i hiOut))
    exact (FaithfullyFlat.derivedTensorHomologyARestrictIso R S _ M i).isZero_iff.mp
      ((FaithfullyFlat.isZero_restrictScalars_iff (algebraMap R S) _).mpr hN)
  have htor : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R S)) lo hi :=
    hasTorAmplitude0DJF_of_isoComplex
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (algebraModule_restrictScalarsIso (R := R) (S := S))).symm
      (hasTorAmplitude0DJF_of_isoComplex
        (((ModuleCat.restrictScalars (algebraMap R S)).mapCochainComplexSingleFunctor 0).app
          (ModuleCat.of S S)) htorRestrict)
  exact ⟨lo, hi, hasTorAmplitudeCanonical_single_of_0DJF R (ModuleCat.of R S) lo hi htor⟩

/-- Finite Tor dimension of a ring homomorphism is a local property of ring maps in the sense of
Stacks 01SR. -/
public theorem finiteTorDimensionRingHom_propertyIsLocal :
    RingHom.PropertyIsLocal HasFiniteTorDimensionRingHom := by
  classical
  constructor
  · intro R S _ _ f r R' S' _ _ _ _ hR hS hf
    exact finiteTorDimensionRingHom_localizationAway f r hf
  · apply (RingHom.ofLocalizationSpanTarget_iff_finite
      HasFiniteTorDimensionRingHom).2
    intro R S _ _ f s hs hloc
    exact finiteTorDimensionRingHom_of_localizationFiniteSpanTargetInterval f s hs hloc
  · apply (RingHom.ofLocalizationSpan_iff_finite HasFiniteTorDimensionRingHom).2
    intro R S _ _ f s hs hloc
    have htImage : Ideal.span ((s.image f : Finset S) : Set S) = ⊤ := by
      rw [Finset.coe_image, ← Ideal.map_span f (s : Set R), hs, Ideal.map_top]
    have hTarget : ∀ y : s.image f, HasFiniteTorDimensionRingHom
        ((algebraMap S (Localization.Away (y : S))).comp f) := by
      rintro ⟨_, hy⟩
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
      let Rr := Localization.Away r
      let Sr := Localization.Away (f r)
      let g := Localization.awayMap f r
      let comp := g.comp (algebraMap R Rr)
      have hComp := finiteTorDimensionRingHom_comp_localizationSource r g (hloc ⟨r, hr⟩)
      have heq : comp = (algebraMap S Sr).comp f := by
        have hsub : Submonoid.powers r ≤
            Submonoid.comap f (Submonoid.powers (f r)) := by
          rintro x ⟨n, rfl⟩
          exact ⟨n, by simp⟩
        dsimp [comp, g, Localization.awayMap, IsLocalization.Away.map]
        exact IsLocalization.map_comp hsub
      rwa [← heq]
    exact finiteTorDimensionRingHom_of_localizationFiniteSpanTargetInterval
      f (s.image f) htImage hTarget
  · intro R S T _ _ _ _ s _ f hf
    exact finiteTorDimensionRingHom_comp_localizationTarget f s hf


/-- Finite Tor dimension of a ring homomorphism, in the shape in which `RingHom.IsPerfectRingMap`
records it: the target, as a module over the source, has finite Tor dimension computed against
every certified derived tensor product on the source.

The two agree because both are equivalent to the existence of a representative by a complex of
flat modules concentrated in a bounded interval, which does not refer to a derived tensor
product at all. -/
public theorem hasFiniteTorDimensionRingHom_iff_forall {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    HasFiniteTorDimensionRingHom f ↔
      letI := f.toAlgebra
      ∀ D : CertifiedDerivedTensoring.{u, u} R,
        ModuleHasFiniteTorDimension D.tensor D.comparison D.isLeftDerived
          (ModuleCat.of R S) := by
  let := f.toAlgebra
  set K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R S)
  constructor
  · rintro ⟨a, b, htor⟩ D
    exact ⟨a, b, (hasTorAmplitude_iff_hasFlatRepresentative D.comparison D.isLeftDerived K a
      b).mpr ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).mp htor)⟩
  · intro h
    obtain ⟨a, b, hamp⟩ := h (canonicalCertifiedDerivedTensoring R)
    exact ⟨a, b, (hasTorAmplitudeIn_canonicalCertified_iff R K a b).mp hamp⟩

/-- For a locally finite type morphism of schemes, perfectness on some affine open covering
of the target and affine open coverings of its preimages is equivalent to perfectness on every
pair of affine opens for which the source open maps into the target open. -/
@[stacks 0686]
theorem exists_affine_openCover_perfect_iff_forall
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    (∃ (J : Type u) (V : J → S.Opens),
      IsOpenCover V ∧
        (∀ j, IsAffineOpen (V j)) ∧
        ∀ j, ∃ (I : Type u) (U : I → X.Opens)
          (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
          (∀ i, IsAffineOpen (U i)) ∧
            ∀ i,
              let g := (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom
              letI := g.toAlgebra
              ∀ D : CertifiedDerivedTensoring Γ(S, V j),
                RingHom.IsPerfectRingMap Γ(S, V j) Γ(X, U i)
                  D.tensor D.comparison D.isLeftDerived) ↔
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
        (hUV : U ≤ f ⁻¹ᵁ V),
          let g := (f.appLE V U hUV).hom
          letI := g.toAlgebra
          ∀ D : CertifiedDerivedTensoring Γ(S, V),
            RingHom.IsPerfectRingMap Γ(S, V) Γ(X, U)
              D.tensor D.comparison D.isLeftDerived := by
  constructor
  · rintro ⟨J, V, hVcover, hVaff, hVpre⟩
    have hpcCover :
        ∃ (J : Type u) (V : J → S.Opens),
          IsOpenCover V ∧
            (∀ j, IsAffineOpen (V j)) ∧
              ∀ j, ∃ (I : Type u) (U : I → X.Opens)
                (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
                (∀ i, IsAffineOpen (U i)) ∧
                  ∀ i,
                    let g := (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom
                    let := g.toAlgebra
                    Algebra.PseudoCoherent Γ(S, V j) Γ(X, U i) := by
      refine ⟨J, V, hVcover, hVaff, fun j => ?_⟩
      obtain ⟨I, U, hU, hUaff, hperf⟩ := hVpre j
      exact ⟨I, U, hU, hUaff, fun i => (hperf i (canonicalCertifiedDerivedTensoring _)).1⟩
    have hpcAll := (pseudoCoherent_tfae f).out 1 2 |>.mp hpcCover
    have htorAll : ∀ (U : X.Opens) (_ : IsAffineOpen U) (W : S.Opens) (_ : IsAffineOpen W)
        (hUW : U ≤ f ⁻¹ᵁ W), HasFiniteTorDimensionRingHom (f.appLE W U hUW).hom := by
      let Pm : MorphismProperty Scheme.{u} := affineLocally HasFiniteTorDimensionRingHom
      let : HasRingHomProperty Pm HasFiniteTorDimensionRingHom :=
        ⟨finiteTorDimensionRingHom_propertyIsLocal, rfl⟩
      have hSourceStable : RingHom.StableUnderCompositionWithLocalizationAwaySource
          HasFiniteTorDimensionRingHom := by
        intro R Rloc T _ _ _ _ r _ g hg
        exact finiteTorDimensionRingHom_comp_localizationSource r g hg
      have hPm : Pm f := by
        refine (HasRingHomProperty.iff_exists_appLE (P := Pm) (f := f) hSourceStable).2
          fun x => ?_
        obtain ⟨j, hxj⟩ := hVcover.exists_mem (f x)
        obtain ⟨I, Uj, hUj, hUjaff, hperf⟩ := hVpre j
        obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, Uj i by rwa [hUj])
        exact ⟨⟨V j, hVaff j⟩, ⟨Uj i, hUjaff i⟩, hxi, (le_iSup Uj i).trans hUj.le,
          (hasFiniteTorDimensionRingHom_iff_forall _).mpr fun D => (hperf i D).2⟩
      intro U hU W hW hUW
      exact (HasRingHomProperty.iff_appLE (P := Pm) (f := f)).mp hPm ⟨W, hW⟩ ⟨U, hU⟩ hUW
    intro U hU V hV hUV _ D
    exact ⟨hpcAll U hU V hV hUV,
      (hasFiniteTorDimensionRingHom_iff_forall _).mp (htorAll U hU V hV hUV) D⟩
  · intro hAll
    have hU (W : X.Opens) :
        (⨆ A : {A : X.affineOpens // (A : X.Opens) ≤ W}, (A.1 : X.Opens)) = W := by
      refine le_antisymm (iSup_le fun A => A.2) fun x hx => ?_
      obtain ⟨_, ⟨A₀, hA₀, rfl⟩, hxA, hAsub⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact Opens.mem_iSup.mpr ⟨⟨⟨A₀, hA₀⟩, hAsub⟩, hxA⟩
    refine ⟨S.affineOpens, fun j => j.1, ?_, fun j => j.2, fun j => ?_⟩
    · exact IsOpenCover.mk (iSup_affineOpens_eq_top S)
    · exact ⟨_, _, hU _, fun i => i.1.2, fun i => hAll _ i.1.2 _ j.2 _⟩

/-- **Stacks 0686, read against `AlgebraicGeometry.Perfect`.** A morphism of schemes locally of
finite type is perfect exactly when there are an affine open cover of the target and, over each
of its members, an affine open cover of the preimage, on which every map on sections is a perfect
ring map.

Stacks 0687 defines perfectness by condition (2) of Stacks 0686, so this is condition (1) of that
lemma restated for the resulting class. -/
theorem perfect_iff_exists_affine_openCover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    Perfect f ↔
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i,
                let g := (f.appLE (V j) (U i) ((le_iSup U i).trans hU.le)).hom
                letI := g.toAlgebra
                ∀ D : CertifiedDerivedTensoring Γ(S, V j),
                  RingHom.IsPerfectRingMap Γ(S, V j) Γ(X, U i)
                    D.tensor D.comparison D.isLeftDerived :=
  ⟨fun h => (exists_affine_openCover_perfect_iff_forall f).mpr
      (@Perfect.perfect_appLE _ _ f h),
    fun h => { perfect_appLE := (exists_affine_openCover_perfect_iff_forall f).mp h }⟩


end AlgebraicGeometry

end
