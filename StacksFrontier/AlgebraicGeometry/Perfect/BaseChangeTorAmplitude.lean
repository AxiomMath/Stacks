module

public import StacksFrontier.Homology.TorAmplitude.CompositionCanonical
public import StacksFrontier.Homology.TorAmplitude.BaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Tor amplitude under a Tor-independent base change of local rings

Transfer results for canonical Tor amplitude of complexes of modules over commutative rings
along extension and restriction of scalars, and in particular along a Tor independent base
change of rings.

## Main results

* `hasTorAmplitudeCanonical_torIndependentBaseChange`: for a pushout square of commutative
  rings whose two intermediate corners are Tor independent over the base, derived extension
  of scalars along one side preserves canonical Tor amplitude read over the other.
* `hasTorAmplitudeCanonical_torIndependent_flatBaseChange`: the same with the upper-right
  corner replaced by a flat extension of the pushout.
* `ringTorIndependent_of_schemeTorIndependent_stalks`: if two morphisms of schemes over `S` are
  Tor independent, then the local rings at points with a common image in `S` are Tor
  independent over the local ring of `S`.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 066L](https://stacks.math.columbia.edu/tag/066L)
* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
  RingedSpaceModuleAdjunction Opposite
open CochainComplex.DerivedTensor CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.BaseChangeTorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars carries canonical Tor amplitude to the same interval. -/
public theorem hasTorAmplitudeCanonical_extendScalars
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (E : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hE : HasTorAmplitudeCanonical R E a b) :
    HasTorAmplitudeCanonical A
      ((totalDerivedExtensionScalars (algebraMap R A)).functor.obj E) a b := by
  have hE'' : HasTorAmplitude (canonicalDerivedTensorProduct R).tensor
      (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R) E a b :=
    (hasTorAmplitudeIn_iff_hasTorAmplitude (canonicalDerivedTensorProduct R)
      (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R) E a b).mp
        ((hasTorAmplitudeIn_canonical_iff R E a b).mpr hE)
  let D := totalDerivedExtensionScalars (algebraMap R A)
  have h := hasTorAmplitude_derivedExtendScalars D.functor D.comparison D.isLeftDerived
    (canonicalDerivedTensorProduct R).tensor (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R)
    (canonicalDerivedTensorProduct A).tensor (canonicalTensorComparison A)
    (canonicalTensorIsLeftDerived A) E a b hE''
  exact (hasTorAmplitudeIn_canonical_iff A _ a b).mp
    ((hasTorAmplitudeIn_iff_hasTorAmplitude (canonicalDerivedTensorProduct A)
      (canonicalTensorComparison A) (canonicalTensorIsLeftDerived A) _ a b).mpr h)

/-- Canonical Tor amplitude depends only on the isomorphism class of the derived object. -/
public theorem hasTorAmplitudeCanonical_of_iso
    {R : Type u} [CommRing R]
    {E F : DerivedCategory (ModuleCat.{u} R)} (e : E ≅ F) (a b : ℤ)
    (hE : HasTorAmplitudeCanonical R E a b) :
    HasTorAmplitudeCanonical R F a b :=
  (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R F a b).2
    (hasFlatRepresentative_of_iso e
      ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative R E a b).1 hE))

/-- Exact functors that preserve flat modules preserve Tor-amplitude bounds. -/
public theorem hasTorAmplitudeCanonical_map_of_preservesFlat
    {R S : Type u} [CommRing R] [CommRing S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : ModuleCat.{u} R, Module.Flat R M → Module.Flat S (F.obj M))
    (E : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hE : HasTorAmplitudeCanonical R E a b) :
    HasTorAmplitudeCanonical S (F.mapDerivedCategory.obj E) a b := by
  obtain ⟨K, hflat, hge, hle, ⟨e⟩⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R E a b).mp hE
  exact (hasTorAmplitudeCanonical_iff_hasFlatRepresentative S _ a b).mpr
    ⟨(F.mapHomologicalComplex (.up ℤ)).obj K, fun i => hF (K.X i) (hflat i), inferInstance,
      inferInstance, ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K⟩⟩

/-- Canonical Tor amplitude in `[a, b]` of an object of `D(R)` implies the same bound for its
image in `D(ULift R)` under `moduleLift`. -/
public theorem hasTorAmplitudeCanonical_moduleLift
    {R : Type u} [CommRing R] (E : DerivedCategory (ModuleCat.{u} R))
    (a b : ℤ) (hE : HasTorAmplitudeCanonical R E a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u} E a b := by
  refine hasTorAmplitudeCanonical_map_of_preservesFlat (moduleLift.{u, u, u} R) ?_ E a b hE
  intro M hM
  change Module.Flat (ULift.{u} R) (ULift.{u} M)
  exact Module.Flat.ulift_left_iff.mpr (Module.Flat.ulift_right_iff.mpr hM)

/-- Let `T` be a pushout of `A` and `B` over `R` with `A` and `B` Tor independent over `R`. If an
object `E` of `D(A)` has canonical Tor amplitude in `[a, b]` as an object of `D(R)`, then its
derived extension of scalars to `T` has canonical Tor amplitude in `[a, b]` as an object of
`D(B)`. -/
public theorem hasTorAmplitudeCanonical_torIndependentBaseChange
    {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
    [IsScalarTower R A T] [IsScalarTower R B T] [Algebra.IsPushout R A B T]
    (hTor : RingTheory.TorIndependence.TorIndependent R A B)
    (E : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (hE : HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj E) a b) :
    HasTorAmplitudeCanonical B
      ((ModuleCat.restrictScalars (algebraMap B T)).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars (algebraMap A T)).functor.obj E)) a b := by
  let Dbase := totalDerivedExtensionScalars.{u, u, u} (algebraMap R B)
  have hbase := hasTorAmplitudeCanonical_extendScalars (R := R) (A := B)
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj E) a b hE
  let Dtop := totalDerivedExtensionScalars.{u, u, u} (algebraMap A T)
  let sq : (algebraMap A T).comp (algebraMap R A) =
      (algebraMap B T).comp (algebraMap R B) :=
    (IsScalarTower.algebraMap_eq R A T).symm.trans
      (IsScalarTower.algebraMap_eq R B T)
  let cmp :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1,
      u + 1}
    R A B T _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap R B) (algebraMap A T) (algebraMap B T)
    sq Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  have : IsIso cmp.2.1 :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u,
      u, u + 1, u + 1, u + 1, u + 1}
    R A B T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hTor Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  exact hasTorAmplitudeCanonical_of_iso (R := B) (asIso (cmp.2.1.app E)) a b hbase

/-- Restriction of scalars along a ring isomorphism `R ≃+* S` preserves canonical Tor
amplitude in `[a, b]`. -/
public theorem hasTorAmplitudeCanonical_restrictScalars_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (E : DerivedCategory (ModuleCat.{u} S)) (a b : ℤ)
    (hE : HasTorAmplitudeCanonical S E a b) :
    HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj E) a b := by
  apply hasTorAmplitudeCanonical_map_of_preservesFlat _ _ E a b hE
  intro M hM
  let : Algebra R S := e.toRingHom.toAlgebra
  let N := (ModuleCat.restrictScalars e.toRingHom).obj M
  let : Module S N := M.isModule
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat S N := hM
  have : Module.Flat R S := RingHom.Flat.of_bijective e.bijective
  exact Module.Flat.trans R S N

/-- For a cochain complex `K` of `R`-modules, the canonical Tor amplitude in `[a, b]` of the image
of `K` in `D(ULift R)` under `moduleLift` implies that of `K` in `D(R)`. -/
public theorem hasTorAmplitudeCanonical_of_moduleLift
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hK : HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj K) a b) :
    HasTorAmplitudeCanonical R (DerivedCategory.Q.obj K) a b := by
  let F := moduleLift.{u, u, u} R
  let U := ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} R ≃+* R).symm.toRingHom
  have h := hasTorAmplitudeCanonical_restrictScalars_ringEquiv
    (ULift.ringEquiv : ULift.{u} R ≃+* R).symm
    (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) a b hK
  let e : ((U.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≅ K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (ULift.moduleEquiv : ULift.{u} (K.X i) ≃ₗ[R] K.X i).toModuleIso)
      (by intro i j hij; ext m; rfl)
  exact hasTorAmplitudeCanonical_of_iso
    (U.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
      U.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso e) a b h

/-- A flat module placed in degree `0` is a K-flat cochain complex. -/
public theorem single_kFlat_of_flat
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : Module.Flat R M) :
    CochainComplex.KFlat ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  have hflat : ∀ i, Module.Flat R (K.X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact @Module.Flat.of_linearEquiv R M _ _ _ _ _ _ hM
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).toLinearEquiv
    · have hz : IsZero (K.X i) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
      exact fun _ _ _ _ _ _ _ _ x y _ => Subsingleton.elim x y
  exact CochainComplex.KFlat.kFlat_of_flat K 0

/-- Let `R → A → B` be ring maps with `B` flat over `A`, and let `K` be a K-flat complex of
`A`-modules whose restriction to `R` has canonical Tor amplitude in `[a, b]`. Then the complex
`K ⊗_A B`, restricted to `R`, has canonical Tor amplitude in `[a, b]`. -/
public theorem hasTorAmplitudeCanonical_restrict_flat_extension
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.Flat A B]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) (a b : ℤ)
    (hamp : HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) a b) :
    HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj K)))
      a b := by
  let N := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  have hN : Module.Flat A N := by
    let e : B ≃ₗ[A] N :=
      { toFun := id, invFun := id, left_inv := fun _ => rfl,
        right_inv := fun _ => rfl, map_add' := fun _ _ => rfl,
        map_smul' := fun r m => Algebra.smul_def r m }
    exact (Module.Flat.equiv_iff e).mp inferInstance
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N
  have hL : HasTorAmplitudeCanonical A (DerivedCategory.Q.obj L) 0 0 :=
    hasTorAmplitudeCanonical_of_iso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app N) 0 0
      ((hasTorDimensionLECanonical_iff_hasFlatRepresentative A N 0).2.mpr hN)
  have h := hasTorAmplitudeCanonical_derivedTensorProduct R A L K 0 0 a b hL hamp
  simp only [zero_add] at h
  let F := ModuleCat.restrictScalars (algebraMap R A)
  let e₁ := (canonicalDerivedTensorProduct A).comparison L K (single_kFlat_of_flat N hN) hK
  let e₂ := StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso N K
  let e₃ : tensorLeft N ≅
      ModuleCat.extendScalars (algebraMap A B) ⋙
        ModuleCat.restrictScalars (algebraMap A B) :=
    NatIso.ofComponents (fun M => Iso.refl _) (by intros; rfl)
  let e₄ := (NatIso.mapHomologicalComplex e₃ (.up ℤ)).app K
  have h' := hasTorAmplitudeCanonical_of_iso
    (F.mapDerivedCategory.mapIso (e₁ ≪≫ DerivedCategory.Q.mapIso (e₂ ≪≫ e₄)) ≪≫
      F.mapDerivedCategoryFactors.app _) a b h
  let e₅ := (NatIso.mapHomologicalComplex
    (ModuleCat.restrictScalarsComp' (algebraMap R A) (algebraMap A B)
      (algebraMap R B) (IsScalarTower.algebraMap_eq R A B)) (.up ℤ)).app
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (.up ℤ)).obj K)
  exact hasTorAmplitudeCanonical_of_iso (DerivedCategory.Q.mapIso e₅.symm) a b h'

/-- Let `T` be a pushout of `A` and `B` over `R` with `A` and `B` Tor independent over `R`, and
let `C` be a flat `T`-algebra. If `K` is a K-flat complex of `A`-modules whose restriction to `R`
has canonical Tor amplitude in `[a, b]`, then `K ⊗_A C`, restricted to `B`, has canonical Tor
amplitude in `[a, b]`. -/
public theorem hasTorAmplitudeCanonical_torIndependent_flatBaseChange
    {R A B T C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [CommRing C] [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T]
    [Algebra B T] [IsScalarTower R A T] [IsScalarTower R B T]
    [Algebra.IsPushout R A B T]
    [Algebra A C] [Algebra B C] [Algebra T C]
    [IsScalarTower A T C] [IsScalarTower B T C] [Module.Flat T C]
    (htor : RingTheory.TorIndependence.TorIndependent R A B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) (a b : ℤ)
    (hamp : HasTorAmplitudeCanonical R
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) a b) :
    HasTorAmplitudeCanonical B
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap B C)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap A C)).mapHomologicalComplex (.up ℤ)).obj K)))
      a b := by
  let D := totalDerivedExtensionScalars (algebraMap A T)
  have : IsIso (D.comparison.app K) := D.comparison_isIso_of_kFlat K hK
  let KT := ((ModuleCat.extendScalars (algebraMap A T)).mapHomologicalComplex (.up ℤ)).obj K
  have hKT : CochainComplex.KFlat KT :=
    CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars (algebraMap A T) K hK
  have hbase := hasTorAmplitudeCanonical_torIndependentBaseChange
    (T := T) htor (DerivedCategory.Q.obj K) a b hamp
  have hbase' := hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars (algebraMap B T)).mapDerivedCategory.mapIso
      (asIso (D.comparison.app K))) a b hbase
  have hlocal := hasTorAmplitudeCanonical_restrict_flat_extension
    (R := B) (A := T) (B := C) KT hKT a b hbase'
  let e : ModuleCat.extendScalars (algebraMap A C) ≅
      ModuleCat.extendScalars (algebraMap A T) ⋙ ModuleCat.extendScalars (algebraMap T C) :=
    eqToIso (congrArg (fun f : A →+* C => ModuleCat.extendScalars f)
      (IsScalarTower.algebraMap_eq A T C)) ≪≫
        ModuleCat.extendScalarsComp (algebraMap A T) (algebraMap T C)
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app K
  exact hasTorAmplitudeCanonical_of_iso
    (DerivedCategory.Q.mapIso
      (((ModuleCat.restrictScalars (algebraMap B C)).mapHomologicalComplex (.up ℤ)).mapIso
        ec.symm)) a b hlocal

/-- If morphisms of schemes `f : X ⟶ S` and `g : Y ⟶ S` are Tor independent, then for points
`x ∈ X` and `y ∈ Y` with `f x = g y` the local rings `𝒪_{X,x}` and `𝒪_{Y,y}` are Tor independent
over `𝒪_{S,f x}`. -/
public theorem ringTorIndependent_of_schemeTorIndependent_stalks
    {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (htor : AlgebraicGeometry.TorIndependent f g)
    (x : X) (y : Y) (hxy : f.base x = g.base y) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
      (eqToHom (congrArg (fun z => S.presheaf.stalk z) hxy) ≫ g.stalkMap y).hom.toAlgebra
    RingTheory.TorIndependence.TorIndependent (S.presheaf.stalk (f.base x))
      (X.presheaf.stalk x) (Y.presheaf.stalk y) := by
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z) hxy) ≫ g.stalkMap y).hom.toAlgebra
  exact (RingTheory.TorIndependence.torIndependent_iff_isZero_tor
    (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (Y.presheaf.stalk y)).2
      (htor.at_stalks x y hxy)
end AlgebraicGeometry.BaseChangeTorAmplitude

end
