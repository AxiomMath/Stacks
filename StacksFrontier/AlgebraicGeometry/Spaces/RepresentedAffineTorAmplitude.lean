module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentTests
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.Termwise

/-!
# Tor amplitude on an affine algebraic space

Let `U` be an object of the big fppf site whose underlying scheme is affine, with ring of global
functions `R`, let `X` be the algebraic space `yoneda.obj U`, and let `Φ : D(R) ⥤ D(𝒪_X)` be the
derived associated-module functor.  For `M ∈ D(R)` the object `Φ(M)` has Tor amplitude in
`[a, b]` exactly when `M` does, and already when its derived tensor products with the
quasi-coherent `𝒪_X`-modules have no cohomology outside `[a, b]`.  Since every object of
`D_QCoh(𝒪_X)` is some `Φ(M)`, this is the affine case of Stacks 08IL: for `E ∈ D_QCoh(𝒪_X)`,
condition (2) of Stacks 08IL implies that `E` has Tor amplitude in `[a, b]`.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_of_representedAffine_tests`: the vanishing
  of `Hⁱ(Φ(M) ⊗^L N^~)` outside `[a, b]` for all `R`-modules `N` gives Tor amplitude of `M` in
  `[a, b]`.
* `AlgebraicGeometry.Space.hasTorAmplitude_representedAffineDerivedAssociated_iff`: `Φ(M)` has
  Tor amplitude in `[a, b]` if and only if `M` has.
* `AlgebraicGeometry.Space.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_representedAffine`:
  the affine case of Stacks 08IL, (2) implies (1).

## References

* [Stacks Project, Tag 08IL](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 08EA](https://stacks.math.columbia.edu/tag/08EA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- `SheafOfModules.hasBinBiprod`, universe-polymorphic in the module universe, gives a second
-- route to the biproducts of sheaves of modules, and the derived tensor product of the small étale
-- site no longer elaborates against it: the two routes leave the module universe stuck at
-- `max ?v ?w =?= u`.
attribute [-instance] SheafOfModules.hasBinBiprod

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The associated module of an `R`-module is zero exactly when the module is. -/
theorem isZero_representedAffineAssociated_obj_iff
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    IsZero ((representedAffineAssociated B S hS U).obj M) ↔ IsZero M := by
  refine ⟨fun h => ?_, fun h => Functor.map_isZero _ h⟩
  rw [IsZero.iff_id_eq_zero]
  refine (representedAffineAssociated B S hS U).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- The associated complex of the termwise tensor complex `P ⊗_R N` is the termwise tensor
complex `P^~ ⊗ N^~`. -/
def representedAffineTensorRowIso (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S
    hS).obj U, ⊤)) ℤ) (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (StacksDraft.TorAmplitude.Termwise.tensorComplex P N) ≅
      CochainComplex.KFlatBifunctor.rowComplex (representedAffineTensor B S hS U)
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((representedAffineAssociated B S hS U).obj N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (representedAffineAssociatedTensorIso B S hS U N).app (P.X n))
    (fun i j _ => ((representedAffineAssociatedTensorIso B S hS U N).hom.naturality (P.d i j)).symm)

/-- The associated complex of a bounded above complex of projective `R`-modules is K-flat. -/
theorem isKFlat_representedAffineAssociated_mapHomologicalComplex
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (m : ℤ)
    [P.IsStrictlyLE m] (hP : ∀ i, Projective (P.X i)) :
    Stacks.SheafOfModules.IsKFlat
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O
      (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        P) := by
  refine Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat _ _ ⟨m, ?_⟩ fun i => ?_
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (representedAffineAssociated B S hS U)
      (P.isZero_of_isStrictlyLE m i hi)
  · have := hP i
    exact isFlat_representedAffineAssociated_obj_of_projective B S hS U (P.X i)

/-- **The derived tensor product of `P^~` with `N^~`** for a bounded above complex `P` of
projective `R`-modules: the associated complex of the termwise tensor complex `P ⊗_R N`. -/
def representedAffineDerivedTensorIso
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (m : ℤ)
    [P.IsStrictlyLE m] (hP : ∀ i, Projective (P.X i))
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
          (DerivedCategory.Q.obj
            (((representedAffineAssociated B S hS U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((representedAffineAssociated B S hS U).obj N)) ≅
      DerivedCategory.Q.obj
        (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)) :=
  ((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
        (DerivedCategory.Q.obj
          (((representedAffineAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P))).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
        ((representedAffineAssociated B S hS U).obj N)) ≪≫
    (smallEtaleDerivedTensorProduct B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).comparisonLeft
      _ _ (isKFlat_representedAffineAssociated_mapHomologicalComplex B S hS U P m hP) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso _ _ _) ≪≫
    DerivedCategory.Q.mapIso (representedAffineTensorRowIso B S hS U P N).symm

/-- Transfer vanishing of `G (A ⊗ X)` along an isomorphism `A ≅ A'`. -/
private theorem isZero_obj_obj_of_iso {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms E] (T : C ⥤ C ⥤ D) (G : D ⥤ E) {A A' : C} (e : A ≅ A') (X : C)
    (h : IsZero (G.obj ((T.obj A').obj X))) : IsZero (G.obj ((T.obj A).obj X)) :=
  h.of_iso (G.mapIso ((T.mapIso e).app X))

/-- **Tor amplitude of `M ∈ D(R)` from the derived tensor products of `Φ(M)` with the associated
modules.**  If `Hⁱ(Φ(M) ⊗^L N^~) = 0` for every `R`-module `N` and every `i ∉ [a, b]`, then `M`
has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitudeCanonical_of_representedAffine_tests
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) (a b : ℤ)
    (hE : ∀ (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (i : ℤ),
      i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) i).obj
        (((smallEtaleDerivedTensor B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).obj
            ((representedAffineDerivedAssociated B S hS U).obj M)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((representedAffineAssociated B S hS U).obj N))))) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      M a b := by
  set R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  set T := smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  set Ã := representedAffineAssociated B S hS U
  have hunit : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((representedAffineDerivedAssociated B S hS U).obj M)) := by
    intro i hi
    refine (hE R₀ i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso ?_)
    exact (T.unitIso _).symm ≪≫
      (T.tensor.obj ((representedAffineDerivedAssociated B S hS U).obj M)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (representedAffineAssociatedUnitIso B S hS U).symm)
  have hMLE : M.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    refine (isZero_representedAffineAssociated_obj_iff B S hS U _).mp
      ((hunit i (by simp only [Set.mem_Icc]; omega)).of_iso ?_)
    exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso Ã i).app M).symm
  obtain ⟨C, hCLE, ⟨eC⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE M b
  obtain ⟨P, m, π, hPLE, hPproj, hπ⟩ :=
    StacksDraft.TorAmplitude.exists_projective_resolution C b
  have hflat : ∀ i : ℤ, Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X i) :=
    fun i => by
      have := hPproj i
      infer_instance
  have hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨m, fun i hi => P.isZero_of_isStrictlyLE m i hi⟩
  have eP : DerivedCategory.Q.obj P ≅ M := asIso (DerivedCategory.Q.map π) ≪≫ eC.symm
  refine (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
    _ M a b).mpr ?_
  refine (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
    (StacksDraft.TorAmplitude.canonicalTensorComparison _)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived _) M a b).mp ?_
  refine (StacksDraft.TorAmplitude.hasTorAmplitude_of_iso eP a b).mp ?_
  rw [StacksDraft.TorAmplitude.hasTorAmplitude_iff_termwise_of_flat
    (StacksDraft.TorAmplitude.canonicalTensorComparison _)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived _) P hbounded hflat a b]
  intro N i hi
  have eT : (representedAffineDerivedAssociated B S hS U).obj M ≅
      DerivedCategory.Q.obj ((Ã.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    (representedAffineDerivedAssociated B S hS U).mapIso eP.symm ≪≫
      Ã.mapDerivedCategoryFactors.app P
  have hz := hE N i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi)
  have hz2 : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (DerivedCategory.Q.obj ((Ã.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)))) :=
    (isZero_obj_obj_of_iso _ _ eT.symm _ hz).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        (representedAffineDerivedTensorIso B S hS U P m hPproj N).symm)
  refine (isZero_representedAffineAssociated_obj_iff B S hS U _).mp (hz2.of_iso ?_)
  exact ((DerivedCategory.homologyFunctorFactors _ i).app
      ((Ã.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)) ≪≫
    (StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso Ã i).app
      (StacksDraft.TorAmplitude.Termwise.tensorComplex P N)).symm

/-- **Tor amplitude of `Φ(M)` from Tor amplitude of `M`.**  If `M ∈ D(R)` has Tor amplitude in
`[a, b]`, then so has `Φ(M)`. -/
theorem hasTorAmplitude_representedAffineDerivedAssociated_of_hasTorAmplitudeCanonical
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) (a b : ℤ)
    (hM : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) M a b) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      ((representedAffineDerivedAssociated B S hS U).obj M) a b := by
  obtain ⟨P, hPflat, hPGE, hPLE, ⟨e⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ M a b).mp hM
  refine Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative _ _ a b
    (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (fun i => ?_) (fun i hi => ?_)
    (((representedAffineDerivedAssociated B S hS U).mapIso e) ≪≫
      (representedAffineAssociated B S hS U).mapDerivedCategoryFactors.app P).symm
  · have := hPflat i
    exact isFlat_representedAffineAssociated_obj B S hS U (P.X i)
  · rcases (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi : i < a ∨ b < i) with h | h
    · exact Functor.map_isZero (representedAffineAssociated B S hS U)
        (P.isZero_of_isStrictlyGE a i h)
    · exact Functor.map_isZero (representedAffineAssociated B S hS U)
        (P.isZero_of_isStrictlyLE b i h)

/-- **Tor amplitude on an affine algebraic space agrees with Tor amplitude over its ring**: for
`M ∈ D(R)`, the object `Φ(M)` of `D(𝒪_{yoneda.obj U})` has Tor amplitude in `[a, b]` if and only
if `M` does.  This is Stacks 08E9 (1) read on the small étale site. -/
theorem hasTorAmplitude_representedAffineDerivedAssociated_iff
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) (a b : ℤ) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
        (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
        ((representedAffineDerivedAssociated B S hS U).obj M) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) M a b :=
  ⟨fun h => hasTorAmplitudeCanonical_of_representedAffine_tests B S hS U M a b
      fun _ i hi => h _ i hi,
    hasTorAmplitude_representedAffineDerivedAssociated_of_hasTorAmplitudeCanonical B S hS U M a b⟩

/-- **The affine case of Stacks 08IL, (2) implies (1).**  On an algebraic space represented by
an affine scheme, an object `E` of `D_QCoh(𝒪)` whose derived tensor products with the
quasi-coherent `𝒪`-modules have no cohomology outside `[a, b]` has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_representedAffine
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E) (a b : ℤ)
    (h : HasTorAmplitudeOnQuasicoherent B S hS (isAlgebraicSpace_yoneda B S hS U)
      (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      E a b) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (smallEtaleDerivedTensorProduct B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      E a b := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := representedAffineDerivedAssociatedQcoh B S hS U)
    (⟨E, hE⟩ : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
  have e' : (representedAffineDerivedAssociated B S hS U).obj M ≅ E :=
    (ObjectProperty.ι _).mapIso e
  have hM := hasTorAmplitudeCanonical_of_representedAffine_tests B S hS U M a b fun N i hi =>
    isZero_obj_obj_of_iso _ _ e' _
      (h _ (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U N) i hi)
  intro F i hi
  exact isZero_obj_obj_of_iso _ _ e'.symm _
    (hasTorAmplitude_representedAffineDerivedAssociated_of_hasTorAmplitudeCanonical B S hS U
      M a b hM F i hi)

end AlgebraicGeometry.Space

end
