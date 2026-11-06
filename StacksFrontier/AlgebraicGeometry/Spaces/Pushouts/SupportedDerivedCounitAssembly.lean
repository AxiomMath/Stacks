module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkCounit
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle

/-!
# Stacks 0AEU from the stalk formula for derived pullbacks

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and `Z ⊆ X` a finitely
presented closed subspace such that `f⁻¹Z ⟶ Z` is an isomorphism and `f` is flat at every point
of `f⁻¹Z`. Stacks 0AEU asserts that the counit `Lf^*Rf_*Q ⟶ Q` is an isomorphism for every
`Q ∈ D_QCoh(𝒪_Y)` supported on `|f⁻¹Z|` (`AlgebraicGeometry.Space.SupportedDerivedCounitIsIso`).
This file proves it from one further input,
`AlgebraicGeometry.Space.DerivedPullbackStalkComparisonStatement`, the computation of the stalks
of `Lg^*` by derived base change along the stalk map, which follows from the stalk formula for
derived pullbacks.

## Main results

* `AlgebraicGeometry.Space.supportedDerivedCounitIsIso_of_derivedPullbackStalkComparison`:
  `DerivedPullbackStalkComparisonStatement B S hS → SupportedDerivedCounitIsIso B S hS`.
* `AlgebraicGeometry.Space.exists_isKInjective_iso_of_cohomologySupportedOn`: a complex
  supported on a closed subspace `W` has a K-injective representative with terms supported on
  `W`, namely `Γ_W I` for a K-injective resolution `I` with injective terms.
* `AlgebraicGeometry.Space.isIso_derivedAdjunction_counit_app_of_forall_geometricPoint`: the
  derived counit at a K-injective complex `J` is invertible when, at every geometric point, the
  stalk of `Lf^*(f_*J) ⟶ f^*(f_*J)` is invertible, `θ` is invertible degreewise and the action
  map `𝒪_{Y,ȳ} ⊗ J_ȳ ⟶ J_ȳ` is a quasi-isomorphism.
* `AlgebraicGeometry.Space.isIso_geometricDerivedStalk_map_comparison_of_supported`,
  `AlgebraicGeometry.Space.isIso_directImageFiberMap_of_supportOfSheaf_preimage` and
  `AlgebraicGeometry.Space.quasiIso_extendRestrictScalarsAdj_counit_sheafModuleFiber_of_supported`:
  the three stalkwise inputs, for `J` with terms supported on `|f⁻¹Z|`.

## Implementation notes

The statement of Stacks 0AEU is at the standard model `HasDerivedCategory.standard` of the
derived categories, at which `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` and the
derived adjunction are formed; the model is introduced locally where a statement needs it.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
* [Stacks Project, Tag 0AET](https://stacks.math.columbia.edu/tag/0AET)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Generic inputs -/

namespace IPowerTorsion

/-- **Power torsion for an ideal passes to every smaller ideal.** -/
theorem isIPowerTorsion_of_le {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {I I' : Ideal R} (h : IsIPowerTorsion R M I) (hle : I' ≤ I) :
    IsIPowerTorsion R M I' :=
  fun m ↦ (h m).imp fun n hn ↦ ⟨hn.1, fun a ha ↦ hn.2 a (Ideal.pow_right_mono hle n ha)⟩

end IPowerTorsion

namespace CochainComplex.DerivedExtensionScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The comparison of a total derived extension of scalars with degreewise extension of scalars
is invertible at a complex all of whose terms vanish. -/
theorem TotalDerivedExtensionScalars.isIso_comparison_app_of_isZero {f : R →+* S}
    {_ : HasDerivedCategory (ModuleCat.{u} R)} {_ : HasDerivedCategory (ModuleCat.{u} S)}
    (D : TotalDerivedExtensionScalars.{u, u, u} f) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ n, IsZero (P.X n)) : IsIso (D.comparison.app P) := by
  have : P.IsStrictlyLE 0 := ⟨fun i _ ↦ hP i⟩
  have : ∀ i, Projective (P.X i) := fun i ↦ Projective.of_iso (hP i).isoZero.symm inferInstance
  exact D.comparison_isIso_of_projective P 0

/-- The degreewise action map `S ⊗_R K ⟶ K` is a quasi-isomorphism at a complex of `S`-modules
all of whose terms vanish. -/
theorem quasiIso_extendRestrictScalarsAdj_counit_of_isZero (f : R →+* S)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (hK : ∀ n, IsZero (K.X n)) :
    QuasiIso ((NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      f).counit (ComplexShape.up ℤ)).app K) := by
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).counit (ComplexShape.up ℤ)).app K).f n) :=
    fun n ↦
    isIso_of_source_target_iso_zero _
      (((ModuleCat.restrictScalars f ⋙ ModuleCat.extendScalars f).map_isZero (hK n)).isoZero)
      (hK n).isoZero
  have := HomologicalComplex.Hom.isIso_of_components
    ((NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      f).counit (ComplexShape.up ℤ)).app K)
  infer_instance

end CochainComplex.DerivedExtensionScalars

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] additive_smallEtalePullbackModules additive_smallEtalePushforwardModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The degree-zero comparison on modules supported on `|f⁻¹Z|` -/

section Support

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (Z : Subfunctor X.1)
  (hZ : IsClosedSubspace B S hS Z) (hfZ : IsIso (Z.fromPreimage f.hom))

include hZ hfZ in
/-- **`θ : (f_*M)_x̄ ⟶ M_ȳ` is invertible at a module supported on `|f⁻¹Z|`** when
`f⁻¹Z ⟶ Z` is an isomorphism: the degree-zero case of Stacks 0AEQ. -/
theorem isIso_directImageFiberMap_of_supportOfSheaf_preimage (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj M) ⊆
      Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)) :
    IsIso ((directImageFiberMap B S hS f y).app M) := by
  have hP := isClosedSubspace_preimage B S hS f.hom Z X.2 Y.2 hZ
  have sq : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage f.hom) :
        (⟨(Z.preimage f.hom).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z.toFunctor, hZ.1⟩)
      (ObjectProperty.homMk (Z.preimage f.hom).ι :
        (⟨(Z.preimage f.hom).toFunctor, hP.1⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (ObjectProperty.homMk Z.ι : (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ X) f :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage f.hom Z)
  exact isIso_directImageFiberMap_of_supportOfSheaf B S hS f _ hZ.2 _ hP.2 _
    (isIntegralHom_of_isIso B S hS (Z.fromPreimage f.hom))
    (universallyInjective_of_isIso B S hS (Z.fromPreimage f.hom)) sq y M hM

/-- **Off the support of `M` the fibre of `f_*M` vanishes**, as soon as `θ` is invertible
at `M`. -/
theorem isZero_sheafModuleFiber_pushforwardModules (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hθ : IsIso ((directImageFiberMap B S hS f y).app M))
    (hy : y.image ∉ supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj M)) :
    IsZero ((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
        (smallEtaleRingedTopos B S hS X).O).obj
      ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj M)) := by
  have h₀ := (ModuleCat.restrictScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map_isZero
    (isZero_sheafModuleFiberOfCommRing_obj_of_not_mem B S hS Y y M hy)
  have h₁ := h₀.of_iso (asIso ((directImageFiberMap B S hS f y).app M))
  exact h₁.of_iso ((Stacks.sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
    (smallEtaleRingedTopos B S hS X).O).mapIso
      ((pushforwardModulesIsoModulePushforward B S hS f).app M))

end Support

/-! ### Stacks 0AET on the stalk complex of a representative -/

/-- **Stacks 0AET on the stalk complex of a complex representing `Q`.** Let `Q ∈ D_QCoh(𝒪_Y)` be
supported on a finitely presented closed subspace `Z'`, and let `J` be a complex of
`𝒪_Y`-modules with `Hⁿ(Q) ≅ Hⁿ(J)` for every `n`. At every geometric point `ȳ` the cohomology
modules of the stalk complex `J_ȳ` are power torsion for the stalk of the ideal of `Z'`. -/
theorem isIPowerTorsion_homology_sheafModuleFiber_of_iso (Y : AlgebraicSpaces B S hS)
    (Z' : ClosedSubspaces B S hS Y.1) (hZ' : IsFinitePresentation B S hS Z'.1.ι)
    (Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hQ : CohomologySupportedOn B S hS Y.1 Y.2
      (Set.range (pointsMap B S hS Z'.1.toFunctor Z'.1.ι)) Q.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (e : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
      ∀ n, (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj Q.1 ≅
        J.homology n)
    (y : GeometricPoint B S hS Y.1) (n : ℤ) :
    IsIPowerTorsion _
      ((((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          J).homology n)
      (pointStalkIdeal B S hS Y y (closedSubspaceStalkIdeal B S hS Y Z' y)) :=
  Stacks.LocalCohomology.isIPowerTorsion_of_iso
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapIso (e n) ≪≫
      ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O) (ComplexShape.up ℤ) n).app J).symm)
    (isIPowerTorsion_moduleStalk_of_geometricModuleStalk B S hS Y y _ _
      (isIPowerTorsion_geometricModuleStalk_homology_of_cohomologySupportedOn B S hS Y Z' hZ' Q
        hQ y n))

/-! ### A K-injective representative supported on the closed subspace -/

/-- An isomorphism `A ≅ Q J` in the derived category gives isomorphisms on all homology. -/
private def homologyIsoOfIsoQ {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {A : DerivedCategory C} {J : CochainComplex C ℤ} (e : A ≅ DerivedCategory.Q.obj J) (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).obj A ≅ J.homology n :=
  (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).app J

/-- **A K-injective representative with terms supported on `W`.** Let `Q ∈ D_QCoh(𝒪_Y)` have its
cohomology sheaves supported on a closed subspace `W`. Then `Q` is represented by a K-injective
complex `J` every term of which is supported on `W`. -/
theorem exists_isKInjective_iso_of_cohomologySupportedOn (Y : AlgebraicSpaces B S hS)
    (W : ClosedSubspaces B S hS Y.1) (Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hQ : CohomologySupportedOn B S hS Y.1 Y.2 (subspacePointSet B S hS Y.1 W.1) Q.1) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
    ∃ J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ, J.IsKInjective ∧
      (∀ n, supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj (J.X n)) ⊆
        subspacePointSet B S hS Y.1 W.1) ∧ Nonempty (Q.1 ≅ DerivedCategory.Q.obj J) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  obtain ⟨I, g, hI, hg, hinj⟩ := exists_quasiIso_isKInjective_injective_modules B S hS Y.1 Y.2
    (DerivedCategory.Q.objPreimage Q.1)
  let V := openComplementOfClosedSubspace B S hS Y W
  have hVW : Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) =
      (subspacePointSet B S hS Y.1 W.1)ᶜ :=
    subspacePointSet_openComplement B S hS Y W
  let eI : Q.1 ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso Q.1).symm ≪≫ asIso (DerivedCategory.Q.map g)
  have hacyc := acyclic_openSubspaceRestriction_of_isZero B S hS V.1 V.2 I fun n ↦ by
    refine isZero_openSubspaceRestriction_of_disjoint B S hS V.1 V.2 _ ?_
    rw [hVW]
    exact Set.disjoint_compl_right_iff_subset.mpr
      ((@supportOfSheaf_toSheaf_subset_of_epi B S hS Y _ _ (homologyIsoOfIsoQ eI n).hom
        (IsIso.epi_of_iso _)).trans (hQ n))
  have hι := quasiIso_sectionsOffOpen_ι B S hS V.1 V.2 I hacyc
  refine ⟨_, isKInjective_sectionsOffOpen B S hS V.1 V.2 I, fun n ↦ ?_,
    ⟨eI ≪≫ (asIso (DerivedCategory.Q.map
      (Stacks.Injectives.SectionsKilledByRestriction.sectionsShortComplex
        (openSubspacePushforwardAdjunction B S hS V.1 V.2) I).f)).symm⟩⟩
  have h := disjoint_supportOfSheaf_sectionsOffOpen B S hS V.1 V.2 (I.X n)
  rw [hVW] at h
  exact Set.disjoint_compl_right_iff_subset.mp h

section Point

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- The counit of the adjunction induced on homotopy categories is the degreewise counit. -/
theorem pullbackAdjPushforwardMapHomotopy_counit_app_quotient
    (J : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    (Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy
        (smallEtaleRingedToposHom B S hS f)).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit (ComplexShape.up ℤ)).app J) :=
  rfl

/-- **The stalk at `ȳ` of the degreewise counit `f^*f_*J ⟶ J` is invertible in the derived
category** when `θ` is invertible in every degree of `J` and the action map
`𝒪_{Y,ȳ} ⊗ J_ȳ ⟶ J_ȳ` is a quasi-isomorphism. -/
theorem isIso_geometricDerivedStalk_map_Qh_map_ringedToposCounit (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hθ : ∀ n : ℤ, IsIso ((directImageFiberMap B S hS f y).app (J.X n)))
    (hc : QuasiIso ((NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj.{u}
        (smallEtaleStalkPullbackRingMap B S hS f y)).counit (ComplexShape.up ℤ)).app
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    IsIso ((geometricDerivedStalk B S hS y).map (DerivedCategory.Qh.map
      ((Stacks.Cohomology.DerivedPushforward.pullbackAdjPushforwardMapHomotopy
        (smallEtaleRingedToposHom B S hS f)).counit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)))) := by
  rw [pullbackAdjPushforwardMapHomotopy_counit_app_quotient]
  exact ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
    (smallEtaleRingedTopos B S hS Y).O).isIso_mapDerivedCategory_map_Qh_map_quotient_map_iff
      _).2
    (quasiIso_sheafModuleFiber_ringedToposCounit B S hS f y J hθ hc)

attribute [local instance] isGrothendieckAbelian_ringedToposModules in
open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- **The derived counit at a K-injective complex, checked on stalks.** Let `J` be a K-injective
complex of `𝒪_Y`-modules. Suppose that at every geometric point `ȳ` of `Y` the stalk of the
comparison `Lf^*(f_*J) ⟶ f^*(f_*J)` of Stacks 06YY is invertible, the comparison
`θ : (f_*Jⁿ)_x̄ ⟶ Jⁿ_ȳ` is invertible in every degree, and the degreewise action map
`𝒪_{Y,ȳ} ⊗ J_ȳ ⟶ J_ȳ` is a quasi-isomorphism. Then the counit `Lf^*Rf_*J ⟶ J` of the derived
adjunction is an isomorphism. -/
theorem isIso_derivedAdjunction_counit_app_of_forall_geometricPoint
    (J : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    [J.IsKInjective]
    (ha : ∀ y : GeometricPoint B S hS Y.1, IsIso ((geometricDerivedStalk B S hS y).map
      ((smallEtaleDerivedModulePullbackComparison B S hS f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((smallEtaleRingedToposHom B S hS f).pushforwardModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)))))
    (hθ : ∀ (y : GeometricPoint B S hS Y.1) (n : ℤ),
      IsIso ((directImageFiberMap B S hS f y).app (J.X n)))
    (hc : ∀ y : GeometricPoint B S hS Y.1,
      QuasiIso ((NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj.{u}
        (smallEtaleStalkPullbackRingMap B S hS f y)).counit (ComplexShape.up ℤ)).app
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    IsIso ((derivedAdjunction (smallEtaleRingedToposHom B S hS f)).counit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J))) := by
  rw [isIso_derivedAdjunction_counit_app_iff_of_isKInjective
    (smallEtaleRingedToposHom B S hS f) J, isIso_iff_forall_isIso_geometricDerivedStalk_map]
  intro y
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' (ha y)
    (isIso_geometricDerivedStalk_map_Qh_map_ringedToposCounit B S hS f y J (hθ y) (hc y))

end Point

/-! ### The three stalkwise inputs at a point -/

section Inputs

open CochainComplex.DerivedExtensionScalars

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (Z : Subfunctor X.1)
  (hZ : IsClosedSubspace B S hS Z) (hfZ : IsIso (Z.fromPreimage f.hom))
  (hflat : ∀ p : points B S hS (Z.preimage f.hom).toFunctor,
    IsFlatAt B S hS f.hom (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι p))

include hZ hfZ in
/-- Off `f⁻¹Z`, the stalk complex `(f_*J)_x̄` of a complex with terms supported on `|f⁻¹Z|`
vanishes termwise. -/
theorem isZero_sheafModuleFiber_pushforwardModules_X_of_supported
    (J : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hsupp : ∀ n, supportOfSheaf B S hS Y.1
      ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj (J.X n)) ⊆
        Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι))
    (y : GeometricPoint B S hS Y.1)
    (hy : y.image ∉ Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι))
    (n : ℤ) :
    IsZero ((((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((smallEtaleRingedToposHom B S hS f).pushforwardModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)).X n) :=
  isZero_sheafModuleFiber_pushforwardModules B S hS f y (J.X n)
    (isIso_directImageFiberMap_of_supportOfSheaf_preimage B S hS f Z hZ hfZ y (J.X n) (hsupp n))
    fun h ↦ hy (hsupp n h)

include hZ hfZ hflat in
/-- **The stalk of `Lf^*(f_*J) ⟶ f^*(f_*J)` at `ȳ` is invertible**, for a complex `J` with terms
supported on `|f⁻¹Z|`, granted the stalk formula for derived pullbacks. -/
theorem isIso_geometricDerivedStalk_map_comparison_of_supported
    (H : DerivedPullbackStalkComparisonStatement B S hS)
    (J : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hsupp : ∀ n, supportOfSheaf B S hS Y.1
      ((SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)).obj (J.X n)) ⊆
        Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι))
    (y : GeometricPoint B S hS Y.1) :
    IsIso ((geometricDerivedStalk B S hS y).map
      ((smallEtaleDerivedModulePullbackComparison B S hS f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((smallEtaleRingedToposHom B S hS f).pushforwardModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)))) := by
  refine H f y _ ?_
  by_cases hy : y.image ∈
    Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)
  · obtain ⟨p, hp⟩ := hy
    exact TotalDerivedExtensionScalars.isIso_comparison_app_of_flat _
      (flat_stalkStructureMap_of_isFlatAt f y (hp ▸ hflat p)) _
  · exact TotalDerivedExtensionScalars.isIso_comparison_app_of_isZero _ _
        (isZero_sheafModuleFiber_pushforwardModules_X_of_supported B S hS f Z hZ hfZ J hsupp y hy)

include hZ hfZ hflat in
/-- **The action map `𝒪_{Y,ȳ} ⊗ J_ȳ ⟶ J_ȳ` is a quasi-isomorphism** for a complex `J` with terms
supported on `|f⁻¹Z|` representing `Q`. -/
theorem quasiIso_extendRestrictScalarsAdj_counit_sheafModuleFiber_of_supported
    (hZfp : IsFinitePresentation B S hS Z.ι)
    (Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hQ : CohomologySupportedOn B S hS Y.1 Y.2
      (Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)) Q.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (e : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
      ∀ n, (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj Q.1 ≅
        J.homology n)
    (hsupp : ∀ n, supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj (J.X n)) ⊆
      Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι))
    (y : GeometricPoint B S hS Y.1) :
    QuasiIso ((NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj.{u}
        (smallEtaleStalkPullbackRingMap B S hS f y)).counit (ComplexShape.up ℤ)).app
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) := by
  by_cases hy : y.image ∈
    Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)
  · obtain ⟨p, hp⟩ := hy
    exact quasiIso_extendRestrictScalarsAdj_counit_of_isIPowerTorsion
      _ (flat_smallEtaleStalkPullbackRingMap_of_isFlatAt f y (hp ▸ hflat p)) _
      (bijective_quotientMap_smallEtaleStalkPullbackRingMap f Z hZ hfZ hflat y ⟨p, hp⟩) _
      fun n ↦ IPowerTorsion.isIPowerTorsion_of_le
        (isIPowerTorsion_homology_sheafModuleFiber_of_iso B S hS Y
          (preimageSubspace B S hS f ⟨Z, hZ⟩) (isFinitePresentation_ι_preimage f ⟨Z, hZ⟩ hZfp)
          Q hQ J e y n)
        (map_comap_closedSubspaceStalkIdeal_le f ⟨Z, hZ⟩ y)
  · exact quasiIso_extendRestrictScalarsAdj_counit_of_isZero _ _ fun n ↦
        isZero_sheafModuleFiberOfCommRing_obj_of_not_mem B S hS Y y (J.X n)
        fun h ↦ hy (hsupp n h)

attribute [local instance] isGrothendieckAbelian_ringedToposModules in
include hZ hfZ hflat in
/-- **The counit `Lf^*Rf_*Q ⟶ Q` at a complex with a K-injective representative supported on
`|f⁻¹Z|`** is an isomorphism, granted the stalk formula for derived pullbacks. -/
theorem isIso_derivedAdjunction_counit_app_of_supported_representative
    (H : DerivedPullbackStalkComparisonStatement B S hS) (hZfp : IsFinitePresentation B S hS Z.ι)
    (Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hQ : CohomologySupportedOn B S hS Y.1 Y.2
      (Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)) Q.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (hJ : J.IsKInjective)
    (hsupp : ∀ n, supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj (J.X n)) ⊆
      Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι))
    (e : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
      Q.1 ≅ DerivedCategory.Q.obj J) :
    IsIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
      (smallEtaleRingedToposHom B S hS f)).counit.app Q.1) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  have e' : Q.1 ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) :=
    e ≪≫ ((DerivedCategory.quotientCompQhIso _).app J).symm
  have : CochainComplex.IsKInjective
      (show CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ
        from J) :=
    hJ
  refine (NatTrans.isIso_app_iff_of_iso
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
      (smallEtaleRingedToposHom B S hS f)).counit e').2 ?_
  exact isIso_derivedAdjunction_counit_app_of_forall_geometricPoint B S hS f J
    (isIso_geometricDerivedStalk_map_comparison_of_supported B S hS f Z hZ hfZ hflat H J hsupp)
    (fun y n ↦ isIso_directImageFiberMap_of_supportOfSheaf_preimage B S hS f Z hZ hfZ y (J.X n)
      (hsupp n))
    (quasiIso_extendRestrictScalarsAdj_counit_sheafModuleFiber_of_supported B S hS f Z hZ hfZ hflat
      hZfp Q hQ J (homologyIsoOfIsoQ e) hsupp)

end Inputs

/-- **Stacks 0AEU, granted the stalk formula for derived pullbacks.** Let `f : Y ⟶ X` be a
morphism of algebraic spaces over `S` and `Z ⊆ X` a finitely presented closed subspace such that
`f⁻¹Z ⟶ Z` is an isomorphism and `f` is flat at every point of `f⁻¹Z`. Then the counit
`Lf^*Rf_*Q ⟶ Q` is an isomorphism for every `Q ∈ D_QCoh(𝒪_Y)` supported on `|f⁻¹Z|`.

The hypothesis `AlgebraicGeometry.Space.DerivedPullbackStalkComparisonStatement` asserts that the
stalk of `Lg^*P ⟶ g^*P` is invertible where derived base change along the stalk map is computed
termwise at the stalk complex of `P`. -/
theorem supportedDerivedCounitIsIso_of_derivedPullbackStalkComparison
    (H : DerivedPullbackStalkComparisonStatement B S hS) : SupportedDerivedCounitIsIso B S hS := by
  intro Y X f Z hZ hZfp hfZ hflat Q hQ
  obtain ⟨J, hJ, hsupp, ⟨e⟩⟩ := exists_isKInjective_iso_of_cohomologySupportedOn B S hS Y
    (preimageSubspace B S hS f ⟨Z, hZ⟩) Q hQ
  exact isIso_derivedAdjunction_counit_app_of_supported_representative B S hS f Z hZ hfZ hflat H
    hZfp Q hQ J hJ hsupp e

end AlgebraicGeometry.Space

end
