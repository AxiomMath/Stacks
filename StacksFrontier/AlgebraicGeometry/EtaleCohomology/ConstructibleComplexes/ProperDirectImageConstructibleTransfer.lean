module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ProperDirectImageCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.RestrictScalarsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.RestrictScalarsReflectConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived

/-!
# Constructibility of proper direct images through restriction of scalars

Let `ρ : R →+* Λ` be a homomorphism from a commutative Noetherian finite ring `R` to a finite ring
`Λ`, not necessarily commutative. Constructibility of sheaves of `Λ`-modules is detected after
restricting scalars to `R`, so the constructibility of the cohomology sheaves of `Rh_*(j_{U!} C)`,
for a complex `C` of sheaves of `Λ`-modules, follows from that of `Rf_!(res_ρ C)` for
`f = j_U ≫ h`, a statement about the commutative ring `R` such as Tag 0GL0 for `R = ℤ/n`.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `etaleModulesToSmallEtaleRestrictScalarsIso`: the transport to the small étale site of Tag 021B
  commutes with restriction of scalars.
* `isConstructibleModuleSheaf_of_isConstructibleEtaleModule_restrictScalars`: on a quasi-compact
  and quasi-separated scheme, for `R` Noetherian and finite and `Λ` finite, a sheaf of `Λ`-modules
  is constructible if its restriction of scalars to `R` is.
* `isConstructibleEtaleModule_restrictScalars_of_isConstructibleModuleSheaf`: for `Λ` finite,
  restriction of scalars along `ρ` preserves constructibility.
* `nonempty_restrictScalars_directImage_iso_derivedLowerShriek`: for `h` proper, `j_U` an open
  immersion and `I` a resolution of `j_{U!} C` by injectives, restricting scalars along `ρ` in
  `h_* I` computes `Rf_!(res_ρ C)` for `f = j_U ≫ h`.
* `isConstructibleModuleSheaf_homology_directImage_of_isConstructibleEtaleComplex`: for `h` proper
  with quasi-compact and quasi-separated target, if `Rf_!(res_ρ C)` has constructible cohomology
  sheaves of `R`-modules, then the cohomology sheaves of `h_* I` are constructible sheaves of
  `Λ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModules_ab5OfSize
attribute [local instance high] smallEtale_hasSheafify_moduleCat_of_type
  hasWeakSheafify_over_moduleCat_type isRightAdjoint_smallEtalePushforward_moduleCat_type

variable (B : BigEtaleSite.{u}) {R Λ : Type} [CommRing R] [Ring Λ] (ρ : R →+* Λ)

/-- **The transport to the small étale site of Tag 021B commutes with restriction of scalars**:
both send a sheaf to its restriction along the inclusion of sites, followed by restriction of
scalars sectionwise. -/
def etaleModulesToSmallEtaleRestrictScalarsIso (X : B.Scheme) :
    etaleModulesToSmallEtale B X Λ ⋙ smallEtaleRestrictScalars B X ρ ≅
      etaleModuleRestrictScalars ρ X.obj ⋙ etaleModulesToSmallEtale B X R :=
  Iso.refl _

/-- **Constructibility of a sheaf of `Λ`-modules from that of its restriction of scalars**, on a
quasi-compact quasi-separated scheme, `R` commutative Noetherian and finite, `Λ` finite. -/
theorem isConstructibleModuleSheaf_of_isConstructibleEtaleModule_restrictScalars
    [IsNoetherianRing R]
    [Finite R] [Finite Λ] (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (G : EtaleModules.{u, 0} Λ X.obj)
    (hG : IsConstructibleEtaleModule R ((etaleModuleRestrictScalars ρ X.obj).obj G)) :
    IsConstructibleModuleSheaf B X Λ ((etaleModulesToSmallEtale B X Λ).obj G) := by
  refine isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_restrictScalars B X ρ _ ?_
  exact (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf R B X.property _).1 hG

/-- **Restriction of scalars preserves constructibility**, read in the model `EtaleModules`. -/
theorem isConstructibleEtaleModule_restrictScalars_of_isConstructibleModuleSheaf [Finite Λ]
    (X : B.Scheme) (G : EtaleModules.{u, 0} Λ X.obj)
    (hG : IsConstructibleModuleSheaf B X Λ ((etaleModulesToSmallEtale B X Λ).obj G)) :
    IsConstructibleEtaleModule R ((etaleModuleRestrictScalars ρ X.obj).obj G) :=
  (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf R B X.property _).2
    (isConstructibleModuleSheaf_restrictScalars B ρ X _ hG)

/-- **A right derived functor at a bounded below complex of injectives is computed termwise**:
`RF(I) ≅ F(I)` for a bounded below complex `I` of injective objects. -/
theorem nonempty_rightDerivedFunctorPlus_obj_iso_of_injective {A B : Type*} [Category* A]
    [Abelian A] [EnoughInjectives A] [Category* B] [Abelian B] (F : A ⥤ B) [F.Additive]
    (I : CochainComplex.Plus A) (hI : ∀ n, Injective (I.obj.X n)) :
    Nonempty (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj I)) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj)) := by
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj I)) := inferInstance
  have : IsIso (F.mapHomologicalComplexDerivedUnit I.property) :=
    inferInstanceAs (IsIso ((F.mapHomologicalComplexQhIso I.property).inv ≫
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient _).obj I))))
  exact ⟨DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso
      ((DerivedCategory.Plus.quotientCompQhIso _).app I).symm) ≪≫
    (asIso (F.mapHomologicalComplexDerivedUnit I.property)).symm⟩

/-- **`res_ρ(h_* I) ≅ Rf_!(res_ρ C)`**: for `h` proper, `j_U` an open immersion, `C` a bounded
below complex of sheaves of `Λ`-modules on `U` and `I` a resolution of `j_{U!} C` by injectives,
restricting scalars along `ρ : R →+* Λ` in `h_* I` computes `Rf_!(res_ρ C)` for `f = j_U ≫ h`,
through the compactification `j_U`. -/
theorem nonempty_restrictScalars_directImage_iso_derivedLowerShriek {X Y U : Scheme.{u}}
    (h : X ⟶ Y) [IsProper h] (jU : U ⟶ X) [IsOpenImmersion jU]
    (C : CochainComplex (EtaleModules.{u, 0} Λ U) ℤ) (a : ℤ) [C.IsStrictlyGE a]
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (φ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj ⟨C, ⟨a, inferInstance⟩⟩
      ⟶ I) [QuasiIso φ.hom] (hI : ∀ n, Injective (I.obj.X n)) :
    Nonempty (DerivedCategory.Q.obj (((etaleModuleRestrictScalars ρ Y).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj
          I).obj) ≅
      (derivedLowerShriekUnbounded.{u, 0} (jU ≫ h) (compactificationOfOpenImmersionProper jU h)
        R).obj (DerivedCategory.Q.obj (((etaleModuleRestrictScalars ρ U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C))) := by
  have : EnoughInjectives (EtaleModules.{u, 0} R X) := etaleModules_enoughInjectives.{u, 0} R X
  have : EnoughInjectives (EtaleModules.{u, 0} Λ X) := etaleModules_enoughInjectives.{u, 0} Λ X
  let resU := etaleModuleRestrictScalars ρ U
  let resX := etaleModuleRestrictScalars ρ X
  let resY := etaleModuleRestrictScalars ρ Y
  let Cb : CochainComplex.Plus (EtaleModules.{u, 0} Λ U) := ⟨C, ⟨a, inferInstance⟩⟩
  let Cr := resU.mapCochainComplexPlus.obj Cb
  let L' := (etaleModuleExtensionByZero.{u, 0} R jU).mapCochainComplexPlus.obj Cr
  obtain ⟨c, _⟩ := L'.property
  obtain ⟨R', -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE c L'.obj
  let I' : CochainComplex.Plus (EtaleModules.{u, 0} R X) := ⟨R'.cocomplex, R'.boundedBelow⟩
  let φ' : L' ⟶ I' := ObjectProperty.homMk R'.ι
  have : QuasiIso φ'.hom := inferInstanceAs (QuasiIso R'.ι)
  have hI' : ∀ n, Injective (I'.obj.X n) := fun n => inferInstanceAs (Injective (R'.cocomplex.X n))
  let jX := compactificationOfOpenImmersionProper jU h
  let φ'' : (etaleModuleExtensionByZero.{u, 0} R jX.immersion).mapCochainComplexPlus.obj Cr ⟶ I' :=
    φ'
  have : QuasiIso φ''.hom := ‹QuasiIso φ'.hom›
  obtain ⟨e₁⟩ := nonempty_derivedLowerShriekUnboundedIsoDirectImage_of_injective R jX Cr I' φ'' hI'
  let hR := etaleModuleDirectImage.{u, 0} R h
  let hΛ := etaleModuleDirectImage.{u, 0} Λ h
  obtain ⟨u₁⟩ := nonempty_rightDerivedFunctorPlus_obj_iso_of_injective hR I' hI'
  obtain ⟨u₂⟩ := nonempty_rightDerivedFunctorPlus_obj_iso_of_injective hΛ I hI
  let uΛ : hΛ.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj I) ≅
      DerivedCategory.Plus.Q.obj (hΛ.mapCochainComplexPlus.obj I) :=
    DerivedCategory.Plus.ι.preimageIso u₂
  let eL : L'.obj ≅ (resX.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((etaleModuleExtensionByZero.{u, 0} Λ jU).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C) :=
    (Functor.mapHomologicalComplexCompIso
        (etaleModuleExtensionByZeroRestrictScalars ρ jU) (ComplexShape.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm.app C
  have hφQ : IsIso (DerivedCategory.Q.map ((resX.mapHomologicalComplex (ComplexShape.up ℤ)).map
      φ.hom)) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let eP : DerivedCategory.Plus.Q.obj L' ≅
      DerivedCategory.Plus.Q.obj (resX.mapCochainComplexPlus.obj I) :=
    DerivedCategory.Plus.ι.preimageIso (DerivedCategory.Q.mapIso eL ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map ((resX.mapHomologicalComplex (ComplexShape.up ℤ)).map
        φ.hom)) hφQ)
  have : IsIso (DerivedCategory.Plus.Q.map φ') := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map φ')) := by
      change IsIso (DerivedCategory.Q.map ((CochainComplex.Plus.ι _).map φ'))
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ‹QuasiIso φ'.hom›
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  let ι := DerivedCategory.Plus.ι (C := EtaleModules.{u, 0} R Y)
  exact ⟨ι.mapIso (((Functor.mapDerivedCategoryPlusQIso resY).app
      (hΛ.mapCochainComplexPlus.obj I)).symm ≪≫ resY.mapDerivedCategoryPlus.mapIso uΛ.symm ≪≫
      (etaleModuleDerivedDirectImageRestrictScalars ρ h).app (DerivedCategory.Plus.Q.obj I) ≪≫
      hR.rightDerivedFunctorPlus.mapIso ((Functor.mapDerivedCategoryPlusQIso resX).app I ≪≫
        eP.symm ≪≫ asIso (DerivedCategory.Plus.Q.map φ'))) ≪≫ u₁ ≪≫ e₁⟩

/-- **Constructibility of the cohomology sheaves of `h_* I` from that of `Rf_!(res_ρ C)`.** For
`h : X ⟶ Y` proper with `Y` quasi-compact and quasi-separated, `j_U` an open immersion, `C` a
bounded below complex of sheaves of `Λ`-modules on `U` and `I` a resolution of `j_{U!} C` by
injectives, if `Rf_!(res_ρ C)` has constructible cohomology sheaves of `R`-modules, `f = j_U ≫ h`,
then the cohomology sheaves of `h_* I` are constructible sheaves of `Λ`-modules. -/
theorem isConstructibleModuleSheaf_homology_directImage_of_isConstructibleEtaleComplex
    [IsNoetherianRing R] [Finite R] [Finite Λ] (X Y U : B.Scheme) [CompactSpace Y.obj]
    [QuasiSeparatedSpace Y.obj] (h : X.obj ⟶ Y.obj) [IsProper h] (jU : U.obj ⟶ X.obj)
    [IsOpenImmersion jU] (C : CochainComplex (EtaleModules.{u, 0} Λ U.obj) ℤ) (a : ℤ)
    [C.IsStrictlyGE a] (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (φ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj ⟨C, ⟨a, inferInstance⟩⟩
      ⟶ I) [QuasiIso φ.hom] (hI : ∀ n, Injective (I.obj.X n))
    (hR : IsConstructibleEtaleComplex R ((derivedLowerShriekUnbounded.{u, 0} (jU ≫ h)
      (compactificationOfOpenImmersionProper jU h) R).obj
        (DerivedCategory.Q.obj (((etaleModuleRestrictScalars ρ U.obj).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)))) (i : ℤ) :
    IsConstructibleModuleSheaf B Y Λ ((etaleModulesToSmallEtale B Y Λ).obj
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ Y.obj) i).obj
        (DerivedCategory.Q.obj ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj
          I).obj))) := by
  obtain ⟨e⟩ := nonempty_restrictScalars_directImage_iso_derivedLowerShriek ρ h jU C a I φ hI
  refine isConstructibleModuleSheaf_of_isConstructibleEtaleModule_restrictScalars B ρ Y _ ?_
  let resY := etaleModuleRestrictScalars ρ Y.obj
  let K := ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj I).obj
  exact (IsConstructibleEtaleModule R).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
        (resY.mapDerivedCategoryFactors.app K ≪≫ e).symm ≪≫
      (resY.mapDerivedCategoryHomologyIso i).app (DerivedCategory.Q.obj K)) (hR i)

/-- **Restriction of scalars of a bounded below complex of constructible flat sheaves is torsion
and constructible**: for a finite ring `Λ` and a homomorphism `ρ : R →+* Λ` from a finite ring,
`res_ρ C` lies in `D^+_{tors, c}(U_étale, R)` for a complex `C` of constructible flat sheaves of
`Λ`-modules concentrated in degrees `≥ a`. -/
theorem isTorsionConstructibleEtaleComplexPlus_restrictScalars [Finite R] [Finite Λ]
    (U : B.Scheme) (C : CochainComplex (EtaleModules.{u, 0} Λ U.obj) ℤ) (a : ℤ) [C.IsStrictlyGE a]
    (hC : ∀ i, IsConstructibleFlatEtaleModule B U Λ (C.X i)) :
    IsTorsionConstructibleEtaleComplexPlus R (DerivedCategory.Q.obj
      (((etaleModuleRestrictScalars ρ U.obj).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        C)) := by
  let resU := etaleModuleRestrictScalars ρ U.obj
  let C' := (resU.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  have : CochainComplex.IsStrictlyGE C' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact resU.map_isZero (C.isZero_of_isStrictlyGE a i hi)
  have : (DerivedCategory.Q.obj C').IsGE a := (DerivedCategory.isGE_Q_obj_iff _ _).2 inferInstance
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, 0}
  let P₀ := isConstructibleModuleSheafProperty.{u, u + 1, 0} B U Λ
  have : P₀.IsWeakSerreClass := isWeakSerreClass_isConstructibleModuleSheafProperty B U Λ
  let P : ObjectProperty (EtaleModules.{u, 0} Λ U.obj) :=
    P₀.inverseImage (etaleModulesToSmallEtale B U Λ)
  have : P.IsWeakSerreClass := inferInstance
  have hX : ∀ i, P (C.X i) := fun i =>
    isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B U Λ (hC i)
  have hH : ∀ i, P ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj C)) := by
    intro i
    let S := C.sc i
    have hc : P S.cycles :=
      P.prop_of_iso (S.cyclesIsKernel.conePointUniqueUpToIso (limit.isLimit _)).symm
        (P.prop_kernel _ (hX _) (hX _))
    exact P.prop_of_iso (((cokernelIsCokernel _).coconePointUniqueUpToIso S.homologyIsCokernel) ≪≫
      ((DerivedCategory.homologyFunctorFactors _ i).app C).symm) (P.prop_cokernel _ (hX _) hc)
  refine ⟨⟨a, fun n hn => DerivedCategory.isZero_of_isGE _ a n hn⟩, fun n => ⟨?_, ?_⟩⟩
  · exact isTorsionEtaleModule_of_isAddTorsion R (fun g => isOfFinAddOrder_of_finite g) _
  · exact (IsConstructibleEtaleModule R).prop_of_iso
      (((resU.mapDerivedCategoryHomologyIso n).app (DerivedCategory.Q.obj C)).symm ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso (resU.mapDerivedCategoryFactors.app C))
      (isConstructibleEtaleModule_restrictScalars_of_isConstructibleModuleSheaf B ρ U _ (hH n))

end Stacks.EtaleCohomology

end
