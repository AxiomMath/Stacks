module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ProperDirectImageFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.DimOneGlobalSectionsAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModuleStalksDetectZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatRepresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# Proper direct images of extensions by zero along curve fibrations lie in `D_ctf`

Let `h : X ⟶ Y` be proper, `Y` quasi-compact and quasi-separated, `j_U : U ⟶ X` a quasi-compact
open immersion with `U` quasi-compact and quasi-separated, such that the fibres of `j_U ≫ h` have
dimension at most one, `Λ` a finite ring (possibly noncommutative), `K₀ ∈ D_ctf(U, Λ)` bounded
below and `J` a resolution of `j_{U!} K₀` by injectives. If the cohomology sheaves of `h_* J` are
constructible, then `h_* J ∈ D_ctf(Y, Λ)`.

The stalk of `h_* J` at a geometric point is `RΓ(Z, D)` for a proper scheme `Z` of dimension at
most one over an algebraically closed field and `D ∈ D_ctf(Z, Λ)` concentrated in the degrees
`[a, b]` of a bounded representative of `K₀`
(`Stacks.EtaleCohomology.exists_derivedEtaleModuleStalk_directImage_iso`). Such a complex is
perfect (`Stacks.EtaleCohomology.isPerfect_etaleModuleDerivedGlobalSections_of_isCtf_of_dimLEOne`)
and lies in degrees `[a, b + 2]` (Tag 0A53), so `h_* J` has perfect stalks and cohomology in
degrees `[a, b + 2]`, and lies in `D_ctf(Y, Λ)` by Tag 03TT, (1) ⟹ (2), for a noncommutative
Noetherian ring (`Stacks.EtaleCohomology.isCtf_of_isPerfect_derivedEtaleModuleStalk`).
Constructibility of the cohomology sheaves is Tag 0GL0.

## Main results

* `Stacks.EtaleCohomology.isCtf_directImage_extensionByZero_of_isConstructible`

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (1), the proof.
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModules_ab5OfSize

/-- Sheafification of presheaves of modules on the small étale site of Tag 021B at the coefficient
universe `u + 1`, for a ring in `Type`. -/
theorem smallEtale_hasSheafify_moduleCat_of_type (B : BigEtaleSite.{u}) (T : B.Scheme) (A : Type)
    [Ring A] : HasSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.{u + 1} A) :=
  SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B T A

attribute [local instance high] smallEtale_hasSheafify_moduleCat_of_type

variable (Λ : Type) [Ring Λ]

/-- **`h_*` of resolutions of extensions by zero of isomorphic complexes are isomorphic**: for `h`
proper, `j_U` an open immersion, `Q K₀ ≅ Q K₁` and resolutions `J₀`, `J₁` of `j_{U!} K₀`,
`j_{U!} K₁` by injectives, `h_* J₀ ≅ h_* J₁`; both compute `Rf_!` for `f = j_U ≫ h`. -/
theorem nonempty_directImage_iso_of_extensionByZero_iso {X Y U : Scheme.{u}} (h : X ⟶ Y)
    [IsProper h] (jU : U ⟶ X) [IsOpenImmersion jU]
    (K₀ K₁ : CochainComplex.Plus (EtaleModules.{u, 0} Λ U))
    (e : DerivedCategory.Q.obj K₀.obj ≅ DerivedCategory.Q.obj K₁.obj)
    (J₀ : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (ψ₀ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K₀ ⟶ J₀)
    [QuasiIso ψ₀.hom] (hJ₀ : ∀ n, Injective (J₀.obj.X n))
    (J₁ : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (ψ₁ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K₁ ⟶ J₁)
    [QuasiIso ψ₁.hom] (hJ₁ : ∀ n, Injective (J₁.obj.X n)) :
    Nonempty (DerivedCategory.Q.obj ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj
        J₀).obj ≅
      DerivedCategory.Q.obj
        ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj J₁).obj) := by
  let jX := compactificationOfOpenImmersionProper jU h
  let ψ₀' : (etaleModuleExtensionByZero.{u, 0} Λ jX.immersion).mapCochainComplexPlus.obj K₀ ⟶ J₀ :=
    ψ₀
  have : QuasiIso ψ₀'.hom := ‹QuasiIso ψ₀.hom›
  let ψ₁' : (etaleModuleExtensionByZero.{u, 0} Λ jX.immersion).mapCochainComplexPlus.obj K₁ ⟶ J₁ :=
    ψ₁
  have : QuasiIso ψ₁'.hom := ‹QuasiIso ψ₁.hom›
  obtain ⟨e₀⟩ := nonempty_derivedLowerShriekUnboundedIsoDirectImage_of_injective Λ jX K₀ J₀ ψ₀' hJ₀
  obtain ⟨e₁⟩ := nonempty_derivedLowerShriekUnboundedIsoDirectImage_of_injective Λ jX K₁ J₁ ψ₁' hJ₁
  exact ⟨e₀ ≪≫ (derivedLowerShriekUnbounded.{u, 0} (jU ≫ h) jX Λ).mapIso e ≪≫ e₁.symm⟩

/-- **The proper direct image of an extension by zero along a curve fibration lies in `D_ctf`,
given constructible cohomology sheaves**, for a bounded complex. Let `h : X ⟶ Y` be proper with
`Y` quasi-compact and quasi-separated, `j_U : U ⟶ X` a quasi-compact open immersion such that the
fibres of `j_U ≫ h` have dimension at most one, `Λ` a finite ring, `C ∈ D_ctf(U, Λ)` a complex
concentrated in degrees `[a, b]` and `I` a resolution of `j_{U!} C` by injectives. If the
cohomology sheaves of `h_* I` are constructible (Tag 0GL0), then `h_* I ∈ D_ctf(Y, Λ)`; its
cohomology lies in degrees `[a, b + 2]`. -/
theorem isCtf_directImage_extensionByZero_of_isConstructible_of_bounded (B : BigEtaleSite.{u})
    [Finite Λ] (X Y U : B.Scheme) [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    (h : X.obj ⟶ Y.obj) [IsProper h] (jU : U.obj ⟶ X.obj) [IsOpenImmersion jU] [QuasiCompact jU]
    (hfib : ∀ y : Y.obj, topologicalKrullDim ((jU ≫ h).fiber y) ≤ 1)
    (C : CochainComplex (EtaleModules.{u, 0} Λ U.obj) ℤ) (a b : ℤ) [C.IsStrictlyGE a]
    [C.IsStrictlyLE b] (hC : IsCtf B U Λ (DerivedCategory.Q.obj C))
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (φ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj ⟨C, ⟨a, inferInstance⟩⟩
      ⟶ I) [QuasiIso φ.hom] (hI : ∀ n, Injective (I.obj.X n))
    (hc : ∀ i : ℤ, IsConstructibleModuleSheaf B Y Λ ((etaleModulesToSmallEtale B Y Λ).obj
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ Y.obj) i).obj
        (DerivedCategory.Q.obj ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj
          I).obj)))) :
    IsCtf B Y Λ (DerivedCategory.Q.obj
      ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj I).obj) := by
  classical
  let K :=
    DerivedCategory.Q.obj ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj I).obj
  -- the stalks of `h_* I`
  have hstalk := fun y : Y.obj =>
    exists_derivedEtaleModuleStalk_directImage_iso Λ B X Y U h jU hfib C a b hC I φ hI y
  -- vanishing of a cohomology sheaf from the vanishing of its stalks
  have hzero : ∀ i : ℤ, (∀ y : Y.obj, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} Λ) i).obj ((derivedEtaleModuleStalk.{u, 0} B Y Λ
        (GeometricPoint.ofPoint Y.obj y)).obj K))) →
      IsZero ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ Y.obj) i).obj K) :=
    fun i hy => isZero_of_forall_isZero_etaleModuleStalk_ofPoint Λ _ fun y =>
      (hy y).of_iso (((etaleModuleStalk.{u, 0} B Y Λ
        (GeometricPoint.ofPoint Y.obj y)).mapDerivedCategoryHomologyIso i).app K).symm
  have (Z : B.Scheme) : EnoughInjectives (EtaleModules.{u, 0} Λ Z.obj) :=
    etaleModules_enoughInjectives.{u, 0} Λ Z.obj
  have (y : Y.obj) : IsAlgClosed (GeometricPoint.ofPoint Y.obj y).residueField :=
    inferInstanceAs (IsAlgClosed (AlgebraicClosure (Y.obj.residueField y)))
  refine isCtf_of_isPerfect_derivedEtaleModuleStalk B Y Λ K hc a (b + 2) ?_ ?_ ?_
  · intro i hi
    refine hzero i fun y => ?_
    obtain ⟨Z, fZ, _, -, D, hDa, hDb, -, ⟨e⟩⟩ := hstalk y
    have := StacksDraft.Perfect.isGE_rightDerivedFunctorPlus_of_isStrictlyGE
      (etaleModuleGlobalSections.{u, 0} Λ Z.obj) D a
    exact (DerivedCategory.isZero_of_isGE _ a i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e)
  · intro i hi
    refine hzero i fun y => ?_
    obtain ⟨Z, fZ, _, hdim, D, hDa, hDb, -, ⟨e⟩⟩ := hstalk y
    have := Stacks.SheafTwist.isLE_etaleModuleDerivedGlobalSections_of_dimLEOne fZ hdim D a b
    exact (DerivedCategory.isZero_of_isLE _ (b + 2) i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e)
  · intro y
    obtain ⟨Z, fZ, _, hdim, D, hDa, hDb, hD, ⟨e⟩⟩ := hstalk y
    exact StacksDraft.Perfect.isPerfect_of_iso e
      (isPerfect_etaleModuleDerivedGlobalSections_of_isCtf_of_dimLEOne B Z Λ fZ hdim
        (DerivedCategory.Plus.Q.obj ⟨D, ⟨a, inferInstance⟩⟩) hD)

/-- **The proper direct image of an extension by zero along a curve fibration lies in `D_ctf`,
given constructible cohomology sheaves.** Let `h : X ⟶ Y` be proper with `Y` quasi-compact and
quasi-separated, `j_U : U ⟶ X` a quasi-compact open immersion with `U` quasi-compact and
quasi-separated such that the fibres of `j_U ≫ h` have dimension at most one, `Λ` a finite ring,
`K₀ ∈ D_ctf(U, Λ)` bounded below and `J` a resolution of `j_{U!} K₀` by injectives. If the
cohomology sheaves of `h_* J` are constructible (Tag 0GL0), then `h_* J ∈ D_ctf(Y, Λ)`. -/
theorem isCtf_directImage_extensionByZero_of_isConstructible (B : BigEtaleSite.{u}) [Finite Λ]
    (X Y U : B.Scheme) [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] [CompactSpace U.obj]
    [QuasiSeparatedSpace U.obj] (h : X.obj ⟶ Y.obj) [IsProper h] (jU : U.obj ⟶ X.obj)
    [IsOpenImmersion jU] [QuasiCompact jU]
    (hfib : ∀ y : Y.obj, topologicalKrullDim ((jU ≫ h).fiber y) ≤ 1)
    (K₀ : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj))
    (hK₀ : IsCtf B U Λ (DerivedCategory.Q.obj K₀.obj))
    (J : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K₀ ⟶ J)
    [QuasiIso ψ.hom] (hJ : ∀ n, Injective (J.obj.X n))
    (hc : ∀ i : ℤ, IsConstructibleModuleSheaf B Y Λ ((etaleModulesToSmallEtale B Y Λ).obj
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ Y.obj) i).obj
        (DerivedCategory.Q.obj ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj
          J).obj)))) :
    IsCtf B Y Λ (DerivedCategory.Q.obj
      ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj J).obj) := by
  -- a bounded representative `C` of `K₀`, in degrees `[a, b]`
  obtain ⟨C, a, b, _, _, -, ⟨e₀⟩⟩ := (isCtf_iff_of_qcqs B Λ _).1 hK₀
  -- a resolution `I` of `j_{U!} C` by injectives
  have : EnoughInjectives (EtaleModules.{u, 0} Λ X.obj) :=
    etaleModules_enoughInjectives.{u, 0} Λ X.obj
  let Cb : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj) := ⟨C, ⟨a, inferInstance⟩⟩
  let L := (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj Cb
  obtain ⟨c, _⟩ := L.property
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE c L.obj
  let I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj) := ⟨R.cocomplex, R.boundedBelow⟩
  let φ : L ⟶ I := ObjectProperty.homMk R.ι
  have : QuasiIso φ.hom := inferInstanceAs (QuasiIso R.ι)
  have hI : ∀ n, Injective (I.obj.X n) := fun n => inferInstanceAs (Injective (R.cocomplex.X n))
  obtain ⟨eJI⟩ :=
    nonempty_directImage_iso_of_extensionByZero_iso Λ h jU K₀ Cb e₀.symm J ψ hJ I φ hI
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, 0}
  let P₀ := isConstructibleModuleSheafProperty.{u, u + 1, 0} B Y Λ
  have : P₀.IsWeakSerreClass := isWeakSerreClass_isConstructibleModuleSheafProperty B Y Λ
  exact (isCtf_directImage_extensionByZero_of_isConstructible_of_bounded Λ B X Y U h jU hfib C a b
    (hK₀.of_iso B U Λ e₀.symm) I φ hI (fun i => P₀.prop_of_iso
      ((etaleModulesToSmallEtale B Y Λ).mapIso ((DerivedCategory.homologyFunctor _ i).mapIso eJI))
      (hc i))).of_iso B Y Λ eJI.symm

end Stacks.EtaleCohomology

end
