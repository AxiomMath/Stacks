module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDirectImageCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion

/-!
# Cohomology of `K ⊗^L ℱ` on the base as cohomology of `E ⊗^L (𝒢^• ⊗ f^*ℱ)` (Stacks 0A1M)

Let `Y` be a Noetherian algebraic space, `f : X ⟶ Y` locally of finite type and quasi-separated,
`E` a perfect object of `D(𝒪_X)` and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules, flat over
`Y`, with support proper over `Y`, and `K = Rf_*(E ⊗^L 𝒢^•)` (Stacks 0DKJ). For a quasi-coherent
`𝒪_Y`-module `ℱ` there are isomorphisms `H^i(Y, K ⊗^L ℱ) ≅ H^i(X, E ⊗^L (𝒢^• ⊗ f^*ℱ))`, natural in
`ℱ` and compatible with the boundary maps of short exact sequences of quasi-coherent modules.

The comparison is the composite of `𝒢^• ⊗^L Lf^*ℱ ≅ 𝒢^• ⊗ f^*ℱ` (the terms of `𝒢^•` being flat over
`Y`), the projection formula of Stacks 08IN on a quasi-compact open neighbourhood of the support of
`𝒢^•`, the associativity of `⊗^L`, and `H^i(-, A) = Hom(𝒪, A[i])`.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `tensorDirectImageUnitHomNatTrans`: `Hom(𝒪_Y, K ⊗^L -) ⟶ Hom(𝒪_X, E ⊗^L (𝒢^• ⊗^L Lf^*-))`, an
  isomorphism on `D_QCoh(𝒪_Y)`.
* `cohomologyTensorDirectImageNatTrans`: the comparison
  `H^i(Y, K ⊗^L ℱ) ⟶ H^i(X, E ⊗^L (𝒢^• ⊗ f^*ℱ))`, natural in the `𝒪_Y`-module `ℱ`.

## Main results

* `isIso_cohomologyTensorDirectImageNatTrans_app`: the comparison is an isomorphism for `ℱ`
  quasi-coherent.
* `cohomologyTensorDirectImageNatTrans_δ`: it is compatible with the boundary maps.
* `exists_cohomologyTensorDirectImage_iso`: Stacks 0A1M.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

section Comparison

variable (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
  (hfqs : IsQuasiSeparated B S hS f.hom) (hY : IsNoetherian B S hS hTop Y.1)
  (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (hG : FlatProperSupportComplex B S hS f hf G)

attribute [local instance] isGrothendieckAbelian_modules in
/-- The object `K = Rf_*(E ⊗^L 𝒢^•)` of Stacks 0DKJ and 0A1M. -/
abbrev tensorDirectImageObj :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
    (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))

/-- The functor `M ↦ E ⊗^L (𝒢^• ⊗^L Lf^*M)` from `D(𝒪_Y)` to `D(𝒪_X)`. -/
abbrev tensorCoefficientFunctor :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  extPerfectCoefficientFunctor B S hS f G ⋙ (smallEtaleDerivedTensor B S hS X).obj E

attribute [local instance] isGrothendieckAbelian_modules in
include hfqs hY hE hG in
/-- The projection formula on morphisms out of the structure sheaf for `A = E ⊗^L 𝒢^•`. -/
theorem exists_unitHomProjectionFormula_tensorDirectImage :
    ∃ θ : (smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G) ⋙
          preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
        smallEtaleDerivedModulePullback B S hS f ⋙
          (smallEtaleDerivedTensor B S hS X).obj
            (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)) ⋙
          preadditiveCoyoneda.obj (op (structureDerived X)),
      ∀ M, QcohDerived B S hS Y M → IsIso (θ.app M) := by
  obtain ⟨Z, hZcl, hZp, hGZ⟩ := hG.properSupport
  have hZc : IsCompact Z := isCompact_of_isProperOver B S hS X.2 Y.2 hY.1 f.hom hf Z hZcl hZp
  have hQG : QcohDerived B S hS X (DerivedCategory.Q.obj G) :=
    (qcohDerived_Q_obj_iff B S hS G).2 fun q => isQuasicoherentOnSite_homology B S hS G
      (fun n => (hG.isCoherent n).toIsQuasicoherentOnSite) q
  have hA := qcohDerived_smallEtaleDerivedTensor X _ _ (qcohDerived_of_isPerfect B S hS X E hE) hQG
  exact exists_unitHomProjectionFormula_of_cohomologySupportedOn B S hS hTop f hfqs hY.2.1 _ hA Z
    hZcl hZc (cohomologySupportedOn_derivedTensor B S hS X (smallEtaleDerivedTensorProduct B S hS X)
      _ G Z hGZ)

/-- The projection formula on morphisms out of the structure sheaf for `A = E ⊗^L 𝒢^•`, chosen. -/
def tensorDirectImageProjectionFormula :=
  (exists_unitHomProjectionFormula_tensorDirectImage B S hS hTop f hf hfqs hY E hE G hG).choose

/-- The chosen projection formula is an isomorphism at every `M ∈ D_QCoh(𝒪_Y)`. -/
theorem isIso_tensorDirectImageProjectionFormula_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) :
    IsIso ((tensorDirectImageProjectionFormula B S hS hTop f hf hfqs hY E hE G hG).app M) :=
  (exists_unitHomProjectionFormula_tensorDirectImage B S hS hTop f hf hfqs hY E hE G hG).choose_spec
    M hM

/-- **`Hom(𝒪_Y, K ⊗^L -) ⟶ Hom(𝒪_X, E ⊗^L (𝒢^• ⊗^L Lf^*-))`**, as a natural transformation of
functors `D(𝒪_Y) ⥤ Ab`: the projection formula followed by the associativity of `⊗^L`. It is an
isomorphism at every `M ∈ D_QCoh(𝒪_Y)`
(`AlgebraicGeometry.Space.isIso_tensorDirectImageUnitHomNatTrans_app`). -/
def tensorDirectImageUnitHomNatTrans :
    (smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G) ⋙
        preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
      tensorCoefficientFunctor B S hS f E G ⋙ preadditiveCoyoneda.obj (op (structureDerived X)) :=
  tensorDirectImageProjectionFormula B S hS hTop f hf hfqs hY E hE G hG ≫
    Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS f)
      (Functor.isoWhiskerRight (smallEtaleDerivedTensorAssocNatIso B S hS X E
        (DerivedCategory.Q.obj G)) (preadditiveCoyoneda.obj (op (structureDerived X)))).hom

/-- `tensorDirectImageUnitHomNatTrans` is an isomorphism at every `M ∈ D_QCoh(𝒪_Y)`. -/
theorem isIso_tensorDirectImageUnitHomNatTrans_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) :
    IsIso ((tensorDirectImageUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).app M) := by
  have hθ := isIso_tensorDirectImageProjectionFormula_app B S hS hTop f hf hfqs hY E hE G hG M hM
  have hA := NatIso.hom_app_isIso (Functor.isoWhiskerRight (smallEtaleDerivedTensorAssocNatIso B S
    hS X E (DerivedCategory.Q.obj G)) (preadditiveCoyoneda.obj (op (structureDerived X))))
    ((smallEtaleDerivedModulePullback B S hS f).obj M)
  exact IsIso.comp_isIso' hθ hA

/-- **`Hom(𝒪_Y, (K ⊗^L -)[i]) ⟶ Hom(𝒪_X, (E ⊗^L (𝒢^• ⊗^L Lf^*-))[i])`**:
`tensorDirectImageUnitHomNatTrans` at `-[i]`, read through the commutation of the two functors with
the shift by `i`. -/
def tensorDirectImageShiftedNatTrans (i : ℤ) :
    (smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G) ⋙
        shiftFunctor _ i ⋙ preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
      tensorCoefficientFunctor B S hS f E G ⋙ shiftFunctor _ i ⋙
        preadditiveCoyoneda.obj (op (structureDerived X)) :=
  (Functor.isoWhiskerRight (((smallEtaleDerivedTensor B S hS Y).obj
      (tensorDirectImageObj B S hS f E G)).commShiftIso i).symm
      (preadditiveCoyoneda.obj (op (structureDerived Y)))).hom ≫
    Functor.whiskerLeft (shiftFunctor _ i)
      (tensorDirectImageUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG) ≫
    (Functor.isoWhiskerRight ((tensorCoefficientFunctor B S hS f E G).commShiftIso i)
      (preadditiveCoyoneda.obj (op (structureDerived X)))).hom

/-- The component of `tensorDirectImageShiftedNatTrans` at `M` is the component of
`tensorDirectImageUnitHomNatTrans` at `M[i]` between the two commutation isomorphisms with the
shift. -/
theorem tensorDirectImageShiftedNatTrans_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (i : ℤ) :
    (tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M =
      (preadditiveCoyoneda.obj (op (structureDerived Y))).map
          ((((smallEtaleDerivedTensor B S hS Y).obj
            (tensorDirectImageObj B S hS f E G)).commShiftIso i).inv.app M) ≫
        (tensorDirectImageUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).app (M⟦i⟧) ≫
        (preadditiveCoyoneda.obj (op (structureDerived X))).map
          (((tensorCoefficientFunctor B S hS f E G).commShiftIso i).hom.app M) :=
  rfl

/-- `tensorDirectImageShiftedNatTrans` is an isomorphism at every `M ∈ D_QCoh(𝒪_Y)`. -/
theorem isIso_tensorDirectImageShiftedNatTrans_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) (i : ℤ) :
    IsIso ((tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M) := by
  rw [tensorDirectImageShiftedNatTrans_app]
  have h1 := isIso_tensorDirectImageUnitHomNatTrans_app B S hS hTop f hf hfqs hY E hE G hG (M⟦i⟧)
    (qcohDerived_shift M i hM)
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' h1 (Functor.map_isIso _ _))

/-- **The shifted comparison carries the boundary maps of `K ⊗^L -` to those of
`E ⊗^L (𝒢^• ⊗^L Lf^*-)`.** -/
theorem tensorDirectImageShiftedNatTrans_delta
    {M₁ M₃ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (a : M₃ ⟶ M₁⟦(1 : ℤ)⟧) (i j : ℤ) (h : 1 + i = j) :
    (preadditiveCoyoneda.obj (op (structureDerived Y))).map
        ((((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G)).map a ≫
          (((smallEtaleDerivedTensor B S hS Y).obj
            (tensorDirectImageObj B S hS f E G)).commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
          (shiftFunctorAdd' _ 1 i j h).inv.app (((smallEtaleDerivedTensor B S hS Y).obj
            (tensorDirectImageObj B S hS f E G)).obj M₁)) ≫
        (tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG j).app M₁ =
      (tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M₃ ≫
        (preadditiveCoyoneda.obj (op (structureDerived X))).map
          (((tensorCoefficientFunctor B S hS f E G).map a ≫
            ((tensorCoefficientFunctor B S hS f E G).commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
            (shiftFunctorAdd' _ 1 i j h).inv.app
              ((tensorCoefficientFunctor B S hS f E G).obj M₁)) := by
  rw [tensorDirectImageShiftedNatTrans_app, tensorDirectImageShiftedNatTrans_app]
  exact Functor.shiftedNatTrans_delta_aux _ _ _ _ _ a i j h


section Cohomology

attribute [local instance 20000] ModuleCat.hasDerivedCategory

/-- **`H^i(Y, K ⊗^L ℱ)`** as a functor of the `𝒪_Y`-module `ℱ`, `K = Rf_*(E ⊗^L 𝒢^•)`. -/
abbrev cohomologyTensorDirectImage (i : ℤ) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤ AddCommGrpCat.{u + 1} :=
  CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q ⋙
    (smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G) ⋙
    derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2 ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) i ⋙
    forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) AddCommGrpCat.{u + 1}

/-- **`H^i(X, E ⊗^L (𝒢^• ⊗ f^*ℱ))`** as a functor of the `𝒪_Y`-module `ℱ`. -/
abbrev cohomologyTensorPullbackComplex (i : ℤ) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤ AddCommGrpCat.{u + 1} :=
  CochainComplex.singleFunctor _ 0 ⋙ tensorPullbackComplex f G ⋙ DerivedCategory.Q ⋙
    (smallEtaleDerivedTensor B S hS X).obj E ⋙
    derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2 ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i ⋙
    forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) AddCommGrpCat.{u + 1}

/-- The comparison `H^i(Y, K ⊗^L M) ⟶ H^i(X, E ⊗^L (𝒢^• ⊗ f^*M))` for a complex `M` of
`𝒪_Y`-modules, universe-lifted: `H^i = Hom(𝒪, -[i])` on both sides, the shifted comparison of
`Hom(𝒪_Y, K ⊗^L -)` with `Hom(𝒪_X, E ⊗^L (𝒢^• ⊗^L Lf^*-))`, and
`𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M`. -/
def cohomologyTensorDirectImageComplexNatTrans (i : ℤ) :
    DerivedCategory.Q ⋙
        (smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G) ⋙
        derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2 ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) i ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1} ⟶
      tensorPullbackComplex f G ⋙ DerivedCategory.Q ⋙ (smallEtaleDerivedTensor B S hS X).obj E ⋙
        derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2 ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) i ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1} :=
  Functor.whiskerLeft DerivedCategory.Q (Functor.whiskerLeft
      ((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G))
      (cohomologyIsoUnitHomShift Y i).hom) ≫
    Functor.whiskerLeft DerivedCategory.Q (Functor.whiskerRight
      (tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i)
      AddCommGrpCat.uliftFunctor.{u + 1, u + 1}) ≫
    Functor.whiskerRight (Functor.whiskerRight (tensorPullbackComplexNatTrans f G)
      ((smallEtaleDerivedTensor B S hS X).obj E))
      (shiftFunctor (DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS X))) i ⋙
        unitHomLifted X) ≫
    Functor.whiskerLeft (tensorPullbackComplex f G ⋙ DerivedCategory.Q ⋙
      (smallEtaleDerivedTensor B S hS X).obj E) (cohomologyIsoUnitHomShift X i).inv

/-- The component of `cohomologyTensorDirectImageComplexNatTrans` at a complex `M`, as the
composite of its four factors. -/
theorem cohomologyTensorDirectImageComplexNatTrans_app (i : ℤ)
    (M : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    (cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M =
      (cohomologyIsoUnitHomShift Y i).hom.app (((smallEtaleDerivedTensor B S hS Y).obj
          (tensorDirectImageObj B S hS f E G)).obj (DerivedCategory.Q.obj M)) ≫
        AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map
          ((tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app
            (DerivedCategory.Q.obj M)) ≫
        (shiftFunctor (DerivedCategory (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS X))) i ⋙ unitHomLifted X).map
            (((smallEtaleDerivedTensor B S hS X).obj E).map
              ((tensorPullbackComplexNatTrans f G).app M)) ≫
        (cohomologyIsoUnitHomShift X i).inv.app (((smallEtaleDerivedTensor B S hS X).obj E).obj
          (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M))) :=
  rfl


/-- A quasi-coherent module placed in degree `0` lies in `D_QCoh`. -/
theorem qcohDerived_Q_single_of_isQuasicoherentOnSite
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hF : F.IsQuasicoherentOnSite) :
    QcohDerived B S hS Y (DerivedCategory.Q.obj
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F)) := by
  refine (qcohDerived_Q_obj_iff B S hS _).2 (fun q => ?_)
  by_cases hq : q = 0
  · subst hq
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 F).symm hF
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 F q hq)

include hG in
/-- `cohomologyTensorDirectImageComplexNatTrans` is an isomorphism at a quasi-coherent module
placed in degree `0`. -/
theorem isIso_cohomologyTensorDirectImageComplexNatTrans_app_single (i : ℤ)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F)) := by
  obtain ⟨a, b, hGb⟩ := hG.bounded
  have hτ : IsIso ((tensorPullbackComplexNatTrans f G).app
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F)) :=
    isIso_tensorPullbackComplexNatTrans_app_single a b hGb
      (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) F
  have hN := isIso_tensorDirectImageShiftedNatTrans_app B S hS hTop f hf hfqs hY E hE G hG
    (DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F))
    (qcohDerived_Q_single_of_isQuasicoherentOnSite B S hS F hF) i
  rw [cohomologyTensorDirectImageComplexNatTrans_app]
  exact IsIso.comp_isIso' (Iso.isIso_hom ((cohomologyIsoUnitHomShift Y i).app _))
    (IsIso.comp_isIso' (Iso.isIso_hom (AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.mapIso
      (@asIso _ _ _ _ _ hN))) (IsIso.comp_isIso' (Functor.map_isIso _ _)
        (Iso.isIso_inv ((cohomologyIsoUnitHomShift X i).app _))))

/-- A commutative square pushed through a functor and pasted with a naturality square. -/
theorem cohomologyTensorDirectImage_map_square_aux {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B P Q R : C} {Z Z' : D} (pa : A ⟶ B) (pc : B ⟶ P) (t₁ : P ⟶ Q) (t₃ : A ⟶ R)
    (b : R ⟶ Q) (c : F.obj P ⟶ Z) (c' : F.obj Q ⟶ Z') (W : Z ⟶ Z')
    (hnat : F.map t₁ ≫ c' = c ≫ W) (hab : pa ≫ pc ≫ t₁ = t₃ ≫ b) :
    F.map pa ≫ (F.map pc ≫ c) ≫ W = F.map t₃ ≫ F.map b ≫ c' := by
  rw [Category.assoc, ← hnat, ← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, hab,
    F.map_comp_assoc]

/-- A commutative square `u ≫ g⟦1⟧' = v ≫ w`, shifted by `i`. -/
theorem cohomologyTensorDirectImage_shift_square_aux {D : Type*} [Category D] [HasShift D ℤ]
    {A A' B B' : D} (u : A ⟶ B⟦(1 : ℤ)⟧) (g : B ⟶ B') (v : A ⟶ A') (w : A' ⟶ B'⟦(1 : ℤ)⟧)
    (hs : u ≫ g⟦(1 : ℤ)⟧' = v ≫ w) (i j : ℤ) (h' : 1 + i = j) :
    (u⟦i⟧' ≫ (shiftFunctorAdd' D 1 i j h').inv.app B) ≫ g⟦j⟧' =
      v⟦i⟧' ≫ (w⟦i⟧' ≫ (shiftFunctorAdd' D 1 i j h').inv.app B') := by
  have nat := (shiftFunctorAdd' D 1 i j h').inv.naturality g
  simp only [Functor.comp_map] at nat
  rw [Category.assoc, ← nat, ← Functor.map_comp_assoc, hs, Functor.map_comp_assoc]

/-- The comparison `𝒢^• ⊗^L Lf^*(-) ⟶ 𝒢^• ⊗ f^*(-)`, tensored with `E`, on a morphism
`M₃ ⟶ M₁[1]` and its counterpart. -/
theorem tensorCoefficientFunctor_map_comp_natTrans
    {M₁ M₃ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (a : DerivedCategory.Q.obj M₃ ⟶ (DerivedCategory.Q.obj M₁)⟦(1 : ℤ)⟧)
    (b : DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₃) ⟶
      (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁))⟦(1 : ℤ)⟧)
    (hab : (extPerfectCoefficientFunctor B S hS f G).map a ≫
      ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Q.obj M₁) ≫
      ((tensorPullbackComplexNatTrans f G).app M₁)⟦(1 : ℤ)⟧' =
        (tensorPullbackComplexNatTrans f G).app M₃ ≫ b) :
    (tensorCoefficientFunctor B S hS f E G).map a ≫
      ((tensorCoefficientFunctor B S hS f E G).commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Q.obj M₁) ≫
      (((smallEtaleDerivedTensor B S hS X).obj E).map
      ((tensorPullbackComplexNatTrans f G).app M₁))⟦(1 : ℤ)⟧' =
      ((smallEtaleDerivedTensor B S hS X).obj E).map ((tensorPullbackComplexNatTrans f G).app M₃) ≫
        ((smallEtaleDerivedTensor B S hS X).obj E).map b ≫
        (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁)) := by
  have nat : ((smallEtaleDerivedTensor B S hS X).obj E).map
    (((tensorPullbackComplexNatTrans f G).app M₁)⟦(1 : ℤ)⟧') ≫
      (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁)) =
      (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.app
        ((extPerfectCoefficientFunctor B S hS f G).obj (DerivedCategory.Q.obj M₁)) ≫
        (((smallEtaleDerivedTensor B S hS X).obj E).map
        ((tensorPullbackComplexNatTrans f G).app M₁))⟦(1 : ℤ)⟧' :=
    (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.naturality
      ((tensorPullbackComplexNatTrans f G).app M₁)
  have e : ((tensorCoefficientFunctor B S hS f E G).commShiftIso (1 : ℤ)).hom.app
    (DerivedCategory.Q.obj M₁) =
      ((smallEtaleDerivedTensor B S hS X).obj E).map
        (((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj M₁)) ≫
        (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.app
          ((extPerfectCoefficientFunctor B S hS f G).obj (DerivedCategory.Q.obj M₁)) :=
    Functor.commShiftIso_comp_hom_app (extPerfectCoefficientFunctor B S hS f G)
      ((smallEtaleDerivedTensor B S hS X).obj E) (1 : ℤ) (DerivedCategory.Q.obj M₁)
  exact (congrArg (fun t => (tensorCoefficientFunctor B S hS f E G).map a ≫ t ≫
    (((smallEtaleDerivedTensor B S hS X).obj E).map
      ((tensorPullbackComplexNatTrans f G).app M₁))⟦(1 : ℤ)⟧') e).trans
    (cohomologyTensorDirectImage_map_square_aux ((smallEtaleDerivedTensor B S hS X).obj E)
      ((extPerfectCoefficientFunctor B S hS f G).map a) _ _ _ b _ _ _ nat hab)

/-- The shifted form of `tensorCoefficientFunctor_map_comp_natTrans`. -/
theorem tensorCoefficientFunctor_map_comp_natTrans_shift
    {M₁ M₃ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (a : DerivedCategory.Q.obj M₃ ⟶ (DerivedCategory.Q.obj M₁)⟦(1 : ℤ)⟧)
    (b : DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₃) ⟶
      (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁))⟦(1 : ℤ)⟧)
    (hab : (extPerfectCoefficientFunctor B S hS f G).map a ≫
      ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Q.obj M₁) ≫
      ((tensorPullbackComplexNatTrans f G).app M₁)⟦(1 : ℤ)⟧' =
        (tensorPullbackComplexNatTrans f G).app M₃ ≫ b) (i j : ℤ) (h' : 1 + i = j) :
    (((tensorCoefficientFunctor B S hS f E G).map a ≫
      ((tensorCoefficientFunctor B S hS f E G).commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Q.obj M₁))⟦i⟧' ≫
        (shiftFunctorAdd' _ 1 i j h').inv.app ((tensorCoefficientFunctor B S hS f E G).obj
          (DerivedCategory.Q.obj M₁))) ≫
          (((smallEtaleDerivedTensor B S hS X).obj E).map
          ((tensorPullbackComplexNatTrans f G).app M₁))⟦j⟧' =
      (((smallEtaleDerivedTensor B S hS X).obj E).map
        ((tensorPullbackComplexNatTrans f G).app M₃))⟦i⟧' ≫
        ((((smallEtaleDerivedTensor B S hS X).obj E).map b ≫
        (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁)))⟦i⟧' ≫
            (shiftFunctorAdd' _ 1 i j h').inv.app (((smallEtaleDerivedTensor B S hS X).obj E).obj
            (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁)))) :=
  cohomologyTensorDirectImage_shift_square_aux _ _ _ _
    ((Category.assoc _ _ _).trans (tensorCoefficientFunctor_map_comp_natTrans B S hS f E G a b hab))
    i j h'

/-- Pasting two commutative squares. -/
theorem cohomologyTensorDirectImage_δ_aux₂ {C : Type*} [Category C] {Q₁ Q₃ R₁ R₃ S₁ S₃ : C}
    {z : Q₃ ⟶ Q₁} {nj : Q₁ ⟶ R₁} {ni : Q₃ ⟶ R₃} {z' : R₃ ⟶ R₁} {wj : R₁ ⟶ S₁} {wi : R₃ ⟶ S₃}
    {z'' : S₃ ⟶ S₁} (h₂ : z ≫ nj = ni ≫ z') (h₃ : z' ≫ wj = wi ≫ z'') :
    z ≫ nj ≫ wj = ni ≫ wi ≫ z'' := by
  rw [reassoc_of% h₂, h₃]

/-- A functor carries an equality of composites to an equality of composites. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' P : C} {f : A ⟶ B} {g : B ⟶ P} {f' : A ⟶ B'} {g' : B' ⟶ P} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- **The comparison `Hom(𝒪_Y, (K ⊗^L -)[•]) ⟶ Hom(𝒪_X, (E ⊗^L (𝒢^• ⊗ f^*-))[•])` on boundary
maps**, for a morphism `a : M₃ ⟶ M₁[1]` and its counterpart `b` for `𝒢^• ⊗ f^*(-)`. -/
theorem tensorDirectImageUnitHom_δ
    {M₁ M₃ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (a : DerivedCategory.Q.obj M₃ ⟶ (DerivedCategory.Q.obj M₁)⟦(1 : ℤ)⟧)
    (b : DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₃) ⟶
      (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁))⟦(1 : ℤ)⟧)
    (hab : (extPerfectCoefficientFunctor B S hS f G).map a ≫
      ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
      (DerivedCategory.Q.obj M₁) ≫
      ((tensorPullbackComplexNatTrans f G).app M₁)⟦(1 : ℤ)⟧' =
        (tensorPullbackComplexNatTrans f G).app M₃ ≫ b) (i j : ℤ) (h' : 1 + i = j) :
    (unitHomLifted Y).map ((shiftFunctor (DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y))) i).map (((smallEtaleDerivedTensor B S hS Y).obj
      (tensorDirectImageObj B S hS f E G)).map a ≫
      (((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G)).commShiftIso
      (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj M₁)) ≫
          (shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS Y))) 1 i j h').inv.app
          (((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G)).obj
          (DerivedCategory.Q.obj M₁))) ≫
      AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map
        ((tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG j).app
        (DerivedCategory.Q.obj M₁)) ≫
      (shiftFunctor (DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS X))) j ⋙
        unitHomLifted X).map (((smallEtaleDerivedTensor B S hS X).obj E).map
        ((tensorPullbackComplexNatTrans f G).app M₁)) =
    AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map
      ((tensorDirectImageShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app
      (DerivedCategory.Q.obj M₃)) ≫
      (shiftFunctor (DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS X))) i ⋙
        unitHomLifted X).map (((smallEtaleDerivedTensor B S hS X).obj E).map
        ((tensorPullbackComplexNatTrans f G).app M₃)) ≫
      (unitHomLifted X).map ((shiftFunctor (DerivedCategory (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS X))) i).map
        (((smallEtaleDerivedTensor B S hS X).obj E).map b ≫
        (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj M₁))) ≫
          (shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS X))) 1 i j h').inv.app
            (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj
            ((tensorPullbackComplex f G).obj M₁)))) := by
  have hN := tensorDirectImageShiftedNatTrans_delta B S hS hTop f hf hfqs hY E hE G hG a i j h'
  have s2 := map_comp_eq_map_comp AddCommGrpCat.uliftFunctor.{u + 1, u + 1} hN
  have s3 := tensorCoefficientFunctor_map_comp_natTrans_shift B S hS f E G a b hab i j h'
  have s3' := map_comp_eq_map_comp (unitHomLifted X) s3
  exact cohomologyTensorDirectImage_δ_aux₂ s2 s3'

/-- `AlgebraicGeometry.Space.cohomologyIsoUnitHomShift_homologySequenceδ` for a triangle given by
its three morphisms, in the spelling of this file. -/
theorem cohomologyIsoUnitHomShift_homologySequenceδ_mk (W : AlgebraicSpaces B S hS)
    {A₁ A₂ A₃ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W))}
    (u' : A₁ ⟶ A₂) (v : A₂ ⟶ A₃) (w : A₃ ⟶ A₁⟦(1 : ℤ)⟧) (i j : ℤ) (h : i + 1 = j)
    (h' : 1 + i = j) :
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS W.1 W.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS W.1 W.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS W.1 W.2).mapTriangle.obj
            (Pretriangulated.Triangle.mk u' v w)) i j h) ≫
        (cohomologyIsoUnitHomShift W j).hom.app A₁ =
      (cohomologyIsoUnitHomShift W i).hom.app A₃ ≫
        (unitHomLifted W).map ((shiftFunctor (DerivedCategory (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS W))) i).map w ≫
            (shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS W))) 1 i j h').inv.app A₁) :=
  cohomologyIsoUnitHomShift_homologySequenceδ W (Pretriangulated.Triangle.mk u' v w) i j h

/-- Pasting: the first two squares. -/
theorem cohomologyTensorDirectImage_δ_auxL {C : Type*} [Category C]
    {P₁ P₃ Q₁ Q₃ R₁ R₃ S₁ S₃ : C} {dL : P₃ ⟶ P₁} {cj : P₁ ⟶ Q₁} {ci : P₃ ⟶ Q₃}
    {z : Q₃ ⟶ Q₁} {nj : Q₁ ⟶ R₁} {ni : Q₃ ⟶ R₃} {wj : R₁ ⟶ S₁} {wi : R₃ ⟶ S₃}
    {z'' : S₃ ⟶ S₁} (h₁ : dL ≫ cj = ci ≫ z) (h₂ : z ≫ nj ≫ wj = ni ≫ wi ≫ z'') :
    dL ≫ cj ≫ nj ≫ wj = ci ≫ ni ≫ wi ≫ z'' := by
  rw [reassoc_of% h₁, h₂]

/-- Pasting: the last square. -/
theorem cohomologyTensorDirectImage_δ_auxR {C : Type*} [Category C]
    {P₁ P₃ Q₁ Q₃ R₁ R₃ S₁ S₃ T₁ T₃ : C} {dL : P₃ ⟶ P₁} {cj : P₁ ⟶ Q₁} {ci : P₃ ⟶ Q₃}
    {nj : Q₁ ⟶ R₁} {ni : Q₃ ⟶ R₃} {wj : R₁ ⟶ S₁} {wi : R₃ ⟶ S₃}
    {z'' : S₃ ⟶ S₁} {dj : S₁ ⟶ T₁} {di : S₃ ⟶ T₃} {dR : T₃ ⟶ T₁}
    (h₁ : dL ≫ cj ≫ nj ≫ wj = ci ≫ ni ≫ wi ≫ z'') (h₄ : z'' ≫ dj = di ≫ dR) :
    dL ≫ cj ≫ nj ≫ wj ≫ dj = (ci ≫ ni ≫ wi ≫ di) ≫ dR := by
  rw [reassoc_of% h₁, h₄]
  simp only [Category.assoc]

/-- **The comparison is compatible with the boundary maps**, on complexes: for a short exact
sequence `Sc` of complexes of `𝒪_Y`-modules whose image under `𝒢^• ⊗ f^*(-)` is short exact and on
which `𝒢^• ⊗^L Lf^*(-) ⟶ 𝒢^• ⊗ f^*(-)` is compatible with the boundary maps, the boundary map of
`K ⊗^L` the triangle of `Sc` corresponds to the boundary map of the triangle of `𝒢^• ⊗ f^*Sc`
tensored with `E`. -/
theorem cohomologyTensorDirectImageComplexNatTrans_δ
    {Sc : ShortComplex (CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) ℤ)}
    (hSc : Sc.ShortExact) (hΨS : (Sc.map (tensorPullbackComplex f G)).ShortExact)
    (hδ : (extPerfectCoefficientFunctor B S hS f G).map (DerivedCategory.triangleOfSESδ hSc) ≫
      ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj Sc.X₁) ≫ ((tensorPullbackComplexNatTrans f G).app Sc.X₁)⟦(1 : ℤ)⟧' =
        (tensorPullbackComplexNatTrans f G).app Sc.X₃ ≫ DerivedCategory.triangleOfSESδ hΨS)
    (i j : ℤ) (h : i + 1 = j) :
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapTriangle.obj
            (((smallEtaleDerivedTensor B S hS Y).obj
              (tensorDirectImageObj B S hS f E G)).mapTriangle.obj
              (DerivedCategory.triangleOfSES
                hSc)))
          i j h) ≫
        (cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG j).app
          Sc.X₁ =
      (cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app
          Sc.X₃ ≫
        (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).mapTriangle.obj
            (((smallEtaleDerivedTensor B S hS X).obj E).mapTriangle.obj
              (DerivedCategory.triangleOfSES hΨS)))
          i j h) := by
  have h' : 1 + i = j := by omega
  have hL := cohomologyIsoUnitHomShift_homologySequenceδ_mk B S hS Y
    (((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G)).map
      (DerivedCategory.Q.map Sc.f))
      (((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G)).map
        (DerivedCategory.Q.map Sc.g))
      (((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G)).map
        (DerivedCategory.triangleOfSESδ hSc) ≫
        (((smallEtaleDerivedTensor B S hS Y).obj (tensorDirectImageObj B S hS f E G)).commShiftIso
          (1 : ℤ)).hom.app (DerivedCategory.Q.obj Sc.X₁)) i j h h'
  have hR := cohomologyIsoUnitHomShift_homologySequenceδ_mk B S hS X
    (((smallEtaleDerivedTensor B S hS X).obj E).map (DerivedCategory.Q.map
      ((tensorPullbackComplex f G).map Sc.f)))
      (((smallEtaleDerivedTensor B S hS X).obj E).map (DerivedCategory.Q.map
        ((tensorPullbackComplex f G).map Sc.g)))
      (((smallEtaleDerivedTensor B S hS X).obj E).map (DerivedCategory.triangleOfSESδ hΨS) ≫
        (((smallEtaleDerivedTensor B S hS X).obj E).commShiftIso (1 : ℤ)).hom.app
          (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj Sc.X₁))) i j h h'
  have s4 := (Iso.comp_inv_eq ((cohomologyIsoUnitHomShift X j).app _)).2
    (((Iso.eq_inv_comp ((cohomologyIsoUnitHomShift X i).app _)).2 hR.symm).trans
      (Category.assoc _ _ _).symm)
  have s23 := tensorDirectImageUnitHom_δ B S hS hTop f hf hfqs hY E hE G hG
    (DerivedCategory.triangleOfSESδ hSc) (DerivedCategory.triangleOfSESδ hΨS) hδ i j h'
  refine (congrArg (fun t => _ ≫ t) (cohomologyTensorDirectImageComplexNatTrans_app B S hS hTop f
    hf hfqs hY E hE G hG j Sc.X₁)).trans (Eq.trans ?_ (congrArg (fun t => t ≫ _)
      (cohomologyTensorDirectImageComplexNatTrans_app B S hS hTop f hf hfqs hY E hE G hG i
        Sc.X₃)).symm)
  have A1 := cohomologyTensorDirectImage_δ_auxL hL s23
  have A2 := cohomologyTensorDirectImage_δ_auxR A1 s4
  exact A2

/-- **The comparison `H^i(Y, K ⊗^L ℱ) ⟶ H^i(X, E ⊗^L (𝒢^• ⊗ f^*ℱ))`** of Stacks 0A1M, natural in
the `𝒪_Y`-module `ℱ`; it is an isomorphism for `ℱ` quasi-coherent
(`AlgebraicGeometry.Space.isIso_cohomologyTensorDirectImageNatTrans_app`). -/
def cohomologyTensorDirectImageNatTrans (i : ℤ) :
    cohomologyTensorDirectImage B S hS f E G i ⟶ cohomologyTensorPullbackComplex B S hS f E G i :=
  (AddCommGrpCat.uliftFunctorFullyFaithful.{u + 1, u + 1}.whiskeringRight _).preimage
    (Functor.whiskerLeft (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)
      (cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG i))

/-- The universe lift of `cohomologyTensorDirectImageNatTrans` at `ℱ` is
`cohomologyTensorDirectImageComplexNatTrans` at `ℱ` placed in degree `0`. -/
theorem uliftFunctor_map_cohomologyTensorDirectImageNatTrans_app (i : ℤ)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map
        ((cohomologyTensorDirectImageNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app F) =
      (cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).obj F) :=
  AddCommGrpCat.uliftFunctorFullyFaithful.{u + 1, u + 1}.map_preimage _

include hG in
/-- `cohomologyTensorDirectImageNatTrans` is an isomorphism at every quasi-coherent `ℱ`. -/
theorem isIso_cohomologyTensorDirectImageNatTrans_app (i : ℤ)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((cohomologyTensorDirectImageNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app F) := by
  have h := isIso_cohomologyTensorDirectImageComplexNatTrans_app_single B S hS hTop f hf hfqs hY
    E hE G hG i F hF
  rw [← uliftFunctor_map_cohomologyTensorDirectImageNatTrans_app] at h
  exact AddCommGrpCat.uliftFunctorFullyFaithful.{u + 1, u + 1}.isIso_of_isIso_map _

/-- `AlgebraicGeometry.Space.tensorPullbackComplexNatTrans_triangleOfSESδ` in the spelling of this
file. -/
theorem tensorPullbackComplexNatTrans_triangleOfSESδ_coefficient
    (hGf : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) :
    (extPerfectCoefficientFunctor B S hS f G).map (DerivedCategory.triangleOfSESδ (hT.map_of_exact
      (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0))) ≫
      ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj (T.map (HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)).X₁) ≫
      ((tensorPullbackComplexNatTrans f G).app (T.map (HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)).X₁)⟦(1 : ℤ)⟧' =
    (tensorPullbackComplexNatTrans f G).app (T.map (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)).X₃ ≫
      DerivedCategory.triangleOfSESδ (shortExact_tensorPullbackComplex_map_single hGf hT) :=
  tensorPullbackComplexNatTrans_triangleOfSESδ hGf hT

/-- `AlgebraicGeometry.Space.cohomologyTensorDirectImageComplexNatTrans_δ` for the short exact
sequence of complexes of a short exact sequence of `𝒪_Y`-modules. -/
theorem cohomologyTensorDirectImageComplexNatTrans_δ_single
    (hGf : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) (i j : ℤ) (h : i + 1 = j) :
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapTriangle.obj
            (((smallEtaleDerivedTensor B S hS Y).obj
              (tensorDirectImageObj B S hS f E G)).mapTriangle.obj
              (DerivedCategory.triangleOfSES
                (hT.map_of_exact (HomologicalComplex.single (SheafOfModules.{u}
                  (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)))))
          i j h) ≫
        (cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG j).app
          (T.map (HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)).X₁ =
      (cohomologyTensorDirectImageComplexNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app
          (T.map (HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)).X₃ ≫
        (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).mapTriangle.obj
            (((smallEtaleDerivedTensor B S hS X).obj E).mapTriangle.obj
              (DerivedCategory.triangleOfSES (shortExact_tensorPullbackComplex_map_single hGf hT))))
          i j h) :=
  cohomologyTensorDirectImageComplexNatTrans_δ B S hS hTop f hf hfqs hY E hE G hG
    (hT.map_of_exact (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0)) (shortExact_tensorPullbackComplex_map_single hGf hT)
    (tensorPullbackComplexNatTrans_triangleOfSESδ_coefficient B S hS f G hGf hT) i j h

include hG in
/-- **The comparison of Stacks 0A1M is compatible with the boundary maps.** -/
theorem cohomologyTensorDirectImageNatTrans_δ
    {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hT : T.ShortExact) (i j : ℤ) (h : i + 1 = j) :
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
          AddCommGrpCat.{u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapTriangle.obj
            (((smallEtaleDerivedTensor B S hS Y).obj
              (tensorDirectImageObj B S hS f E G)).mapTriangle.obj
              (DerivedCategory.triangleOfSES
                (hT.map_of_exact (HomologicalComplex.single (SheafOfModules.{u}
                  (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)))))
          i j h) ≫
        (cohomologyTensorDirectImageNatTrans B S hS hTop f hf hfqs hY E hE G hG j).app T.X₁ =
      (cohomologyTensorDirectImageNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app T.X₃ ≫
        (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
          AddCommGrpCat.{u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).mapTriangle.obj
            (((smallEtaleDerivedTensor B S hS X).obj E).mapTriangle.obj
              (DerivedCategory.triangleOfSES (shortExact_tensorPullbackComplex_map_single
                ((FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG)) hT))))
          i j h) := by
  have key := cohomologyTensorDirectImageComplexNatTrans_δ_single B S hS hTop f hf hfqs hY E hE G hG
    (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT i j h
  apply AddCommGrpCat.uliftFunctorFullyFaithful.{u + 1, u + 1}.map_injective
  exact (AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map_comp _ _).trans
    ((congrArg (fun t => _ ≫ t) (uliftFunctor_map_cohomologyTensorDirectImageNatTrans_app B S hS
      hTop f hf hfqs hY E hE G hG j T.X₁)).trans (key.trans
        ((congrArg (fun t => t ≫ _) (uliftFunctor_map_cohomologyTensorDirectImageNatTrans_app B S
          hS hTop f hf hfqs hY E hE G hG i T.X₃)).symm.trans
            (AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map_comp _ _).symm)))

include hTop hfqs hY hE hG in
/-- **Stacks 0A1M.** Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism locally of
finite type and quasi-separated. Let `E` be a perfect object of `D(𝒪_X)` and `𝒢^•` a bounded
complex of coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`, and
`K = Rf_*(E ⊗^L 𝒢^•)` (Stacks 0DKJ). Then there are maps
`H^i(Y, K ⊗^L ℱ) ⟶ H^i(X, E ⊗^L (𝒢^• ⊗ f^*ℱ))`, natural in the `𝒪_Y`-module `ℱ`, which are
isomorphisms for `ℱ` quasi-coherent, and which are compatible with the boundary maps: for a short
exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` the boundary maps of the triangle
`K ⊗^L ℱ₁ → K ⊗^L ℱ₂ → K ⊗^L ℱ₃ → K ⊗^L ℱ₁[1]` correspond to those of the triangle of the short
exact sequence of complexes `0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0` tensored with `E`.
Here `⊗^L` is the canonical derived tensor product on the small étale site. -/
@[stacks 0A1M]
theorem exists_cohomologyTensorDirectImage_iso :
    ∃ η : ∀ i : ℤ, cohomologyTensorDirectImage B S hS f E G i ⟶
        cohomologyTensorPullbackComplex B S hS f E G i,
      (∀ (i : ℤ) (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
        F.IsQuasicoherentOnSite → IsIso ((η i).app F)) ∧
      ∀ {T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
        (hT : T.ShortExact) (i j : ℤ) (h : i + 1 = j),
        (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
              AddCommGrpCat.{u + 1}).map
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).homologySequenceδ
              ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapTriangle.obj
                (((smallEtaleDerivedTensor B S hS Y).obj
                  (tensorDirectImageObj B S hS f E G)).mapTriangle.obj
                  (DerivedCategory.triangleOfSES
                    (hT.map_of_exact (HomologicalComplex.single (SheafOfModules.{u}
                      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)))))
              i j h) ≫ (η j).app T.X₁ =
          (η i).app T.X₃ ≫
            (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2))
              AddCommGrpCat.{u + 1}).map
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS X.1 X.2)) 0).homologySequenceδ
              ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS X.1 X.2).mapTriangle.obj
                (((smallEtaleDerivedTensor B S hS X).obj E).mapTriangle.obj
                  (DerivedCategory.triangleOfSES (shortExact_tensorPullbackComplex_map_single
                    ((FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG))
                      hT))))
              i j h) :=
  ⟨cohomologyTensorDirectImageNatTrans B S hS hTop f hf hfqs hY E hE G hG,
    fun i F hF => isIso_cohomologyTensorDirectImageNatTrans_app B S hS hTop f hf hfqs hY E hE G hG
      i F hF,
    fun hT i j h => cohomologyTensorDirectImageNatTrans_δ B S hS hTop f hf hfqs hY E hE G hG
      hT i j h⟩

end Cohomology

end Comparison

end AlgebraicGeometry.Space

end
