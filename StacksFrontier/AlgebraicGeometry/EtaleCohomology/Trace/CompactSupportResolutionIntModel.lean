module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwo
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusObjSingleIsoQ
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomologyComposition
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDegreeZeroBridge

/-!
# The resolution model of `Hᵐ_c(X_k̄, F)` read over `ℤ`

Let `I` be an injective resolution of `j_! F` on the compactification `X̄`, `F` a sheaf of
`Λ`-modules. `Hᵐ_c(X_k̄, F) = Hᵐ(X̄_k̄, (j_! F)|)` is computed by the acyclic complex
`Γ(X̄_k̄, I|)` (`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`). Read in abelian groups
through `res_ℤ Hᵐ(X̄_k̄, -) ≅ Hᵐ(X̄_k̄, res_ℤ -)`
(`Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIntIso`), the class of a cocycle `x` of
`Γ(X̄_k̄, I|)` is the class of the same sections, read as a cocycle of `Γ_ℤ(X̄_k̄, res_ℤ I|)`, in
the computation of `Hᵐ(X̄_k̄, res_ℤ (j_! F)|)` on the acyclic resolution `res_ℤ I|`
(`restrictScalars_galoisCompactSupportResolutionIso_trans_rightDerivedPlusRestrictScalarsIntIso`).

This is the form in which `H²_c` of a morphism of resolutions over `ℤ` is compared with the
coefficient change of the S6a bridge in the base case of Tag 03VM.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- `etaleModules_enoughInjectives` at the coefficient universe `0`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_resolutionIntModel (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section Acyclic

variable {Λ : Type} [Ring Λ] (Y : Scheme.{u})

/-- **`res_ℤ` keeps `Γ`-acyclic sheaves acyclic**: `Hⁱ(Y, res_ℤ N) ≅ res_ℤ Hⁱ(Y, N)`. -/
theorem rightAcyclic_restrictScalarsInt_of_rightAcyclic (N : EtaleModules.{u, 0} Λ Y)
    (hN : (etaleModuleGlobalSections.{u, 0} Λ Y).rightAcyclic N) :
    (etaleModuleGlobalSections.{u, 0} ℤ Y).rightAcyclic
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N) := by
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _ _).2 inferInstance).2
    fun i hi => ?_
  have h := ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _ _).2 inferInstance).1
    hN i hi
  exact ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map_isZero h).of_iso
    (rightDerivedPlusRestrictScalarsIntIso Y N i).symm

end Acyclic

section HomologyElement

variable {Λ : Type} [Ring Λ]

/-- The cocycle of `K'` produced from `x` by `φ : res_ℤ K ⟶ K'` has underlying element `φ(x)`. -/
private lemma iCycles_cyclesMap_mapCyclesIso_inv_aux
    (K : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (K' : CochainComplex (ModuleCat.{u + 1} ℤ) ℤ)
    (φ : ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapHomologicalComplex _).obj K ⟶
      K')
    (m : ℤ) (x : K.cycles m) :
    (K'.iCycles m).hom ((HomologicalComplex.cyclesMap φ m).hom
        (((K.sc m).mapCyclesIso (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))).inv.hom
          x)) =
      (φ.f m).hom ((K.iCycles m).hom x) := by
  have hi : ((K.sc m).mapCyclesIso (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))).inv ≫
      ((K.sc m).map (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))).iCycles =
        (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map (K.sc m).iCycles := by
    rw [Iso.inv_comp_eq, ShortComplex.mapCyclesIso_hom_iCycles]
  exact (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ m) _).trans
    (congrArg (φ.f m).hom (ConcreteCategory.congr_hom hi x))

/-- **`res_ℤ Hᵐ(K) ≅ Hᵐ(res_ℤ K)` on classes**: the class of a cocycle `x` of a complex of
`Λ`-modules, followed by a morphism of complexes `φ : res_ℤ K ⟶ K'`, is the class of any cocycle
of `K'` with underlying element `φ(x)`. -/
theorem complexHomologyIso_inv_app_homologyMap_homologyπ
    (K : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (K' : CochainComplex (ModuleCat.{u + 1} ℤ) ℤ)
    (φ : ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapHomologicalComplex _).obj K ⟶
      K')
    (m : ℤ) (x : K.cycles m) (x' : K'.cycles m)
    (h : (K'.iCycles m).hom x' = (φ.f m).hom ((K.iCycles m).hom x)) :
    ((Stacks.DerivedFunctor.complexHomologyIso
        (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) (ComplexShape.up ℤ) m).inv.app K ≫
      HomologicalComplex.homologyMap φ m).hom ((K.homologyπ m).hom x) =
        (K'.homologyπ m).hom x' := by
  let rM := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let S := K.sc m
  have e1 : (Stacks.DerivedFunctor.complexHomologyIso rM (ComplexShape.up ℤ) m).inv.app K =
      (S.mapHomologyIso rM).inv :=
    congrArg Iso.inv (Iso.ext (Stacks.DerivedFunctor.complexHomologyIso_hom_app _ m rM K) :
      (Stacks.DerivedFunctor.complexHomologyIso rM (ComplexShape.up ℤ) m).app K =
        S.mapHomologyIso rM)
  have hπ : rM.map S.homologyπ ≫ (S.mapHomologyIso rM).inv =
      (S.mapCyclesIso rM).inv ≫ (S.map rM).homologyπ := by
    rw [Iso.comp_inv_eq, Category.assoc, ShortComplex.homologyπ_comp_mapHomologyIso_hom,
      Iso.inv_hom_id_assoc]
  let y : ((rM.mapHomologicalComplex _).obj K).cycles m := ((S.mapCyclesIso rM).inv).hom x
  have hy : (HomologicalComplex.cyclesMap φ m).hom y = x' := by
    apply (ModuleCat.mono_iff_injective (K'.iCycles m)).1 inferInstance
    exact (iCycles_cyclesMap_mapCyclesIso_inv_aux K K' φ m x).trans h.symm
  have h3 := ConcreteCategory.congr_hom hπ x
  have h4 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ m) y
  rw [e1]
  exact (congrArg (HomologicalComplex.homologyMap φ m).hom h3).trans (h4.trans
    (congrArg (K'.homologyπ m).hom hy))

/-- The cocycle of `K'` produced from a cocycle `x` of `K` by `φ : res_ℤ K ⟶ K'` has underlying
element `φ(x)`. -/
theorem iCycles_cyclesMap_mapCyclesIso_inv
    (K : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (K' : CochainComplex (ModuleCat.{u + 1} ℤ) ℤ)
    (φ : ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapHomologicalComplex _).obj K ⟶
      K')
    (m : ℤ) (x : K.cycles m) :
    (K'.iCycles m).hom ((HomologicalComplex.cyclesMap φ m).hom
        (((K.sc m).mapCyclesIso (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))).inv.hom
          x)) =
      (φ.f m).hom ((K.iCycles m).hom x) :=
  iCycles_cyclesMap_mapCyclesIso_inv_aux K K' φ m x

end HomologyElement

section Model

variable {Λ : Type} [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} {j : CompactificationOf (Over.mk f)}
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

/-- The terms of `res_ℤ I|_{X̄_k̄}` are `Γ_ℤ(X̄_k̄, -)`-acyclic. -/
theorem rightAcyclic_restrictScalarsInt_compactSupportResolutionRestriction
    (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (n : ℤ) :
    (etaleModuleGlobalSections.{u, 0} ℤ (fieldBaseChange (Over.mk j.toBase) kbar)).rightAcyclic
      (((etaleModuleRestrictScalars (Int.castRingHom Λ)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              I.cocomplexPlus)).obj.X n) :=
  rightAcyclic_restrictScalarsInt_of_rightAcyclic _ _
    (rightAcyclic_compactSupportResolutionRestriction F I n)

/-- **The augmentation `((j_! F)|_{X̄_k̄})[0] ⟶ I|_{X̄_k̄}`** of the restriction of an injective
resolution `I` of `j_! F`. -/
def compactSupportResolutionAugmentation (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj I.cocomplexPlus :=
  ((etaleModuleInverseImage.{u, 0} Λ
      (pullback.fst j.toBase (specAlgebraMap k kbar))).mapCochainComplexPlus.mapIso
      (mapCochainComplexPlusSinglePlusIso (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) F) ≪≫
    mapCochainComplexPlusSinglePlusIso
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar)))
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)).inv ≫
    compactSupportResolutionRestrictionMap (kbar := kbar) F I

/-- **The augmentation `res_ℤ((j_! F)|_{X̄_k̄})[0] ⟶ res_ℤ(I|_{X̄_k̄})`** of the restricted
resolution, as complexes of sheaves of abelian groups. -/
def compactSupportResolutionIntAugmentation (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ)
            (pullback j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom Λ)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              I.cocomplexPlus) :=
  (mapCochainComplexPlusSinglePlusIso (etaleModuleRestrictScalars (Int.castRingHom Λ)
      (pullback j.toBase (specAlgebraMap k kbar))) _).inv ≫
    (etaleModuleRestrictScalars (Int.castRingHom Λ)
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
        (compactSupportResolutionAugmentation kbar F I)

/-- **`((j_! F)|_{X̄_k̄})[0] ≅ I|_{X̄_k̄}` in `D⁺`**, the localization of the augmentation. -/
def compactSupportResolutionSingleIso (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ≅
      DerivedCategory.Plus.Q.obj ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj I.cocomplexPlus) :=
  (DerivedCategory.Plus.Q.mapIso
      ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst j.toBase (specAlgebraMap k kbar))).mapCochainComplexPlus.mapIso
          (mapCochainComplexPlusSinglePlusIso
            (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) F) ≪≫
        mapCochainComplexPlusSinglePlusIso
          (etaleModuleInverseImage.{u, 0} Λ
            (pullback.fst j.toBase (specAlgebraMap k kbar)))
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))).symm ≪≫
    @asIso _ _ _ _ (DerivedCategory.Plus.Q.map
      (compactSupportResolutionRestrictionMap (kbar := kbar) F I))
      (isIso_Q_map_compactSupportResolutionRestrictionMap (kbar := kbar) F I)

omit [Algebra.IsSeparable k kbar] in
/-- `compactSupportResolutionSingleIso` is the localization of the augmentation
`compactSupportResolutionAugmentation`. -/
lemma compactSupportResolutionSingleIso_hom (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (compactSupportResolutionSingleIso kbar F I).hom =
      DerivedCategory.Plus.Q.map (compactSupportResolutionAugmentation kbar F I) :=
  (DerivedCategory.Plus.Q.map_comp _ _).symm

/-- **`res_ℤ((j_! F)|_{X̄_k̄})[0] ≅ res_ℤ(I|_{X̄_k̄})` in `D⁺`**:
`compactSupportResolutionSingleIso` transported along the exact `res_ℤ`. -/
def compactSupportResolutionIntSingleIso (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ)
            (pullback j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) ≅
      DerivedCategory.Plus.Q.obj ((etaleModuleRestrictScalars (Int.castRingHom Λ)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              I.cocomplexPlus)) :=
  ((etaleModuleRestrictScalars (Int.castRingHom Λ)
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapDerivedCategoryPlusObjSingleIso
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))).symm ≪≫
    (etaleModuleRestrictScalars (Int.castRingHom Λ)
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapDerivedCategoryPlus.mapIso
      (compactSupportResolutionSingleIso kbar F I) ≪≫
    (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars (Int.castRingHom Λ)
      (fieldBaseChange (Over.mk j.toBase) kbar))).app
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
            I.cocomplexPlus)

omit [Algebra.IsSeparable k kbar] in
/-- `compactSupportResolutionIntSingleIso` is the localization of the augmentation
`compactSupportResolutionIntAugmentation`. -/
lemma compactSupportResolutionIntSingleIso_hom (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) :
    (compactSupportResolutionIntSingleIso kbar F I).hom =
      DerivedCategory.Plus.Q.map (compactSupportResolutionIntAugmentation kbar F I) :=
  Functor.mapDerivedCategoryPlusObjSingleIso_symm_trans_mapIso_trans_hom _ _ _ _
    (compactSupportResolutionSingleIso_hom kbar F I)

/-- **The resolution model of `Hᵐ_c(X_k̄, F)` read over `ℤ`**: through
`res_ℤ Hᵐ(X̄_k̄, -) ≅ Hᵐ(X̄_k̄, res_ℤ -)`, the identification `Hᵐ(Γ(X̄_k̄, I|)) ≅ Hᵐ_c(X_k̄, F)` is
`res_ℤ Hᵐ(Γ(X̄_k̄, I|)) ≅ Hᵐ(Γ_ℤ(X̄_k̄, res_ℤ I|))` followed by the computation of
`Hᵐ(X̄_k̄, res_ℤ (j_! F)|)` on the acyclic resolution `res_ℤ I|`. -/
theorem
    restrictScalars_galoisCompactSupportResolutionIso_trans_rightDerivedPlusRestrictScalarsIntIso
    (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (m : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map
        ((galoisCompactSupportResolutionIso (f := f) kbar F I m ≪≫
          galoisCompactSupportSingleIso f j kbar Λ F m).hom) ≫
      (rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) m).hom =
      (Stacks.DerivedFunctor.complexHomologyIso
          (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) (ComplexShape.up ℤ) m).inv.app
          (((etaleModuleGlobalSections.{u, 0} Λ
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              (((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
                  I.cocomplex)) ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
          (etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ)
            (fieldBaseChange (Over.mk j.toBase) kbar)).hom (ComplexShape.up ℤ)).app
              (((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
                  I.cocomplex)) m ≫
        ((etaleModuleGlobalSections.{u, 0} ℤ
          (fieldBaseChange (Over.mk j.toBase) kbar)).homologyIsoRightDerivedPlusOfResolution
          ((etaleModuleRestrictScalars (Int.castRingHom Λ)
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, 0} Λ
                (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
                  I.cocomplexPlus))
          (rightAcyclic_restrictScalarsInt_compactSupportResolutionRestriction kbar F I)
          (compactSupportResolutionIntSingleIso kbar F I) m).hom := by
  rw [galoisCompactSupportResolutionIso_trans_singleIso_hom,
    rightDerivedPlusRestrictScalarsIntIso_eq]
  exact Functor.rightDerivedPlusRestrictionIso_resolution _ _ _ _ _ _ _
    (rightAcyclic_compactSupportResolutionRestriction F I) _ _ m

/-- The chase computing a class through `res_ℤ(r ≫ s) ≫ t = a ≫ b ≫ c`, on abstract morphisms. -/
private lemma resolution_class_chase {R : Type} [Ring R] {M₀ M N : ModuleCat.{u + 1} R}
    {P B C : ModuleCat.{u + 1} ℤ} (r : M₀ ≅ M) (s : M ≅ N)
    (t : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R)).obj N ≅ P)
    (a : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R)).obj M₀ ⟶ B) (b : B ⟶ C)
    (c : C ⟶ P)
    (h : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R)).map (r ≪≫ s).hom ≫ t.hom =
      a ≫ b ≫ c) {x : M₀} {y : C} (hx : (a ≫ b).hom x = y) :
    t.hom.hom (s.hom.hom (r.hom.hom x)) = c.hom y := by
  rw [← hx]
  exact ConcreteCategory.congr_hom h x

/-- The chase moving a class through `g ≫ m' = m ≫ θ`, on abstract morphisms. -/
private lemma resolution_class_naturality_chase {R : Type} [Ring R] {M₀ M N : ModuleCat.{u + 1} R}
    {P P' B C C' : ModuleCat.{u + 1} ℤ} (r : M₀ ≅ M) (s : M ≅ N)
    (t : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R)).obj N ≅ P)
    (a : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R)).obj M₀ ⟶ B) (b : B ⟶ C)
    (m : C ⟶ P) (g : C ⟶ C') (m' : C' ⟶ P') (θ : P ⟶ P') (q : B ⟶ C')
    (h₁ : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R)).map (r ≪≫ s).hom ≫ t.hom =
      a ≫ b ≫ m) (h₂ : g ≫ m' = m ≫ θ) (h₃ : q = b ≫ g) {x : M₀} {y : C'}
    (hx : (a ≫ q).hom x = y) :
    θ.hom (t.hom.hom (s.hom.hom (r.hom.hom x))) = m'.hom y := by
  rw [← hx, h₃]
  have e := ConcreteCategory.congr_hom h₁ x
  have e' := ConcreteCategory.congr_hom h₂ (b.hom (a.hom x))
  exact (congrArg θ.hom e).trans e'.symm

/-- Two classes with the same image under `res_ℤ s ≫ t` agree. -/
private lemma eq_of_restrictScalars_iso_chase {R : Type} [Ring R] {M N : ModuleCat.{u + 1} R}
    {P : ModuleCat.{u + 1} ℤ} (s : M ≅ N)
    (t : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R)).obj N ≅ P) {x y : M}
    (h : t.hom.hom (s.hom.hom x) = t.hom.hom (s.hom.hom y)) : x = y :=
  s.toLinearEquiv.injective (t.toLinearEquiv.injective h)

/-- **`Hᵐ_c(X_k̄, -)` of a morphism of restricted resolutions over `ℤ`.** Let `I`, `K₀` be
injective resolutions of `j_! F` (over `Λ`) and `j_! G` (over `R`, with `ℤ → R` surjective), and
`g : res_ℤ(I|_{X̄_k̄}) ⟶ res_ℤ(K₀|_{X̄_k̄})` a morphism of complexes of abelian sheaves lying over
`θ : res_ℤ((j_! F)|) ⟶ res_ℤ((j_! G)|)`. For cocycles `x` of `Γ(X̄_k̄, I|)` and `z` of
`Γ(X̄_k̄, K₀|)` with `z = g(x)` on sections, the class of `z` in `H²_c(X_k̄, G)` is the image of
the class of `x` under the map induced by `θ`
(`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar` of the `R`-linear lift of
`θ`). -/
theorem galoisCompactSupportResolutionIso_homologyπ_eq_restrictScalarsMapOfBar {R : Type} [Ring R]
    (ψ : R →+* Λ) (hR : Function.Surjective (Int.castRingHom R)) (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)))
    (K₀ : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)))
    (θ : (etaleModuleRestrictScalars (Int.castRingHom Λ)
          (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom R)
          (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)))
    (g : (etaleModuleRestrictScalars (Int.castRingHom Λ)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              I.cocomplexPlus) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom R)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              K₀.cocomplexPlus))
    (hg : compactSupportResolutionIntAugmentation kbar F I ≫ g =
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map θ ≫
        compactSupportResolutionIntAugmentation kbar G K₀)
    (x : (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              I.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (z : (((etaleModuleGlobalSections.{u, 0} R
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)).cycles ((2 : ℕ) : ℤ))
    (hxz : ((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom R)
        (fieldBaseChange (Over.mk j.toBase) kbar)).hom.app
          ((((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex).X ((2 : ℕ) : ℤ))).hom
          ((HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} R
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) ((2 : ℕ) : ℤ)).hom z) =
      ((etaleModuleGlobalSections.{u, 0} ℤ (fieldBaseChange (Over.mk j.toBase) kbar)).map
          (g.hom.f ((2 : ℕ) : ℤ))).hom
        (((etaleModuleGlobalSectionsRestrictScalars (Int.castRingHom Λ)
          (fieldBaseChange (Over.mk j.toBase) kbar)).hom.app
            ((((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
                I.cocomplex).X ((2 : ℕ) : ℤ))).hom
          ((HomologicalComplex.iCycles (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              I.cocomplex)) ((2 : ℕ) : ℤ)).hom x))) :
    (galoisCompactSupportResolutionIso (f := f) kbar G K₀ ((2 : ℕ) : ℤ)).hom.hom
        ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} R
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) ((2 : ℕ) : ℤ)).hom z) =
      galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G
        (restrictScalarsIntLift ψ _ hR θ)
        ((galoisCompactSupportResolutionIso (f := f) kbar F I ((2 : ℕ) : ℤ)).hom.hom
          ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              I.cocomplex)) ((2 : ℕ) : ℤ)).hom x)) := by
  have E1F :=
    restrictScalars_galoisCompactSupportResolutionIso_trans_rightDerivedPlusRestrictScalarsIntIso
      kbar F I ((2 : ℕ) : ℤ)
  have E1G :=
    restrictScalars_galoisCompactSupportResolutionIso_trans_rightDerivedPlusRestrictScalarsIntIso
      kbar G K₀ ((2 : ℕ) : ℤ)
  have L2 := Functor.homologyIsoRightDerivedPlusOfResolution_hom_naturality
    (etaleModuleGlobalSections.{u, 0} ℤ (fieldBaseChange (Over.mk j.toBase) kbar)) θ g
    (rightAcyclic_restrictScalarsInt_compactSupportResolutionRestriction kbar F I)
    (rightAcyclic_restrictScalarsInt_compactSupportResolutionRestriction kbar G K₀)
    (compactSupportResolutionIntSingleIso kbar F I) (compactSupportResolutionIntSingleIso kbar G K₀)
    (by
      rw [compactSupportResolutionIntSingleIso_hom, compactSupportResolutionIntSingleIso_hom]
      exact ((DerivedCategory.Plus.Q.map_comp _ _).symm.trans
        (congrArg DerivedCategory.Plus.Q.map hg)).trans (DerivedCategory.Plus.Q.map_comp _ _))
    ((2 : ℕ) : ℤ)
  let φF := (NatTrans.mapHomologicalComplex (etaleModuleGlobalSectionsRestrictScalars
    (Int.castRingHom Λ) (fieldBaseChange (Over.mk j.toBase) kbar)).hom (ComplexShape.up ℤ)).app
      (((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj I.cocomplex)
  let φG := (NatTrans.mapHomologicalComplex (etaleModuleGlobalSectionsRestrictScalars
    (Int.castRingHom R) (fieldBaseChange (Over.mk j.toBase) kbar)).hom (ComplexShape.up ℤ)).app
      (((etaleModuleInverseImage.{u, 0} R
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj K₀.cocomplex)
  let z' := (HomologicalComplex.cyclesMap φG ((2 : ℕ) : ℤ)).hom
    (((HomologicalComplex.sc (((etaleModuleGlobalSections.{u, 0} R
    (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
      (((etaleModuleInverseImage.{u, 0} R
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj K₀.cocomplex))
          ((2 : ℕ) : ℤ)).mapCyclesIso
      (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom R))).inv.hom z)
  have hz' := iCycles_cyclesMap_mapCyclesIso_inv _ _ φG ((2 : ℕ) : ℤ) z
  have elG := complexHomologyIso_inv_app_homologyMap_homologyπ _ _ φG ((2 : ℕ) : ℤ) z z' hz'
  let ψF := φF ≫ ((etaleModuleGlobalSections.{u, 0} ℤ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).map g.hom
  have h2 : (HomologicalComplex.iCycles (((etaleModuleRestrictScalars (Int.castRingHom R)
        (fieldBaseChange (Over.mk j.toBase) kbar) ⋙
      etaleModuleGlobalSections.{u, 0} ℤ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
      (((etaleModuleInverseImage.{u, 0} R
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj K₀.cocomplex))
          ((2 : ℕ) : ℤ)).hom z' =
      (ψF.f ((2 : ℕ) : ℤ)).hom ((HomologicalComplex.iCycles
        (((etaleModuleGlobalSections.{u, 0} Λ
    (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
      (((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj I.cocomplex))
          ((2 : ℕ) : ℤ)).hom x) := by
    rw [hz']
    dsimp only [ψF, φF, φG, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hxz
  have elF := complexHomologyIso_inv_app_homologyMap_homologyπ _ _ ψF ((2 : ℕ) : ℤ) x z' h2
  let modelF := (etaleModuleGlobalSections.{u, 0} ℤ
    (fieldBaseChange (Over.mk j.toBase) kbar)).homologyIsoRightDerivedPlusOfResolution
      ((etaleModuleRestrictScalars (Int.castRingHom Λ)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              I.cocomplexPlus))
      (rightAcyclic_restrictScalarsInt_compactSupportResolutionRestriction kbar F I)
      (compactSupportResolutionIntSingleIso kbar F I) ((2 : ℕ) : ℤ)
  let modelG := (etaleModuleGlobalSections.{u, 0} ℤ
    (fieldBaseChange (Over.mk j.toBase) kbar)).homologyIsoRightDerivedPlusOfResolution
      ((etaleModuleRestrictScalars (Int.castRingHom R)
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              K₀.cocomplexPlus))
      (rightAcyclic_restrictScalarsInt_compactSupportResolutionRestriction kbar G K₀)
      (compactSupportResolutionIntSingleIso kbar G K₀) ((2 : ℕ) : ℤ)
  let cF := (Stacks.DerivedFunctor.complexHomologyIso
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) (ComplexShape.up ℤ)
      ((2 : ℕ) : ℤ)).inv.app (((etaleModuleGlobalSections.{u, 0} Λ
    (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
      (((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj I.cocomplex))
  let R2θ := ((etaleModuleGlobalSections.{u, 0} ℤ
    (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedPlus ((2 : ℕ) : ℤ)).map θ
  let Hg := HomologicalComplex.homologyMap (((etaleModuleGlobalSections.{u, 0} ℤ
    (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).map g.hom) ((2 : ℕ) : ℤ)
  have key1 := resolution_class_chase _ _ _ _ _ _ E1G elG
  have key2 := (galoisCompactSupportRestrictScalarsMapOfBar_int_lift f j kbar ψ hR F G θ
    ((galoisCompactSupportResolutionIso (f := f) kbar F I ((2 : ℕ) : ℤ)).hom.hom
      ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} Λ
    (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
      (((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj I.cocomplex))
          ((2 : ℕ) : ℤ)).hom x))).trans
    (resolution_class_naturality_chase _ _ _ _ _ _ _ _ _ _ E1F L2
      (HomologicalComplex.homologyMap_comp _ _ _) elF)
  have key3 : (rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
      ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) ((2 : ℕ) : ℤ)).hom.hom
        ((galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).hom.hom
          ((galoisCompactSupportResolutionIso (f := f) kbar G K₀ ((2 : ℕ) : ℤ)).hom.hom
            ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} R
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              K₀.cocomplex)) ((2 : ℕ) : ℤ)).hom z))) =
      (rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
      ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) ((2 : ℕ) : ℤ)).hom.hom
        ((galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ)).hom.hom
          (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G
            (restrictScalarsIntLift ψ _ hR θ)
            ((galoisCompactSupportResolutionIso (f := f) kbar F I ((2 : ℕ) : ℤ)).hom.hom
              ((HomologicalComplex.homologyπ (((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              I.cocomplex)) ((2 : ℕ) : ℤ)).hom x)))) :=
    key1.trans key2.symm
  refine eq_of_restrictScalars_iso_chase (galoisCompactSupportSingleIso f j kbar R G ((2 : ℕ) : ℤ))
    (rightDerivedPlusRestrictScalarsIntIso (pullback j.toBase (specAlgebraMap k kbar))
      ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) ((2 : ℕ) : ℤ)) ?_
  exact key3

end Model

end Stacks.EtaleCohomology

end
