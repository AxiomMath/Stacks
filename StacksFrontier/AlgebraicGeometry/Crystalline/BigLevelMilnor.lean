module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelLimit

/-!
# The Milnor triangle of `RΓ(CRIS(X/S), N)` over the finite levels

For a global crystalline situation with affine base `S`, `A = Γ(S, 𝒪_S)`, a sequence of levels
`e(n)` and a module `N` on `CRIS(X/S)`, this file proves the content of [Stacks, Remark 07MV] at
module coefficients: `RΓ(CRIS(X/S), N)` sits in a distinguished triangle in `D(Mod_A)`
`RΓ(CRIS(X/S), N) ⟶ ∏ₙ RΓ(CRIS(X/S_{e(n)}), N_{e(n)}) ⟶ ∏ₙ RΓ(CRIS(X/S_{e(n)}), N_{e(n)}) ⟶`
whose maps are the derived comparisons of global sections along `S_{e(n)} ⟶ S` and along
`S_{e(n)} ⟶ S_{e(n+1)}`.  The computations on an injective resolution are in
`StacksFrontier/AlgebraicGeometry/Crystalline/BigLevelLimit.lean`; here they are assembled with the
Milnor triangle of the limit of the tower of complexes of global sections.

## Main results

* `GlobalCrystallineSituation.levelDerivedTransition_comp_levelResolutionQIso` — the transitions
  of the levels are the localized transitions of the tower of complexes.
* `GlobalCrystallineSituation.exists_distTriang_levelDerived` — **the Milnor triangle.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite

universe wB wA u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] (hN : S.LevelSequence)
  [HasDerivedCategory.{wB} (SmallSite.BigModuleSheaf S)]
  [∀ n, HasDerivedCategory.{wB} (SmallSite.BigModuleSheaf (S.levelSituation (hN.isLevel n)))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [∀ n, HasDerivedCategory.{wA}
    (ModuleCat.{u + 1} Γ((S.levelSituation (hN.isLevel n)).S.scheme, ⊤))]

section Resolution

variable {N : SmallSite.BigModuleSheaf S}
  (R : CochainComplex.InjectiveResolution
    ((CochainComplex.singleFunctor (SmallSite.BigModuleSheaf S) 0).obj N))

set_option maxHeartbeats 1600000 in
/-- **The transition of the restricted resolutions, localized, is the localized transition of
global sections applied to the resolution**: the three pieces (comparison along
`S_{e(n)} ⟶ S_{e(n+1)}`, composition of restrictions of scalars, identification of the two
restrictions of the resolution) assemble to `levelSectionsTransition`. -/
theorem levelResolutionTransition_square (n : ℕ) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlus (ModuleCat.restrictScalars.{u + 1}
            (SmallSite.baseChangeRingHom (S.levelProj (hN.isLevel (n + 1)))))).map
          ((Functor.mapHomotopyCategoryPlusNatTrans (changeBaseBigBaseGlobalSectionsTrans
            (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)) (𝟙 S.X)
            (S.levelTransition_condition (hN.isLevel n) (hN.isLevel (n + 1))
              (hN.le_succ n)))).app
            ((S.levelPullback (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.obj
              ((HomotopyCategory.Plus.quotient _).obj ⟨R.cocomplex, R.boundedBelow⟩))) ≫
          (Functor.mapHomotopyCategoryPlusNatTrans
            (S.levelRestrictScalarsComp (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))).app
            ((SmallSite.bigBaseModuleGlobalSections
              (S.levelSituation (hN.isLevel n))).mapHomotopyCategoryPlus.obj
              ((S.levelStepPullback (hN.isLevel n) (hN.isLevel (n + 1))
                (hN.le_succ n)).mapHomotopyCategoryPlus.obj
                ((S.levelPullback (hN.isLevel (n + 1))).mapHomotopyCategoryPlus.obj
                  ((HomotopyCategory.Plus.quotient _).obj ⟨R.cocomplex, R.boundedBelow⟩)))) ≫
          (ModuleCat.restrictScalars.{u + 1}
            (SmallSite.baseChangeRingHom (S.levelProj (hN.isLevel n)))).mapHomotopyCategoryPlus.map
            ((SmallSite.bigBaseModuleGlobalSections
              (S.levelSituation (hN.isLevel n))).mapHomotopyCategoryPlus.map
              (S.levelStepResolutionHom hN R n)))) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        ((((S.levelPullback (hN.isLevel n)) ⋙
          (SmallSite.bigBaseModuleGlobalSections (S.levelSituation (hN.isLevel n))) ⋙
          (ModuleCat.restrictScalars.{u + 1}
            (SmallSite.baseChangeRingHom (S.levelProj (hN.isLevel n))))).mapHomologicalComplex
              _).obj R.cocomplex) =
    (DerivedCategory.quotientCompQhIso _).hom.app
        ((((S.levelPullback (hN.isLevel (n + 1))) ⋙
          (SmallSite.bigBaseModuleGlobalSections (S.levelSituation (hN.isLevel (n + 1)))) ⋙
          (ModuleCat.restrictScalars.{u + 1}
            (SmallSite.baseChangeRingHom (S.levelProj (hN.isLevel (n + 1)))))).mapHomologicalComplex
              _).obj R.cocomplex) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (S.levelPullback (hN.isLevel (n + 1)))
          (Functor.whiskerRight (changeBaseBigBaseGlobalSectionsTrans
            (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)) (𝟙 S.X)
            (S.levelTransition_condition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)))
            (ModuleCat.restrictScalars.{u + 1}
              (SmallSite.baseChangeRingHom (S.levelProj (hN.isLevel (n + 1)))))) ≫
          Functor.whiskerRight
            (S.levelPullbackCompIso (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)).hom
            ((SmallSite.bigBaseModuleGlobalSections (S.levelSituation (hN.isLevel n))) ⋙
              (ModuleCat.restrictScalars.{u + 1} (SmallSite.baseChangeRingHom
                (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)))) ⋙
              (ModuleCat.restrictScalars.{u + 1}
                (SmallSite.baseChangeRingHom (S.levelProj (hN.isLevel (n + 1)))))) ≫
          Functor.whiskerLeft ((S.levelPullback (hN.isLevel n)) ⋙
              (SmallSite.bigBaseModuleGlobalSections (S.levelSituation (hN.isLevel n))))
            (S.levelRestrictScalarsComp (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)))
        _).app R.cocomplex) :=
  ι_map_Qh_map_transition_comp (changeBaseBigBaseGlobalSectionsTrans
      (S.levelTransition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)) (𝟙 S.X)
      (S.levelTransition_condition (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)))
    (S.levelPullbackCompIso (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))
    (S.levelRestrictScalarsComp (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n))
    R.cocomplex R.boundedBelow (S.levelStepResolutionHom hN R n) rfl

set_option maxHeartbeats 1600000 in
/-- The transition of the levels is, in `D(Mod_A)`, the transition of global sections applied to
the resolution. -/
theorem levelDerivedTransition_comp_levelResolutionQIso_app (n : ℕ) :
    DerivedCategory.Plus.ι.map (S.levelDerivedTransition hN n N) ≫
        (S.levelResolutionQIso hN R n).hom =
      (S.levelResolutionQIso hN R (n + 1)).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (S.levelSectionsTransition
          (hN.isLevel n) (hN.isLevel (n + 1)) (hN.le_succ n)) _).app R.cocomplex) := by
  dsimp only [levelResolutionQIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  exact map_comp_comp_eq_of_eq DerivedCategory.Plus.ι
    (S.levelDerivedTransition_comp_levelResolutionIso hN R n)
    (S.levelResolutionTransition_square hN R n)


/-- The transition of the levels is, in `D(Mod_A)`, the transition of the tower of complexes. -/
theorem levelDerivedTransition_comp_levelResolutionQIso (n : ℕ) :
    DerivedCategory.Plus.ι.map (S.levelDerivedTransition hN n N) ≫
        (S.levelResolutionQIso hN R n).hom =
      (S.levelResolutionQIso hN R (n + 1)).hom ≫
        DerivedCategory.Q.map ((S.levelSectionsComplexTower hN R).map
          (homOfLE (Nat.le_succ n)).op) := by
  rw [S.levelSectionsComplexTower_map_succ hN R n]
  exact S.levelDerivedTransition_comp_levelResolutionQIso_app hN R n

end Resolution

/-- **Remark 07MV at module coefficients on the big crystalline site: `RΓ(CRIS(X/S), N)` is the
derived limit of the `RΓ(CRIS(X/S_{e(n)}), N_{e(n)})`.**  For an affine base `S` with
`A = Γ(S, 𝒪_S)`, a sequence of levels `e(n)` (`p^{e(n)}`-torsion closed subschemes
`S_{e(n)} = V(p^{e(n)}) ⊂ S`, increasing and unbounded) and a module `N` on `CRIS(X/S)`, the
triangle in `D(Mod_A)`
`RΓ(CRIS(X/S), N) ⟶ ∏ₙ RΓ(CRIS(X/S_{e(n)}), N_{e(n)}) ⟶ ∏ₙ RΓ(CRIS(X/S_{e(n)}), N_{e(n)}) ⟶`
whose first map has components the derived comparisons of global sections along
`S_{e(n)} ⟶ S` and whose second map is `(xₙ) ↦ (xₙ - tₙ(xₙ₊₁))`, with `tₙ` the derived
comparison along `S_{e(n)} ⟶ S_{e(n+1)}`, is distinguished for some third map. -/
theorem exists_distTriang_levelDerived (N : SmallSite.BigModuleSheaf S) :
    letI := hasProductsOfShape_nat_derivedCategory_moduleCat Γ(S.S.scheme, ⊤)
    ∃ δ, Triangle.mk
      (Pi.lift fun n => DerivedCategory.Plus.ι.map (S.levelDerivedProj hN n N))
      (Pi.lift fun n => Pi.π (fun n => DerivedCategory.Plus.ι.obj (S.levelDerived hN n N)) n -
        Pi.π (fun n => DerivedCategory.Plus.ι.obj (S.levelDerived hN n N)) (n + 1) ≫
          DerivedCategory.Plus.ι.map (S.levelDerivedTransition hN n N)) δ ∈
      distTriang (DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))) := by
  have := hasProductsOfShape_nat_derivedCategory_moduleCat Γ(S.S.scheme, ⊤)
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    ((CochainComplex.singleFunctor (SmallSite.BigModuleSheaf S) 0).obj N)
  have h1 := DerivedCategory.exists_distTriang_of_limitCone_of_epi
    (S.levelSectionsComplexTower hN R) _ (S.isLimitLevelSectionsComplexCone hN R)
  exact Pretriangulated.exists_distTriang_milnor_of_iso _ _ _ _ (S.baseResolutionQIso hN R)
    (S.levelResolutionQIso hN R) (S.levelDerivedProj_comp_levelResolutionQIso hN R)
    (S.levelDerivedTransition_comp_levelResolutionQIso hN R) h1


end Crystalline.GlobalCrystallineSituation
