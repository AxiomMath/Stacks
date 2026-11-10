module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleBaseChangeComparison

/-!
# The base change map at the structure sheaf along an affine morphism

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of algebraic spaces with `g` and `g'` affine.  The base change map of the
transposed square, `Lf^*Rg_*𝒪_{Y'} ⟶ Rg'_*L(f')^*𝒪_{Y'}`, is computed by the underived base
change map `f^*g_*𝒪_{Y'} ⟶ g'_*(f')^*𝒪_{Y'}`: the derived direct images along the affine
morphisms are computed by the underived ones on quasi-coherent modules placed in degree `0`, and
`L(f')^*𝒪_{Y'} = (f')^*𝒪_{Y'}` because `𝒪_{Y'}` is flat.  The one remaining derived pullback,
`Lf^*(g_*𝒪_{Y'})`, is computed by `f^*` exactly when `X` and `Y'` are Tor independent over `Y`,
which is the input of the proof of Stacks 08IR.

## Main results

* `AlgebraicGeometry.Space.isIso_transposeBaseChangeMap_structure_of_isIso`: the transposed
  base change map at `𝒪_{Y'}` is invertible as soon as `Lf^*(g_*𝒪_{Y'}) ⟶ f^*g_*𝒪_{Y'}` and the
  underived base change map at `𝒪_{Y'}` are.

## References

* [Stacks Project, Tag 08IR](https://stacks.math.columbia.edu/tag/08IR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy
  sourceQuasiIso)

namespace Stacks.CategoryTheory.BaseChange

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc Lc' : A ⥤ B'}

/-- The base change map only depends on the comparison `eg.hom ≫ ef.inv`: an isomorphism
composed onto the identification of one composite may be moved onto the other. -/
theorem map_trans_left (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc)
    (ef : Lf ⋙ Lg' ≅ Lc') (τ : Lc ≅ Lc') (K : B) :
    map adjf adjf' (eg ≪≫ τ) ef K = map adjf adjf' eg (ef ≪≫ τ.symm) K := by
  simp only [map, twoSquare, pullbackComparison, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
    Category.assoc]

/-- A transport of the identification of one composite along an equality in a family of functors
may be moved, reversed, onto the identification of the other composite. -/
theorem isIso_map_eqToIso_left {T : Sort*} (Λ : T → (A ⥤ B')) {t₁ t₂ : T} (h : t₁ = t₂)
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Λ t₂) (ef : Lf ⋙ Lg' ≅ Λ t₁) (K : B)
    (hK : IsIso (map adjf adjf' eg (ef ≪≫ eqToIso (congrArg Λ h)) K)) :
    IsIso (map adjf adjf' (eg ≪≫ eqToIso (congrArg Λ h.symm)) ef K) := by
  subst h
  simpa using hK

end Stacks.CategoryTheory.BaseChange

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The second factor of a fourfold composite is invertible when the composite and the three
other factors are. -/
private theorem isIso_of_isIso_comp₄ {C : Type*} [Category C] {P Q R T V : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ T) (d : T ⟶ V) (ha : IsIso a) (hc : IsIso c) (hd : IsIso d)
    (h : IsIso (a ≫ b ≫ c ≫ d)) : IsIso b := by
  have h₁ : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a _
  have h₂ : IsIso ((b ≫ c) ≫ d) := by rw [Category.assoc]; exact h₁
  have h₃ : IsIso (b ≫ c) := IsIso.of_isIso_comp_right (b ≫ c) d
  exact IsIso.of_isIso_comp_right b c

/-- A component of a natural transformation is invertible when its composite with `eqToHom` of
an equality of functors is. -/
theorem isIso_app_of_isIso_eqToHom_comp_app {C D : Type*} [Category C] [Category D]
    {F F' G : C ⥤ D} (h : F = F') (α : F' ⟶ G) (X : C) (hh : IsIso ((eqToHom h ≫ α).app X)) :
    IsIso (α.app X) := by
  subst h
  simpa using hh

/-- The unit of a right derived functor of the direct image at `M[0]` is invertible as soon as
the canonical map `(g_*M)[0] ⟶ RF(M[0])` built from it is. -/
theorem isIso_app_single_of_isIso_modulePushforwardSingleToRightDerived
    (RF : DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF) (M : Modules.{u, u} B S hS Y'.1 Y'.2)
    (h : IsIso ((modulePushforwardSingleToRightDerived B S hS g RF α).app M)) :
    IsIso (α.app ((HomotopyCategory.singleFunctor _ 0).obj M)) := by
  rw [modulePushforwardSingleToRightDerived] at h
  exact isIso_of_isIso_comp₄ _ _ _ _ inferInstance inferInstance inferInstance h

/-- The unit `(g_*M)[0] ⟶ Rg_*(M[0])` of the derived direct image is invertible for an affine
morphism `g` and a quasi-coherent module `M`, read on the homotopy category. -/
theorem isIso_derivedModulePushforwardUnit_app_single_of_isAffineHom
    (hg : IsAffineHom B S hS g.hom) (M : Modules.{u, u} B S hS Y'.1 Y'.2)
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((derivedModulePushforwardUnit B S hS g).app
      ((HomotopyCategory.singleFunctor _ 0).obj M)) :=
  isIso_app_single_of_isIso_modulePushforwardSingleToRightDerived B S hS g _
    (derivedModulePushforwardUnit B S hS g) M
    (isIso_modulePushforwardSingleToDerived_app_of_isAffineHom B S hS g hg M hM)

/-- The structure sheaf of `Y'` placed in degree `0` of the homotopy category. -/
abbrev structureHomotopy (Y' : AlgebraicSpaces B S hS) :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'))
      (ComplexShape.up ℤ) :=
  (HomotopyCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y'))

/-- The degree-`0` complex of a flat module is K-flat for the derived pullback. -/
theorem smallEtaleModuleKFlat_structureHomotopy (Y' : AlgebraicSpaces B S hS) :
    smallEtaleModuleKFlat B S hS Y' (structureHomotopy B S hS Y') := by
  refine @smallEtaleModuleKFlat_of_isStrictlyLE B S hS Y'
    ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y'))) 0 inferInstance
    (fun i => ?_)
  by_cases h : i = 0
  · subst h
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      (HomologicalComplex.singleObjXSelf _ _ _).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
        (Y := smallEtaleRingedSite B S hS Y'.1 Y'.2))
  · exact isFlat_of_isZero B S hS (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

/-- The unit of `AlgebraicGeometry.Space.derivedModulePushforward` is the unit of the total right
derived direct image, read through the identification of the two spellings of the direct image. -/
theorem derivedModulePushforwardUnit_eq_totalRightDerivedUnit :
    derivedModulePushforwardUnit B S hS g =
      eqToHom (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS g) ≫
    (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS Y')
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS g)).totalRightDerivedUnit
        DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS Y')) := rfl

/-- The unit of the total right derived direct image along an affine morphism is invertible at
the degree-`0` complex of a quasi-coherent module. -/
private theorem isIso_totalRightDerivedUnit_app_single (hg : IsAffineHom B S hS g.hom)
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) (hM : M.IsQuasicoherentOnSite) :
    IsIso (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS Y')
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS g)).totalRightDerivedUnit
        DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS Y'))).app
          ((HomotopyCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj M)) := by
  have h := isIso_derivedModulePushforwardUnit_app_single_of_isAffineHom B S hS g hg M hM
  rw [derivedModulePushforwardUnit_eq_totalRightDerivedUnit] at h
  have h' := isIso_app_of_isIso_eqToHom_comp_app _ _ _ h
  exact @isIso_app_of_iso_of_isIso_app _ _ _ _ _ _ _ _ _ (Iso.refl _) h'

/-- For an affine morphism `g : Y' ⟶ Y`, the unit `g_*𝒪_{Y'} ⟶ Rg_*𝒪_{Y'}` of the total right
derived direct image is invertible at `𝒪_{Y'}[0]`. -/
theorem isIso_totalRightDerivedUnit_app_structureHomotopy (hg : IsAffineHom B S hS g.hom) :
    IsIso (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS Y')
      (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS g)).totalRightDerivedUnit
        DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS Y'))).app
          (structureHomotopy B S hS Y')) := by
  exact isIso_totalRightDerivedUnit_app_single B S hS g hg _
    (SheafOfModules.isQuasicoherentOnSite_unit _)

/-- The base change map of the transposed square at `𝒪_{Y'}[0]`, read on the homotopy category,
through the underived one.  For
a commutative square `g' ≫ f = f' ≫ g` with `g` and `g'` affine, the base change map
`Lf^*Rg_*𝒪_{Y'} ⟶ Rg'_*L(f')^*𝒪_{Y'}` is invertible as soon as the comparison
`Lf^*(g_*𝒪_{Y'}) ⟶ f^*(g_*𝒪_{Y'})` (`h₃`) and the underived base change map
`f^*g_*𝒪_{Y'} ⟶ g'_*(f')^*𝒪_{Y'}` (`h₄`) are. -/
theorem isIso_transposeBaseChangeMap_structureHomotopy_of_isIso (w : g' ≫ f = f' ≫ g)
    (hg : IsAffineHom B S hS g.hom) (hg' : IsAffineHom B S hS g'.hom)
    (h₃ : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y'))))
    (h₄ : IsIso (smallEtaleUnderivedBaseChangeMap B S hS g f g' f' w.symm
      (structureHomotopy B S hS Y'))) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS g)
      (smallEtaleDerivedModuleAdjunction B S hS g')
      (smallEtaleDerivedModulePullbackCompIso B S hS g' f)
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g ≪≫
        eqToIso (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) w.symm))
      (DerivedCategory.Qh.obj (structureHomotopy B S hS Y'))) := by
  let uf := (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS Y')
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS g)).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS Y'))
  let uf' := (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X')
    (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS g')).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS X'))
  let O' : Modules.{u, u} B S hS Y'.1 Y'.2 :=
    SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y')
  have hO' : O'.IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
  have h₁ : IsIso (uf.app (structureHomotopy B S hS Y')) :=
    isIso_totalRightDerivedUnit_app_structureHomotopy B S hS g hg
  have h₂ := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f'
    (structureHomotopy B S hS Y') (smallEtaleModuleKFlat_structureHomotopy B S hS Y')
  let F' := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X')
    (Y := smallEtaleRingedTopos B S hS Y') (smallEtaleRingedToposHom B S hS f').toModulesHom
  let P : Modules.{u, u} B S hS X'.1 X'.2 := F'.obj O'
  have hP : P.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((pullbackModulesIsoModulePullback B S hS f').app O').symm
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f' O' hO')
  have h₅ : IsIso (uf'.app ((smallEtalePullbackMapHomotopy B S hS f').obj
      (structureHomotopy B S hS Y'))) := by
    have h' := isIso_totalRightDerivedUnit_app_single B S hS g' hg' P hP
    let e : (smallEtalePullbackMapHomotopy B S hS f').obj (structureHomotopy B S hS Y') ≅
        (HomotopyCategory.singleFunctor (Modules.{u, u} B S hS X'.1 X'.2) 0).obj P :=
      (HomotopyCategory.quotient _ _).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F' (ComplexShape.up ℤ) 0).app O')
    exact @isIso_app_of_iso_of_isIso_app _ _ _ _ _ _ uf' _ _ e h'
  have h₄' := h₄
  unfold smallEtaleUnderivedBaseChangeMap at h₄'
  rw [smallEtaleUnderivedPullbackSquareIso_eq, smallEtaleUnderivedPullbackCongr] at h₄'
  have key := Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_twoSquare_eq
    (smallEtaleMapHomotopyAdjunction B S hS g) (smallEtaleMapHomotopyAdjunction B S hS g')
    (smallEtaleDerivedModuleAdjunction B S hS g) (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModulePullbackComparison B S hS g)
    (smallEtaleDerivedModulePullbackComparison B S hS g')
    (smallEtaleDerivedModulePullbackComparison B S hS f)
    (smallEtaleDerivedModulePullbackComparison B S hS f') uf uf'
    (fun f ↦ smallEtaleDerivedModulePullback B S hS f) (smallEtalePullbackMapHomotopy B S hS)
    (fun f ↦ smallEtaleDerivedModulePullbackComparison B S hS f) w.symm
    (smallEtaleDerivedModulePullbackCompIso B S hS g' f)
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleUnderivedPullbackCompIso B S hS g' f)
    (smallEtaleUnderivedPullbackCompIso B S hS f' g)
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS g)
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS g')
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS g' f)
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS f' g)
    (structureHomotopy B S hS Y') h₁ h₂ h₃ h₄' h₅
  exact key

/-- **The base change map of the transposed square at `𝒪_{Y'}` through the underived one.**  For
a commutative square `g' ≫ f = f' ≫ g` with `g` and `g'` affine, the base change map
`Lf^*Rg_*𝒪_{Y'} ⟶ Rg'_*L(f')^*𝒪_{Y'}` is invertible as soon as the comparison
`Lf^*(g_*𝒪_{Y'}) ⟶ f^*(g_*𝒪_{Y'})` (`h₃`) and the underived base change map
`f^*g_*𝒪_{Y'} ⟶ g'_*(f')^*𝒪_{Y'}` (`h₄`) are. -/
theorem isIso_transposeBaseChangeMap_structure_of_isIso (w : g' ≫ f = f' ≫ g)
    (hg : IsAffineHom B S hS g.hom) (hg' : IsAffineHom B S hS g'.hom)
    (h₃ : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y'))))
    (h₄ : IsIso (smallEtaleUnderivedBaseChangeMap B S hS g f g' f' w.symm
      (structureHomotopy B S hS Y'))) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS g)
      (smallEtaleDerivedModuleAdjunction B S hS g')
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w)
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g) (structureDerived Y')) := by
  have key := Stacks.CategoryTheory.BaseChange.isIso_map_eqToIso_left
    (fun f ↦ smallEtaleDerivedModulePullback B S hS f) w.symm _ _ _ _ _
    (isIso_transposeBaseChangeMap_structureHomotopy_of_isIso B S hS f g f' g' w hg hg' h₃ h₄)
  have e : smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w =
      smallEtaleDerivedModulePullbackCompIso B S hS g' f ≪≫
        eqToIso (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f) w.symm.symm) := rfl
  rw [e]
  exact (@Stacks.CategoryTheory.BaseChange.isIso_map_iff_of_iso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ ((DerivedCategory.singleFunctorIsoCompQh _ 0).app
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y'))).symm).1 key

/-- The underived base change map of a commutative square at `𝒪_{Y'}[0]` is invertible as soon
as the base change map of modules of Stacks 03LU is invertible at `𝒪_{Y'}`. -/
theorem isIso_smallEtaleUnderivedBaseChangeMap_structureHomotopy (w : g' ≫ f = f' ≫ g)
    (h : IsIso ((moduleBaseChangeMap f g f' g' w).app
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))) :
    IsIso (smallEtaleUnderivedBaseChangeMap B S hS f g f' g' w (structureHomotopy B S hS X)) := by
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS f' g)
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g' f)
  have hK := Stacks.CategoryTheory.BaseChange.isIso_map_mapHomotopyCategory_quotient_obj
    (fun k : X' ⟶ Y => Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS k).toModulesHom) w
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y') (smallEtaleRingedToposHom B S hS f'))
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f')
        (smallEtaleRingedToposHom B S hS g)).symm (pullbackModulesCompTransport B S hS f' g)
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g')
        (smallEtaleRingedToposHom B S hS f)).symm (pullbackModulesCompTransport B S hS g' f)
    ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) (fun n => by
        by_cases hn : n = 0
        · subst hn
          have h' := isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap_app
            B S hS f g f' g' w _ h
          exact (@Stacks.CategoryTheory.BaseChange.isIso_map_iff_of_iso _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ (HomologicalComplex.singleObjXSelf _ _ _).symm).1 h'
        · exact Stacks.CategoryTheory.BaseChange.isIso_map_of_isZero _ _ _ _
            (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn))
  exact (@Stacks.CategoryTheory.BaseChange.isIso_map_iff_of_iso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ ((HomotopyCategory.singleFunctorPostcompQuotientIso _ 0).app _).symm).1 hK

end AlgebraicGeometry.Space

end
