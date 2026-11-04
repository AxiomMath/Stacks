module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.FlatOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankStratumExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The direct image of `E` in the derived category, for Stacks 0D23

Let `f : X ⟶ Y` be flat, proper and of finite presentation and `E` a finite locally free
`𝒪_X`-module. The object `K = Rf_*E` of `D(𝒪_Y)` is perfect and its formation commutes with
every base change `g : Y' ⟶ Y` (cohomology and base change, Stacks 0CTM), so
`Lg^*K ≅ Rf'_*((g')^*E)`. Hence `H^j(Lg^*K) = 0` for `j < 0` and
`H^0(Lg^*K) ≅ f'_*((g')^*E)`. These are the inputs with which the proof of Stacks 0D23 applies
the bottom rank stratum of Stacks 0D21 to `K` in degree `0`.

These are private, unregistered helpers for Stacks 0D23.

## Main definitions

* `AlgebraicGeometry.Space.DescentStratum.pushforwardComplex`: the object `Rf_*E`.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.isPerfect_pushforwardComplex`
* `AlgebraicGeometry.Space.DescentStratum.isZero_pullbackHomology_pushforwardComplex`
* `AlgebraicGeometry.Space.DescentStratum.nonempty_pullbackHomology_pushforwardComplex_zero_iso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.DescentStratum

open BottomRankLocus

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The object `Rf_*E` of `D(𝒪_Y)`**, for an `𝒪_X`-module `E` placed in degree `0`. -/
def pushforwardComplex (f : X ⟶ Y) (E : Modules.{u, u} B S hS X.1 X.2) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  (derivedModulePushforward B S hS f).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj E)

/-- **`Rf_*E` is perfect** for `f` flat, proper and of finite presentation and `E` finite
locally free (Stacks 0CTM). -/
theorem isPerfect_pushforwardComplex (f : X ⟶ Y) (hP : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) (pushforwardComplex f E) :=
  (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hP hfp E
    (isFinitePresentation_modules_of_isFiniteLocallyFree E hE)
    (isFlatOver_of_isFiniteLocallyFree f hfl E hE)).1

/-- **The formation of `Rf_*E` commutes with base change**: `Lg^*Rf_*E ≅ Rf'_*((g')^*E)`
(Stacks 0CTM). -/
theorem nonempty_pullback_pushforwardComplex_iso (f : X ⟶ Y) (hP : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS g).obj (pushforwardComplex f E) ≅
      (derivedModulePushforward B S hS (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (pullback f g))) 0).obj
          ((modulePullback B S hS (pullback.fst f g)).obj E))) := by
  have h := (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hP hfp E
    (isFinitePresentation_modules_of_isFiniteLocallyFree E hE)
    (isFlatOver_of_isFiniteLocallyFree f hfl E hE)).2 g (pullback.snd f g) (pullback.fst f g)
    (IsPullback.of_hasPullback f g)
  have : (modulePullback B S hS (pullback.fst f g)).Additive := modulePullback_additive _
  exact ⟨@asIso _ _ _ _ _ h ≪≫ (derivedModulePushforward B S hS (pullback.snd f g)).mapIso
    (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback B S hS (pullback.fst f g)) (ComplexShape.up ℤ) 0).app E))⟩

/-- **`Lg^*Rf_*E` has no cohomology in negative degrees**: it is `Rf'_*` of a module, and `Rf'_*`
is left t-exact. -/
theorem isZero_pullbackHomology_pushforwardComplex (f : X ⟶ Y) (hP : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (j : ℤ) (hj : j < 0) :
    IsZero (pullbackHomology (pushforwardComplex f E) j g) := by
  obtain ⟨e⟩ := nonempty_pullback_pushforwardComplex_iso f hP hfp hfl E hE g
  have h0 : ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (pullback f g))) 0).obj
          ((modulePullback B S hS (pullback.fst f g)).obj E)).IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact (HomologicalComplex.isZero_single_obj_homology _ _ _ _ (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app _)
  have h := isGE_derivedModulePushforward_obj_of_isGE B S hS (pullback.snd f g)
    ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS (pullback f g))) 0).obj
          ((modulePullback B S hS (pullback.fst f g)).obj E)) 0 h0
  rw [DerivedCategory.isGE_iff] at h
  exact (h j hj).of_iso
    ((DerivedCategory.homologyFunctor _ j).mapIso e)

/-- **`H^0(Lg^*Rf_*E)` is `f'_*((g')^*E)`.** -/
theorem nonempty_pullbackHomology_pushforwardComplex_zero_iso (f : X ⟶ Y)
    (hP : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E)
    {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    Nonempty (pullbackHomology (pushforwardComplex f E) 0 g ≅
      (modulePushforward B S hS (pullback.snd f g)).obj
        ((modulePullback B S hS (pullback.fst f g)).obj E)) := by
  obtain ⟨e⟩ := nonempty_pullback_pushforwardComplex_iso f hP hfp hfl E hE g
  exact ⟨(DerivedCategory.homologyFunctor _ 0).mapIso
      (e ≪≫ (smallEtaleDerivedModulePushforwardIso B S hS (pullback.snd f g)).app _) ≪≫
    homologyDerivedModulePushforwardSingleIso B S hS (pullback.snd f g) _ 0 0 0 (by simp) ≪≫
    (modulePushforward B S hS (pullback.snd f g)).rightDerivedZeroIsoSelf.app _⟩

end AlgebraicGeometry.Space.DescentStratum

end
