module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatLocallyFree

/-!
# The derived pullback of flat complexes and of locally free modules on algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces. A bounded above complex of flat
`𝒪_Y`-modules is K-flat, so the derived pullback `Lf^*` is computed on it by degreewise
pullback. In particular this applies to a finite locally free module placed in one degree, to a
retract of a finite free module placed in one degree, and to a bounded complex of retracts of
finite free modules.

## Main results

* `AlgebraicGeometry.Space.isFlat_of_isFiniteLocallyFreeOfIntRank` and
  `AlgebraicGeometry.Space.isFlat_of_isRetractOfFiniteFree`: finite locally free `𝒪_Y`-modules
  and retracts of finite free ones are flat.
* `AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_obj_Q_iso`: `Lf^*` of a
  bounded above complex of flat modules is its degreewise pullback.
* `AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_obj_singleFunctor_iso`:
  `Lf^*(M[-i]) ≅ (f^*M)[-i]` for a flat module `M`, with the isomorphism
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSingleIsoOfFlat`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackUnitIso`: `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite locally free `𝒪_Y`-module is flat.** -/
theorem isFlat_of_isFiniteLocallyFreeOfIntRank {Y : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) {r : ℤ}
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank M r) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) M :=
  Stacks.SheafOfModules.isFlat_of_isFiniteLocallyFreeOfIntRank
    (Y := smallEtaleRingedSite B S hS Y.1 Y.2) M hM

/-- **A retract of a finite free `𝒪_Y`-module is flat.** -/
theorem isFlat_of_isRetractOfFiniteFree {Y : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hM : IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) M :=
  Stacks.SheafOfModules.isFlat_of_isRetractOfFiniteFree
    (Y := smallEtaleRingedSite B S hS Y.1 Y.2) M hM

/-- A zero `𝒪_Y`-module is flat. -/
theorem isFlat_of_isZero {Y : AlgebraicSpaces B S hS}
    {M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (hM : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) M :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_retract _ (hM.to_ _ : M ⟶ SheafOfModules.unit _)
    (0 : SheafOfModules.unit _ ⟶ M) (hM.eq_of_src _ _)
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
      (Y := smallEtaleRingedSite B S hS Y.1 Y.2))

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Pullback of modules along a morphism of algebraic spaces is additive. -/
instance pullbackModules_smallEtale_additive {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y') :
    ((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules).Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS g)

/-- **The derived pullback of a bounded above complex of flat modules is its degreewise
pullback**, as an isomorphism. -/
def smallEtaleDerivedModulePullbackObjQIso
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (n : ℤ)
    [K.IsStrictlyLE n]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) (K.X i)) :
    (smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.Q).obj K) ≅
      (DerivedCategory.Q).obj
        ((((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f _
    (smallEtaleModuleKFlat_of_isStrictlyLE B S hS Y K n hflat)
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
    asIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((HomotopyCategory.quotient _ _).obj K)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- **The derived pullback of a bounded above complex of flat modules is its degreewise
pullback.** -/
theorem nonempty_smallEtaleDerivedModulePullback_obj_Q_iso
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (n : ℤ)
    [K.IsStrictlyLE n]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) (K.X i)) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.Q).obj K) ≅
      (DerivedCategory.Q).obj
        ((((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) :=
  ⟨smallEtaleDerivedModulePullbackObjQIso f K n hflat⟩

/-- **`Lf^*(M[-i]) ≅ (f^*M)[-i]` for a flat module `M`**, as an isomorphism. -/
def smallEtaleDerivedModulePullbackSingleIsoOfFlat
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) M) :
    (smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) i).obj M) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          i).obj
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).obj M) :=
  let K := (HomologicalComplex.single
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) i).obj M
  have hflat : ∀ j : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) (K.X j) := fun j => by
    by_cases hj : j = i
    · subst hj
      exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
        (HomologicalComplex.singleObjXSelf _ _ M).symm hM
    · exact isFlat_of_isZero B S hS (HomologicalComplex.isZero_single_obj_X _ i M j hj)
  let F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) :=
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f).toModulesHom
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ i).app M) ≪≫
    smallEtaleDerivedModulePullbackObjQIso f K i hflat ≪≫
    (DerivedCategory.Q).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) i).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ i).app _).symm

/-- **`Lf^*(M[-i]) ≅ (f^*M)[-i]` for a flat module `M`.** -/
theorem nonempty_smallEtaleDerivedModulePullback_obj_singleFunctor_iso
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) M) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) i).obj M) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          i).obj
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).obj M)) :=
  ⟨smallEtaleDerivedModulePullbackSingleIsoOfFlat f M i hM⟩

/-- **The derived pullback of the structure sheaf is the structure sheaf**:
`Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`. -/
def smallEtaleDerivedModulePullbackUnitIso :
    (smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral
    (smallEtaleRingedToposHom B S hS f)

end AlgebraicGeometry.Space

end
