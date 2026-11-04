module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelEtaleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtaleDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Derived extension by zero on the spaces-étale models, and its base change

For an étale morphism `j : Y ⟶ W` of algebraic spaces, extension by zero `j_!` on the
spaces-étale models (`AlgebraicGeometry.Space.spacesEtaleModelLowerShriek`) is exact, so it
induces a functor on derived categories which is left adjoint to the derived pullback `Lj^*`
(`AlgebraicGeometry.Space.spacesEtaleModelDerivedLowerShriekAdjunction`).

For a cartesian square
```
  Y' --j'--> W'
  |h         |g
  v          v
  Y  --j-->  W
```
with `j`, `j'` étale, the base change morphism `Lh^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` (the mate of the square
of derived pullbacks along the two derived extension-by-zero adjunctions) is invertible
(`AlgebraicGeometry.Space.isIso_mateEquiv_symm_spacesEtaleModelDerivedLowerShriekAdjunction`):
it is a conjugate of the derived base change morphism `Rg_* ⋙ Lj^* ⟶ Lj'^* ⋙ Rh_*`, invertible by
`AlgebraicGeometry.Space.isIso_spacesEtaleModelDerivedPushforwardBaseChange_of_isPullback`. With
`CategoryTheory.Adjunction.homEquivOfIsIsoMate` this identifies morphisms `Lg^*(j_! A) ⟶ K` with
morphisms `Lh^* A ⟶ Lj'^* K`, which is how the Mayer–Vietoris triangles of Stacks 08GV are compared
along the stages of a limit in the proof of Stacks 09RI.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelDerivedLowerShriek`: derived extension by zero.
* `AlgebraicGeometry.Space.spacesEtaleModelDerivedLowerShriekAdjunction`: `j_! ⊣ Lj^*`.

## Main results

* `AlgebraicGeometry.Space.isIso_mateEquiv_symm_spacesEtaleModelDerivedLowerShriekAdjunction`:
  base change for derived extension by zero along a cartesian square.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

attribute [local instance high] HasDerivedCategory.standard

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Adjunction

variable {X Y : AlgebraicSpaces B S hS} (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)

/-- **Derived extension by zero on the spaces-étale models**: the functor induced on derived
categories by the exact functor `AlgebraicGeometry.Space.spacesEtaleModelLowerShriek`. -/
def spacesEtaleModelDerivedLowerShriek :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS X).O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Y).O)) :=
  (spacesEtaleModelLowerShriek B S hS j hj).mapDerivedCategory

/-- **Derived extension by zero is left adjoint to derived pullback**, along an étale morphism
on the spaces-étale models: the derived form of `j_! ⊣ j^*`, both functors being exact, with the
derived pullback identified with the functor induced by the exact inverse image. -/
def spacesEtaleModelDerivedLowerShriekAdjunction :
    spacesEtaleModelDerivedLowerShriek B S hS j hj ⊣
      derivedPullback (spacesEtaleModelHom B S hS j) :=
  haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS j hj
  (Adjunction.mapDerivedCategory (spacesEtaleModelLowerShriekAdjunction B S hS j hj)).ofNatIsoRight
    (spacesEtaleModelDerivedPullbackIsoOfEtale B S hS j hj).symm

end Adjunction

variable {W W' Y Y' : AlgebraicSpaces B S hS} (g : W' ⟶ W) (h : Y' ⟶ Y) (j : Y ⟶ W)
  (j' : Y' ⟶ W') (comm : h ≫ j = j' ≫ g)

/-- **Base change for derived extension by zero on the spaces-étale models**: for a cartesian
square with étale horizontal arrows `j`, `j'`, the mate `Lh^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` of the square
of derived pullbacks along the derived extension-by-zero adjunctions is invertible. It is a
conjugate of the derived base change morphism `Rg_* ⋙ Lj^* ⟶ Lj'^* ⋙ Rh_*`
(`CategoryTheory.Adjunction.isIso_mateEquiv_symm_iff_isIso_mateEquiv`). -/
theorem isIso_mateEquiv_symm_spacesEtaleModelDerivedLowerShriekAdjunction
    (hj : IsEtale B S hS j.hom) (hj' : IsEtale B S hS j'.hom) (sq : IsPullback j' h g j) :
    IsIso ((mateEquiv (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j hj)
      (spacesEtaleModelDerivedLowerShriekAdjunction B S hS j' hj')).symm
        (spacesEtaleModelDerivedPullbackSquare B S hS g h j j' comm)).natTrans :=
  (Adjunction.isIso_mateEquiv_symm_iff_isIso_mateEquiv _ _ _
    (derivedAdjunction (spacesEtaleModelHom B S hS h)
      (isMorphismOfSites_spacesEtaleModelHom B S hS h))
    (derivedAdjunction (spacesEtaleModelHom B S hS g)
      (isMorphismOfSites_spacesEtaleModelHom B S hS g))).2
    (isIso_spacesEtaleModelDerivedPushforwardBaseChange_of_isPullback B S hS g h j j' comm hj hj'
      sq)

end AlgebraicGeometry.Space

end
