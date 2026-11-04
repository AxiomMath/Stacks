module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeUnitSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived

/-!
# The base change map of modules of small étale ringed topoi against the canonical one

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces.  The base change map
`g^* f_* M ⟶ f'_* (g')^* M` of modules can be built from the morphisms of small étale ringed
topoi of Stacks 03G8 and their pullback and pushforward of modules
(`AlgebraicGeometry.Space.smallEtaleModuleBaseChangeMap`, the mate across the vertical
adjunctions of the comparison of composite pullbacks), or as the mate across the horizontal
adjunctions of Stacks 03LU of the comparison of composite direct images
(`AlgebraicGeometry.Space.moduleBaseChangeMap`).  This file shows that the two are invertible
together; consequently the base change map of the ringed topoi is invertible for a cartesian
square with étale bottom arrow as soon as the canonical comparison of Stacks 03LX
(`AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison`) is.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap`.
* `AlgebraicGeometry.Space.isIso_smallEtaleModuleBaseChangeMap_of_isIso_comparison`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The base change map of modules of the small étale ringed topoi of a commutative square is
invertible at a module as soon as the base change map of Stacks 03LU is invertible there. -/
theorem isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap_app
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (h : IsIso ((moduleBaseChangeMap f g f' g' w).app M)) :
    IsIso (smallEtaleModuleBaseChangeMap B S hS f g f' g' w M) := by
  let adj {A C : AlgebraicSpaces B S hS} (k : A ⟶ C) :=
    RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS A)
      (Y := smallEtaleRingedTopos B S hS C) (smallEtaleRingedToposHom B S hS k)
  exact Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_mateEquiv_symm_app
    (adj f) (adj f') (adj g) (adj g')
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHomComp B S hS f' g))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHomComp B S hS g' f))
    adj w
    (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f')
      (smallEtaleRingedToposHom B S hS g))
    (pushforwardModulesCompTransport B S hS f' g)
    (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS g')
      (smallEtaleRingedToposHom B S hS f))
    (pushforwardModulesCompTransport B S hS g' f)
    (modulePullbackAdjunction B S hS g) (modulePullbackAdjunction B S hS g')
    (pushforwardModules_eq_modulePushforward B S hS g)
    (pushforwardModules_eq_modulePushforward B S hS g')
    (pushforwardModules_eq_modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS f')
    (fun k => pushforwardModules_eq_modulePushforward B S hS k)
    (modulePushforward_comp_eq B S hS f' g) (modulePushforward_comp_eq B S hS g' f)
    (modulePushforwardCompIso B S hS f' g) (modulePushforwardCompIso B S hS g' f)
    (modulePushforwardCompIso.eq_1 B S hS f' g) (modulePushforwardCompIso.eq_1 B S hS g' f)
    (moduleBaseChangeMap f g f' g' w) (moduleBaseChangeMap.eq_1 f g f' g' w) M h

/-- The base change map of modules of the small étale ringed topoi of a commutative square is
invertible at every module as soon as the base change map of Stacks 03LU is. -/
theorem isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap
    (h : IsIso (moduleBaseChangeMap f g f' g' w))
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    IsIso (smallEtaleModuleBaseChangeMap B S hS f g f' g' w M) :=
  isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap_app B S hS f g f' g' w M
    (NatIso.isIso_app_of_isIso (moduleBaseChangeMap f g f' g' w) M)

/-- For a cartesian square of algebraic spaces with étale bottom arrow, the base change map of
modules of the small étale ringed topoi is invertible as soon as the canonical comparison of
Stacks 03LX is. -/
theorem isIso_smallEtaleModuleBaseChangeMap_of_isIso_comparison (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom)
    (h : IsIso (moduleEtaleBaseChangeComparison B S hS g' f' f g sq hg))
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    IsIso (smallEtaleModuleBaseChangeMap B S hS f g f' g' sq.w M) := by
  unfold moduleEtaleBaseChangeComparison at h
  rw [isIso_comp_left_iff, isIso_comp_right_iff] at h
  exact isIso_smallEtaleModuleBaseChangeMap_of_isIso_moduleBaseChangeMap B S hS f g f' g' sq.w h M

end AlgebraicGeometry.Space

end
