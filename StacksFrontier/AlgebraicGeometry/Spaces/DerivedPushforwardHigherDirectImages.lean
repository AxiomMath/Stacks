module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedBelowRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# The derived direct image along a morphism of algebraic spaces and the higher direct images

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The derived direct image
`Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` is `AlgebraicGeometry.Space.smallEtaleDerivedModulePushforward`, the total
right derived functor of the degreewise direct image of modules along the morphism of small étale
ringed topoi of `f`.  This file records the facts about it that the coherence statements of
Stacks 08GK, 0D0R and 08IS consume:

* it is the total right derived functor of `AlgebraicGeometry.Space.modulePushforward`, the
  direct image of modules in which the higher direct images `R^n f_*` are written;
* on a module placed in degree `a` its degree-`m` cohomology is `R^{m-a} f_*`;
* it is left t-exact and exact (it commutes with shifts and preserves distinguished triangles);
* `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*` (Stacks 0D6E for algebraic spaces), by uniqueness of right
  adjoints from `Lf^* ⊣ Rf_*` and `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` (Stacks 07A6 and 0D6D).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePushforwardIso`: `Rf_*` is the total right
  derived functor of `AlgebraicGeometry.Space.modulePushforward`.
* `AlgebraicGeometry.Space.homologyDerivedModulePushforwardSingleIso`:
  `H^m(Rf_*(𝓕[-a])) ≅ R^{m-a} f_*𝓕`.
* `AlgebraicGeometry.Space.smallEtaleDerivedPushforwardCompIso` and
  `AlgebraicGeometry.Space.derivedModulePushforwardCompIso`: `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`.
* `AlgebraicGeometry.Space.isTriangulated_derivedModulePushforward`: exactness.

## References

* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] isGrothendieckAbelian_modules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck


attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **`Rf_*` is the total right derived functor of the direct image of modules.**  Both are
right derived functors of isomorphic functors on the homotopy category: the degreewise direct
image of the morphism of small étale ringed topoi is `AlgebraicGeometry.Space.modulePushforward`
(Stacks 03LU). -/
def smallEtaleDerivedModulePushforwardIso (f : X ⟶ Y) :
    smallEtaleDerivedModulePushforward B S hS f ≅
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) :
        DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :=
  @Stacks.DerivedFunctor.totalRightDerivedIsoOfIso _ _ _
    (isGrothendieckAbelian_modules B S hS X.1 X.2) _ _ _ _ _
    (smallEtaleRingedToposHom B S hS f).pushforwardModules
    (Functor.additive_of_iso (F := modulePushforward B S hS f)
      (pushforwardModulesIsoModulePushforward B S hS f).symm) (modulePushforward B S hS f)
    (modulePushforward_additive B S hS f) (pushforwardModulesIsoModulePushforward B S hS f)

/-- **The cohomology of `Rf_*` on a module placed in one degree is a higher direct image**:
`H^m(Rf_*(𝓕[-a])) ≅ R^n f_*𝓕` when `m - a = n`. -/
def homologyDerivedModulePushforwardSingleIso (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) (a m : ℤ) (n : ℕ) (hn : m - a = n) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) m).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) a).obj M)) ≅
      ((modulePushforward B S hS f).rightDerived n).obj M :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso (modulePushforward B S hS f)
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f))
    ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) M a m n hn

/-- `Rf_*` commutes with the shift, as a right derived functor of a functor which does. -/
instance commShift_derivedModulePushforward (f : X ⟶ Y) :
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) :
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _
    ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ

/-- **`Rf_*` is exact**: it preserves distinguished triangles. -/
instance isTriangulated_derivedModulePushforward (f : X ⟶ Y) :
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) :
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) _ _
    ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))

/-- **Stacks 0D6E for algebraic spaces**, in the ringed-topos spelling:
`Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`.  The composite is right adjoint to `Lg^* ⋙ Lf^*`, which is
`L(f ≫ g)^*` by Stacks 0D6D, whose right adjoint is `R(f ≫ g)_*`; right adjoints are unique up to
isomorphism. -/
def smallEtaleDerivedPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleDerivedModulePushforward B S hS f ⋙ smallEtaleDerivedModulePushforward B S hS g ≅
      smallEtaleDerivedModulePushforward B S hS (f ≫ g) :=
  ((smallEtaleDerivedAdjunction B S hS g).comp
      (smallEtaleDerivedAdjunction B S hS f)).rightAdjointUniq
    ((smallEtaleDerivedAdjunction B S hS (f ≫ g)).ofNatIsoLeft
      (smallEtaleDerivedPullbackCompIso B S hS f g).symm)

/-- **Stacks 0D6E for algebraic spaces**: `R(f ≫ g)_* ≅ Rf_* ⋙ Rg_*`, for the total right derived
functors of the direct images of modules. -/
def derivedModulePushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS (f ≫ g)) :
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) ≅
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f) :
        DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) ⋙
        (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS g) :
          DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
            DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  (smallEtaleDerivedModulePushforwardIso B S hS (f ≫ g)).symm ≪≫
    (smallEtaleDerivedPushforwardCompIso B S hS f g).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleDerivedModulePushforwardIso B S hS f) _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleDerivedModulePushforwardIso B S hS g)

end AlgebraicGeometry.Space

end
