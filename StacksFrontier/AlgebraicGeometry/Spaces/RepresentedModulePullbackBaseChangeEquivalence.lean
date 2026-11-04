module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
import all StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# Pullback of modules across the small étale site of a represented space

For a morphism `g : T' ⟶ T` in the big fppf site over `S`, the equivalence between modules on the
small étale site of the scheme underlying `T` and modules on the small étale site of the algebraic
space `yoneda.obj T` intertwines the two pullbacks of modules along `g`.

## Main definitions

* `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalencePullbackIso`: the natural
  isomorphism between the two composites of an equivalence with a pullback along `g`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

section Represented

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-! ### The inverse image of modules across the identification of the sites -/

/-- The equivalence between modules on the small étale site of the scheme underlying `T` and
modules on the small étale site of `yoneda.obj T` intertwines the two pullbacks along `g`. -/
noncomputable def representedSmallEtaleModuleEquivalencePullbackIso :
    (representedSmallEtaleModuleEquivalence B S hS T).functor ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) ≅
      SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (representedSmallEtaleModuleEquivalence B S hS T').counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (representedModulePullbackIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (representedSmallEtaleModuleEquivalence B S hS T).unitIso.symm _ ≪≫
      Functor.leftUnitor _) _

end Represented

end AlgebraicGeometry.Space

end
