module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism

/-!
# Derived pullback along the identity, at any model of the derived category

For a ringed space `X` and any model `HasDerivedCategory.{w}` of `D(𝒪_X)`, the derived pullback
`L(𝟙 X)^*` is isomorphic to the identity functor.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackAlongIso.pullbackOnHomotopyIdIsoGeneral`: degreewise
  pullback along `𝟙 X` followed by localization is the localization functor.
* `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIsoGeneral`: `L(𝟙 X)^* ≅ 𝟭`.

## Implementation notes

These are `Stacks.Cohomology.DerivedPullbackAlongIso.pullbackOnHomotopyIdIso` and
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso`, which are stated at the
standard model `HasDerivedCategory.standard`, for an arbitrary model; the construction is the
same: the identity functor of `D(𝒪_X)` is a left derived functor of degreewise pullback along
`𝟙 X`, and left derived functors are unique.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedPullbackAlongIso

noncomputable section

universe w u

/-- Degreewise pullback along the identity, followed by localization, is the localization
functor, at any model of the derived category. -/
def pullbackOnHomotopyIdIsoGeneral (X : RingedSpace.{u, u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))] :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (𝟙 X) :=
  Functor.rightUnitor _ ≪≫
    (Functor.isoWhiskerRight
      (mapHomotopyCategoryIso (RingedSpaceModuleAdjunction.modulePullbackId X)
          (ComplexShape.up ℤ) ≪≫
        mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.leftUnitor _).symm

/-- **Derived pullback along the identity is the identity**, `L(𝟙 X)^* ≅ 𝟭`, at any model of
the derived category. -/
def derivedPullbackIdIsoGeneral (X : RingedSpace.{u, u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (𝟙 X) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  letI : (𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))).IsLeftDerivedFunctor
      (pullbackOnHomotopyIdIsoGeneral X).hom
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (pullbackOnHomotopyIdIsoGeneral X)
  Functor.leftDerivedUnique
    (LF := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (𝟙 X))
    (LF' := 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (α := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (𝟙 X))
    (α'₂ := (pullbackOnHomotopyIdIsoGeneral X).hom)
    (W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

end

end Stacks.Cohomology.DerivedPullbackAlongIso
