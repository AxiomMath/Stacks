module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact

/-!
# Degreewise and derived pullback agree along an isomorphism of ringed spaces

Let `e : X ≅ Y` be an isomorphism of ringed spaces. Degreewise pullback `e.hom^*` of sheaves of
modules is exact, so it induces a functor `D(𝒪_Y) ⥤ D(𝒪_X)` on the derived categories, and that
functor is the derived pullback `Le.hom^*`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategory` and
  `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategoryOfIsIso`:
  `Le.hom^* ≅ D(e.hom^*)`, for an isomorphism and for an invertible morphism.

## Main results

* `Stacks.Cohomology.DerivedPullbackAlongIso.preservesFiniteLimits_modulePullback_of_isIso`:
  degreewise pullback along an isomorphism preserves finite limits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedPullbackAlongIso

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}}

/-- Degreewise pullback of sheaves of modules along a morphism of ringed spaces preserves finite
colimits. -/
instance (f : X ⟶ Y) : Limits.PreservesFiniteColimits (modulePullback f) :=
  RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback f

/-- Degreewise pullback of sheaves of modules along an isomorphism of ringed spaces preserves
finite limits. -/
instance preservesFiniteLimits_modulePullback_of_isIso (f : X ⟶ Y) [IsIso f] :
    Limits.PreservesFiniteLimits (modulePullback f) :=
  haveI := Stacks.Cohomology.modulePullbackIso_isEquivalence (asIso f)
  inferInstance

variable (e : X ≅ Y)

/-- The derived pullback along an isomorphism `e` of ringed spaces is the functor induced on
derived categories by degreewise pullback: `Le.hom^* ≅ D(e.hom^*)`. -/
def derivedPullbackIsoMapDerivedCategory :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.hom ≅
      (modulePullback e.hom).mapDerivedCategory :=
  letI : (modulePullback e.hom).mapDerivedCategory.IsLeftDerivedFunctor
      (modulePullback e.hom).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      (modulePullback e.hom).mapDerivedCategoryFactorsh
  Functor.leftDerivedUnique
    (LF := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.hom)
    (LF' := (modulePullback e.hom).mapDerivedCategory)
    (α := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison e.hom)
    (α'₂ := (modulePullback e.hom).mapDerivedCategoryFactorsh.hom)
    (W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))

/-- The derived pullback along an invertible morphism `f` of ringed spaces is the functor induced
on derived categories by degreewise pullback: `Lf^* ≅ D(f^*)`. -/
def derivedPullbackIsoMapDerivedCategoryOfIsIso (f : X ⟶ Y) [IsIso f] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ≅
      (modulePullback f).mapDerivedCategory :=
  derivedPullbackIsoMapDerivedCategory (asIso f)

end

end Stacks.Cohomology.DerivedPullbackAlongIso

end
