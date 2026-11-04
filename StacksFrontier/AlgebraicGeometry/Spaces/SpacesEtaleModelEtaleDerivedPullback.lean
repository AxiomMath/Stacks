module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineGlobalPointDerived

/-!
# Derived pullback along an étale morphism on the spaces-étale models

Let `j : X ⟶ Y` be an étale morphism of algebraic spaces. On the models of the ringed
spaces-étale sites, the inverse image of modules along
`AlgebraicGeometry.Space.spacesEtaleModelHom j`
is restriction along postcomposition with `j`
(`AlgebraicGeometry.Space.spacesEtaleModelPullbackIsoPushforward`). Restriction is a left adjoint
(of the direct image along `j`) and a right adjoint (of the inverse image along postcomposition),
so it is exact, and the derived pullback `Lj^*` is the functor that `j^*` induces on derived
categories.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelPostcompHom`: postcomposition with `j` as a morphism of
  ringed topoi from the model of `Y` to the model of `X`; its direct image is restriction.
* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIsoOfEtale`: `Lj^* ≅ D(j^*)`.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)

attribute [local instance] HasDerivedCategory.standard RingedSite.hasSheafCompose_forget₂_ringCat

/-- **Postcomposition with an étale morphism `j : X ⟶ Y` as a morphism of ringed topoi** from the
model of `Y` to the model of `X`: its functor of sites is postcomposition and its structure map
reads a regular function on `W` as one on the same algebraic space over `Y`. Its direct image is
restriction of modules along postcomposition. -/
def spacesEtaleModelPostcompHom :
    RingedToposSiteHom (spacesEtaleModelRingedTopos B S hS Y)
      (spacesEtaleModelRingedTopos B S hS X) where
  u := smallModelPostcomp B S hS j hj
  isContinuous := isContinuous_smallModelPostcomp_ringedTopos B S hS j hj
  fSharp := ⟨smallModelPostcompSharpComm B S hS j hj⟩

/-- The direct image along postcomposition is restriction along postcomposition. -/
theorem spacesEtaleModelPostcompHom_pushforwardTopos :
    (spacesEtaleModelPostcompHom B S hS j hj).pushforwardTopos =
      SheafOfModules.pushforward (smallModelPostcompSharp B S hS j hj) :=
  rfl

include hj in
/-- The inverse image of modules along `AlgebraicGeometry.Space.spacesEtaleModelHom j`, for `j`
étale, preserves finite limits: it is restriction along postcomposition, a right adjoint. -/
theorem preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos :
    PreservesFiniteLimits (spacesEtaleModelHom B S hS j).pullbackTopos :=
  have : PreservesLimitsOfSize.{0, 0} (spacesEtaleModelPostcompHom B S hS j hj).pushforwardTopos :=
    (spacesEtaleModelPostcompHom B S hS j hj).pullbackPushforwardAdjunctionTopos
      |>.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (spacesEtaleModelPostcompHom B S hS j hj).pushforwardTopos :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  preservesFiniteLimits_of_natIso (F := (spacesEtaleModelPostcompHom B S hS j hj).pushforwardTopos)
    (spacesEtaleModelPullbackIsoPushforward B S hS j hj).symm

/-- The inverse image of modules along `AlgebraicGeometry.Space.spacesEtaleModelHom j` preserves
finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_spacesEtaleModelHom_pullbackTopos :
    PreservesFiniteColimits (spacesEtaleModelHom B S hS j).pullbackTopos :=
  haveI : PreservesColimitsOfSize.{0, 0} (spacesEtaleModelHom B S hS j).pullbackTopos :=
    (spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Derived pullback along an étale morphism, on the spaces-étale models, is the functor that
the (exact) inverse image induces on derived categories.** -/
def spacesEtaleModelDerivedPullbackIsoOfEtale :
    haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS j hj
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback.{u}
        (spacesEtaleModelHom B S hS j) ≅
      (spacesEtaleModelHom B S hS j).pullbackTopos.mapDerivedCategory :=
  haveI := preservesFiniteLimits_spacesEtaleModelHom_pullbackTopos B S hS j hj
  derivedPullbackIsoMapDerivedCategoryOfExact (spacesEtaleModelHom B S hS j)

end AlgebraicGeometry.Space

end
