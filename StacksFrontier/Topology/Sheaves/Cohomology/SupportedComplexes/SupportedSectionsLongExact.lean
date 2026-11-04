module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExactIdentity
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsSheafTriangle

/-!
# Cohomology with support in a closed subset, degree by degree

Let `X` be a ringed space, `Z ⊆ X` a closed subset, `j : U → X` the inclusion of the open
complement and `ℱ` an `𝒪_X`-module.  The modules `i_*ℋ^q_Z(ℱ)` are the right derived functors
of the functor `ℱ ↦ i_*ℋ_Z(ℱ)` of sections supported on `Z`.  This file proves the ringed-space
form of [Stacks, Tag 0A45]:

* `i_*ℋ⁰_Z(ℱ) = ker(ℱ ⟶ j_*(ℱ|_U))`,
* `i_*ℋ¹_Z(ℱ) = coker(ℱ ⟶ j_*(ℱ|_U))`,
* `i_*ℋ^{p+1}_Z(ℱ) = R^pj_*(ℱ|_U)` for `p ≥ 1`.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.restrictPushRightDerivedIso`:
  `R^p(j_*(-|_U)) ≅ R^pj_* ∘ (-|_U)`.
* `Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedZeroIso`,
  `Stacks.Cohomology.SupportedComplexes.supportedSectionsRightDerivedOneIso` and
  `Stacks.Cohomology.SupportedComplexes.restrictPushHigherDirectImageSupportedIso`: the three
  identifications above.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- The short complex `i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)` of endofunctors of `𝒪_X`-modules is short exact
at every injective module. -/
theorem supportedSectionsShortComplex_shortExact_on_injectives
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (hM : Injective M) :
    (NatTrans.appShortComplex (supportedSectionsSubsheafInclusion X Z)
      (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit
      (supportedSectionsSubsheafInclusion_comp_unit X Z hZ) M).ShortExact :=
  have := hM
  supportedSectionsRestrictPushShortExact X Z hZ M

/-- `ℱ ↦ j_*(ℱ|_U)` is left exact. -/
instance preservesFiniteLimits_restrictPush :
    PreservesFiniteLimits (jStar (openComplement Z hZ) (structureSheafRing X) ⋙
      jPush (openComplement Z hZ) (structureSheafRing X)) :=
  haveI : (jPush (openComplement Z hZ) (structureSheafRing X)).IsRightAdjoint :=
    (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).isRightAdjoint
  inferInstance

/-- **`i_*ℋ⁰_Z(ℱ) = ker(ℱ ⟶ j_*(ℱ|_U))`.** -/
def supportedSectionsRightDerivedZeroIso (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    ((supportedSectionsFunctor X Z).rightDerived 0).obj F ≅
      kernel ((jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.app F) :=
  rightDerivedZeroIsoKernelOfShortExactOnInjectives _ _ _
    (supportedSectionsShortComplex_shortExact_on_injectives X Z hZ) F

/-- **`i_*ℋ¹_Z(ℱ) = coker(ℱ ⟶ j_*(ℱ|_U))`.** -/
def supportedSectionsRightDerivedOneIso (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    ((supportedSectionsFunctor X Z).rightDerived 1).obj F ≅
      cokernel ((jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.app F) :=
  rightDerivedOneIsoCokernelOfShortExactOnInjectives _ _ _
    (supportedSectionsShortComplex_shortExact_on_injectives X Z hZ) F

/-- **`R^p(j_*(-|_U)) = R^pj_*(-|_U)`**: the right derived functors of `ℱ ↦ j_*(ℱ|_U)` are those
of the direct image at the restricted module. -/
def restrictPushRightDerivedIso (n : ℕ) :
    (jStar (openComplement Z hZ) (structureSheafRing X) ⋙
        jPush (openComplement Z hZ) (structureSheafRing X)).rightDerived n ≅
      jStar (openComplement Z hZ) (structureSheafRing X) ⋙
        (jPush (openComplement Z hZ) (structureSheafRing X)).rightDerived n :=
  haveI := Stacks.Cohomology.HigherDirectImage.jStar_preservesInjectiveObjects
    (openComplement Z hZ) (structureSheafRing X)
  Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso _ _ n

/-- **`R^pj_*(ℱ|_U) ≅ i_*ℋ^{p+1}_Z(ℱ)` for `p ≥ 1`.**  The comparison is the connecting
morphism of the long exact sequence of `i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)`, read through
`restrictPushRightDerivedIso`. -/
def restrictPushHigherDirectImageSupportedIso
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℕ) (hn : 0 < n) :
    ((jPush (openComplement Z hZ) (structureSheafRing X)).rightDerived n).obj
        ((jStar (openComplement Z hZ) (structureSheafRing X)).obj F) ≅
      ((supportedSectionsFunctor X Z).rightDerived (n + 1)).obj F :=
  ((restrictPushRightDerivedIso X Z hZ n).app F).symm ≪≫
    rightDerivedSuccIsoOfShortExactOnInjectives _ _ _
      (supportedSectionsShortComplex_shortExact_on_injectives X Z hZ) F n hn

end Stacks.Cohomology.SupportedComplexes

end
