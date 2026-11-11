module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsWithSupport

/-!
# Sections with support in a closed subspace are left exact

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. This file proves
the two left exactness assertions of Stacks 0A4L: the functor `Γ_Z(X, -)` of global sections
with support in `Z` is left exact, and so is the functor `𝓗_Z : Ab(X_étale) ⥤ Ab(Z_étale)` of
sections with support in `Z`. Consequently the zeroth right derived functors are the functors
themselves: `H^0_Z(X, F) = Γ_Z(X, F)` and `𝓗^0_Z(F) = 𝓗_Z(F)`.

## Main definitions

* `AlgebraicGeometry.Space.closedSectionsWithSupportIsoPushforward`: the subsheaf `H_Z(F) ⊆ F`
  of sections supported on `|Z|` is the direct image along `i` of `𝓗_Z(F)`, naturally in `F`.
* `AlgebraicGeometry.Space.closedCohomologyWithSupportZeroIso`: `H^0_Z(X, -) ≅ Γ_Z(X, -)`.
* `AlgebraicGeometry.Space.higherSectionsWithSupportZeroIso`: `𝓗^0_Z ≅ 𝓗_Z`.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteLimits_sectionsWithSupportInClosedSubspace`: `𝓗_Z`
  is left exact, being right adjoint to the direct image `i_*` (the adjunction of Stacks 0A4M).
* `AlgebraicGeometry.Space.preservesFiniteLimits_closedSectionsWithSupport`: the subsheaf of
  sections supported on `|Z|` is left exact in the sheaf.
* `AlgebraicGeometry.Space.preservesFiniteLimits_closedGlobalSectionsWithSupport`: `Γ_Z(X, -)`
  is left exact.

## Implementation notes

The subsheaf `H_Z(F)` is left exact because it is `i_* 𝓗_Z(F)`: the unit of the inverse
image/direct image adjunction is invertible at a sheaf all of whose sections are supported on
`|Z|` (the essential-image clause of Stacks 04E5, part (2)), and `𝓗_Z(F)` is by definition the
inverse image of `H_Z(F)`. Both `𝓗_Z` and `i_*` are right adjoints, and so is global sections.

## References

* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4M](https://stacks.math.columbia.edu/tag/0A4M)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)

/-- **`𝓗_Z` is left exact**: it is right adjoint to the direct image along the closed immersion
`i`, which is the adjunction `i_* ⊣ 𝓗_Z` of Stacks 0A4M. -/
@[stacks 0A4L "the functor 𝓗_Z : Ab(X_étale) → Ab(Z_étale) is left exact"]
instance preservesFiniteLimits_sectionsWithSupportInClosedSubspace :
    PreservesFiniteLimits (sectionsWithSupportInClosedSubspace B S hS i hi) :=
  have : PreservesLimitsOfSize.{0, 0} (sectionsWithSupportInClosedSubspace B S hS i hi) :=
    (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i
      hi).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- **The subsheaf of sections supported on `|Z|` is the direct image of `𝓗_Z`.** For every
abelian sheaf `F` on `X_étale`, the unit of the inverse image/direct image adjunction along `i`
identifies the subsheaf `H_Z(F) ⊆ F` with `i_* 𝓗_Z(F)`, naturally in `F`. -/
def closedSectionsWithSupportIsoPushforward :
    closedSectionsWithSupport.{u + 1} B S hS i ≅
      sectionsWithSupportInClosedSubspace B S hS i hi ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ ((smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.app
        ((closedSectionsWithSupport.{u + 1} B S hS i).obj F))
      (isIso_unit_app_closedSectionsWithSupport B S hS i hi
        (unitIsoOnSupportedSheaves_of_isClosedImmersion B S hS i hi) F))
    (fun φ => (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.naturality
      ((closedSectionsWithSupport.{u + 1} B S hS i).map φ))

include hi in
/-- **The subsheaf of sections supported on `|Z|` is left exact in the sheaf**, being the
composite `i_* ∘ 𝓗_Z` of two right adjoints. -/
theorem preservesFiniteLimits_closedSectionsWithSupport :
    PreservesFiniteLimits (closedSectionsWithSupport.{u + 1} B S hS i) :=
  preservesFiniteLimits_of_natIso (closedSectionsWithSupportIsoPushforward B S hS i hi).symm

include hi in
/-- **The sections with support `Γ_Z(X, -)` are left exact** (Stacks 0A4L): the composite of the
left exact subsheaf of sections supported on `|Z|` with global sections, a right adjoint. -/
@[stacks 0A4L "the functor Γ_Z(X, -) is left exact"]
theorem preservesFiniteLimits_closedGlobalSectionsWithSupport :
    PreservesFiniteLimits (closedGlobalSectionsWithSupport B S hS i) :=
  have := preservesFiniteLimits_closedSectionsWithSupport B S hS i hi
  have : PreservesLimitsOfSize.{0, 0}
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :=
    (constantSheafΓAdj (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.{u + 1}).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  inferInstanceAs (PreservesFiniteLimits (closedSectionsWithSupport.{u + 1} B S hS i ⋙
    Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}))

/-- **`H^0_Z(X, -) = Γ_Z(X, -)`.** The zeroth right derived functor of the left exact functor
`Γ_Z(X, -)` is the functor itself. -/
def closedCohomologyWithSupportZeroIso :
    closedCohomologyWithSupport B S hS i 0 ≅ closedGlobalSectionsWithSupport B S hS i :=
  have := preservesFiniteLimits_closedGlobalSectionsWithSupport B S hS i hi
  (closedGlobalSectionsWithSupport B S hS i).rightDerivedZeroIsoSelf

/-- **`𝓗^0_Z = 𝓗_Z`.** The zeroth right derived functor of the left exact functor `𝓗_Z` is the
functor itself, as the source records after defining `𝓗^q_Z = R^q 𝓗_Z`. -/
@[stacks 0A4L "𝓗^0_Z(F) = 𝓗_Z(F)"]
def higherSectionsWithSupportZeroIso :
    higherSectionsWithSupportInClosedSubspace B S hS i hi 0 ≅
      sectionsWithSupportInClosedSubspace B S hS i hi :=
  letI := HasDerivedCategory.standard (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
  letI := HasDerivedCategory.standard (Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
  Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (sectionsWithSupportInClosedSubspace B S hS i hi)

end AlgebraicGeometry.Space

end
