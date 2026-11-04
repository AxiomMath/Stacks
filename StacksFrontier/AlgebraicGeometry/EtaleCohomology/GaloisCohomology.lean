module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.DerivedFunctorBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous

/-!
# Invariants are the zeroth continuous group cohomology

Continuous group cohomology `H ⁱ(G, M)` of a discrete continuous `G`-module is the `i`-th right
derived functor of taking `G`-invariants (`continuousGroupCohomology`). Taking invariants is left
exact, so the canonical map `Mᴳ ⟶ H ⁰(G, M)` is an isomorphism. For `G` the absolute Galois group
at a geometric point of the spectrum of a field this is the Galois-cohomology half of the
degree-zero statement of [Stacks, Tag 03QU] part (2).

## Main results

* `Stacks.GroupCohomology.preservesFiniteLimits_continuousGModuleInvariants` — taking
  `G`-invariants of a discrete continuous `G`-module is left exact.
* `Stacks.GroupCohomology.invariantsIsoZerothCohomology` — `Mᴳ ≅ H ⁰(G, M)`, the canonical
  degree-zero unit of the right derived invariants functor.
* `Stacks.EtaleCohomology.invariantsIsoZerothGroupCohomology` — the same isomorphism at the
  absolute Galois group of a geometric point of `Spec K`.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.GroupCohomology

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- `ℤ`-modules are given the discrete topology when forming continuous actions. -/
local instance : HasForget₂ (ModuleCat.{v} ℤ) TopCat.{v} :=
  { forget₂ := forget (ModuleCat.{v} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

/-- **Taking invariants is left exact**: the functor of `G`-invariants on discrete continuous
`G`-modules preserves finite limits. -/
public instance preservesFiniteLimits_continuousGModuleInvariants :
    PreservesFiniteLimits (continuousGModuleInvariants.{u, v} G) := by
  have hcont : PreservesFiniteLimits
      (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G))) := by
    have := fun ⦃X Y : ObjectProperty.FullSubcategory
        (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G))⦄
      (f : X ⟶ Y) ↦ ObjectProperty.preservesKernels_ι _ f
    exact Functor.preservesFiniteLimits_of_preservesKernels _
  have hdisc : PreservesFiniteLimits
      (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G))) := by
    have := fun ⦃X Y : ObjectProperty.FullSubcategory
        (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G))⦄
      (f : X ⟶ Y) ↦ ObjectProperty.preservesKernels_ι _ f
    exact Functor.preservesFiniteLimits_of_preservesKernels _
  change PreservesFiniteLimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{v} ℤ) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{v} ℤ) (G := G)) ⋙
      Rep.ActionToRep ℤ G ⋙ Rep.invariantsFunctor ℤ G ⋙
        forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v})
  infer_instance

variable [IsTopologicalGroup G]

/-- The canonical degree-zero comparison from invariants to continuous group cohomology,
`Mᴳ ≅ H ⁰(G, M)`. It is the unit of the right derived invariants functor, which is invertible
because invariants are left exact. -/
public noncomputable def invariantsIsoZerothCohomology
    (M : ContinuousGModule.{u, max u v} G) :
    (continuousGModuleInvariants G).obj M ≅ continuousGroupCohomology.{u, v} G 0 M :=
  haveI := Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit
    (continuousGModuleInvariants.{u, max u v} G) M
  asIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit
    (continuousGModuleInvariants.{u, max u v} G) M)

/-- The degree-zero comparison with continuous group cohomology is the right-derived-functor
unit. -/
public theorem invariantsIsoZerothCohomology_hom (M : ContinuousGModule.{u, max u v} G) :
    (invariantsIsoZerothCohomology.{u, v} G M).hom =
      Stacks.RightDerivedPlus.rightDerivedZeroUnit
        (continuousGModuleInvariants.{u, max u v} G) M := rfl

end Stacks.GroupCohomology

namespace Stacks.EtaleCohomology

open Stacks.GroupCohomology

variable (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K)))

/-- The canonical degree-zero comparison from the invariants of a continuous module for the
absolute Galois group at a geometric point of `Spec K` to its zeroth Galois cohomology group,
`Mᴳ ≅ H ⁰(K, M)`. -/
public noncomputable def invariantsIsoZerothGroupCohomology
    (M : ContinuousGModule.{u, u} (GeometricPoint.absoluteGaloisGroup s)) :
    (continuousGModuleInvariants (GeometricPoint.absoluteGaloisGroup s)).obj M ≅
      continuousGroupCohomology (GeometricPoint.absoluteGaloisGroup s) 0 M :=
  invariantsIsoZerothCohomology.{u, u} _ M

/-- The degree-zero identification with Galois cohomology is the canonical unit of the right
derived invariants functor. -/
public theorem invariantsIsoZerothGroupCohomology_unit
    (M : ContinuousGModule.{u, u} (GeometricPoint.absoluteGaloisGroup s)) :
    (invariantsIsoZerothGroupCohomology K s M).hom =
      Stacks.RightDerivedPlus.rightDerivedZeroUnit
        (continuousGModuleInvariants (GeometricPoint.absoluteGaloisGroup s)) M := rfl

end Stacks.EtaleCohomology

end
