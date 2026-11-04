module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Separated
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological

/-!
# Properness along a finite-order deformation

In a flat deformation diagram the morphism between the special fibres is proper if and only if
its ambient deformation is.

Properness is separatedness together with universal closedness and local finite type. The first
two transfer in both directions because the two horizontal morphisms form a morphism of
thickenings. Local finite type of the deformation follows from its local finite presentation over
the enlarged base, and local finite type of the special fibre follows by base change — which also
gives the reverse implication in one step, since properness is stable under base change.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.isProper_iff`

## Implementation notes

The commutative square formed by the two thickenings and the two horizontal morphisms is passed
to the thickening-morphism results as a morphism in the arrow category of schemes, built by
`CategoryTheory.Arrow.homMk`. Properness is Mathlib's `AlgebraicGeometry.IsProper`, unfolded by
`AlgebraicGeometry.isProper_iff` into its three constituent conditions.

## References

* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

/-- Properness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "proper"]
theorem FlatDeformationDiagram.isProper_iff (d : FlatDeformationDiagram.{u}) :
    IsProper d.f ↔ IsProper d.f' := by
  refine ⟨fun h => ?_, MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (d.isPullback_X.of_bot d.comm_f d.isPullback_Y)⟩
  obtain ⟨hs, huc, -⟩ := (AlgebraicGeometry.isProper_iff d.f).mp h
  let φ : Arrow.mk d.iX ⟶ Arrow.mk d.iY := Arrow.homMk d.f d.f' d.comm_f.symm
  have : LocallyOfFinitePresentation (d.f' ≫ d.g') := d.finitePresentation_X'
  exact (AlgebraicGeometry.isProper_iff d.f').mpr
    ⟨(isSeparated_left_iff_right d.iX_thickening d.iY_thickening φ).mp hs,
      (universallyClosed_left_iff_right φ d.iX_thickening d.iY_thickening).mp huc,
      locallyOfFiniteType_of_comp d.f' d.g'⟩

end Stacks.Thickenings

end
