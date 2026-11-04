module

public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Smoothness along a finite-order deformation

In either of the two standing deformation situations the morphism between the special fibres is
smooth if and only if its ambient deformation is.

One direction is base change: the special-fibre morphism is the base change of its deformation
along the base thickening, and smoothness is stable under base change. The other direction is
the fibrewise criterion for smoothness: the ambient morphism is flat, because flatness is
invariant under the deformation, and locally of finite presentation, because it is so over the
ambient base while the ambient target is locally of finite type there; and each of its fibres is
a fibre of the special-fibre morphism, the deformation changing neither the fibres nor the
residue fields of the target.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.smooth_iff`: **Stacks 0CF4**, smooth case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.smooth_iff`: **Stacks 06AG**, smooth
  case. Here local finite presentation of the ambient morphism comes from the corresponding case
  of the same lemma instead, the ambient source not being assumed locally of finite presentation
  over the ambient base.

## Implementation notes

Every point of the thickened target is the image of a point of the smaller target, the target
thickening being surjective on points; the fibre of the ambient morphism over it is then
identified with a fibre of the special-fibre morphism by
`Stacks.Thickenings.prop_fiberToSpecResidueField_iff_of_isPullback`.

## References

* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Smoothness descends along a cartesian square with thickened target when the right-hand
morphism is flat and locally of finite presentation. -/
private theorem smooth_of_isPullback_of_thickening {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'} [Flat f'] [LocallyOfFinitePresentation f']
    (hj : IsThickening j) (h : IsPullback i f f' j) (hf : Smooth f) : Smooth f' := by
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine Smooth.of_smooth_fiberToSpecResidueField f' fun y' => ?_
  obtain ⟨y, rfl⟩ := hj.2 y'
  exact (prop_fiberToSpecResidueField_iff_of_isPullback hj h (@Smooth.{u}) y).1
    (MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) hf)

/-- Smoothness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "smooth"]
theorem FlatDeformationDiagram.smooth_iff (D : FlatDeformationDiagram.{u}) :
    Smooth D.f ↔ Smooth D.f' := by
  refine ⟨fun hf => ?_, MorphismProperty.of_isPullback
    (D.isPullback_X.of_bot D.comm_f D.isPullback_Y)⟩
  have : LocallyOfFiniteType D.g' := D.finiteType_Y'
  have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
  have : LocallyOfFinitePresentation D.f' := locallyOfFinitePresentation_of_comp D.f' D.g'
  have : Flat D.f' := D.flat_iff.1 inferInstance
  exact smooth_of_isPullback_of_thickening D.iY_thickening D.isPullback_f hf

/-- **Stacks 06AG, smooth case.** Smoothness is invariant under a cartesian finite-order
deformation with flat ambient source. -/
@[stacks 06AG "smooth"]
theorem CartesianFiniteOrderDeformationDiagram.smooth_iff
    (D : CartesianFiniteOrderDeformationDiagram.{u}) : Smooth D.f ↔ Smooth D.f' := by
  refine ⟨fun hf => ?_, CartesianFiniteOrderDeformationDiagram.property_of_baseChange @Smooth.{u} D⟩
  have : LocallyOfFinitePresentation D.f' := D.locallyOfFinitePresentation_iff.1 inferInstance
  have : Flat D.f' := D.flat_iff.1 inferInstance
  exact smooth_of_isPullback_of_thickening D.iY_thickening D.isPullback_f hf

end Stacks.Thickenings

end
