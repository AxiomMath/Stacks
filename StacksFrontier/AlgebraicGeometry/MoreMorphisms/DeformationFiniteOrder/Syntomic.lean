module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties

/-!
# Syntomicity along a finite-order deformation

In either of the two standing deformation situations the morphism between the special fibres is
syntomic if and only if its ambient deformation is.

One direction is base change: the special-fibre morphism is the base change of its deformation
along the base thickening, and syntomicity is stable under base change. The other direction is
the fibrewise criterion for syntomicity: the ambient morphism is flat, because a syntomic
morphism is flat and flatness is invariant under the deformation, and locally of finite
presentation, because it is so over the ambient base while the ambient target is locally of
finite type there; and each of its fibres is a fibre of the special-fibre morphism, hence a
local complete intersection over the residue field of its base point.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.syntomic_iff`: **Stacks 0CF4**, syntomic case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.syntomic_iff`: **Stacks 06AG**,
  syntomic case. Here local finite presentation of the ambient morphism comes from the
  corresponding case of the same lemma, applied to the local finite presentation of the
  special-fibre morphism that syntomicity already provides.

## Implementation notes

Being a local complete intersection over a field is, by definition, syntomicity of the
structure morphism to the spectrum of that field, so the fibre condition demanded by
`AlgebraicGeometry.syntomic_of_lci_fibers` (Tag 01UF) is exactly what transporting syntomicity
along the identification of corresponding fibres produces.

## References

* [Stacks Project, Tag 01UF](https://stacks.math.columbia.edu/tag/01UF)
* [Stacks Project, Tag 01UL](https://stacks.math.columbia.edu/tag/01UL)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Syntomicity is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "syntomic"]
theorem FlatDeformationDiagram.syntomic_iff (D : FlatDeformationDiagram.{u}) :
    Syntomic D.f ↔ Syntomic D.f' := by
  refine ⟨fun hf => ?_, fun hf' =>
    MorphismProperty.of_isPullback (D.isPullback_X.of_bot D.comm_f D.isPullback_Y) hf'⟩
  have : Flat D.f := AlgebraicGeometry.flat hf
  have : LocallyOfFiniteType D.g' := D.finiteType_Y'
  have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
  have : LocallyOfFinitePresentation D.f' := locallyOfFinitePresentation_of_comp D.f' D.g'
  have : Flat D.f' := D.flat_iff.1 inferInstance
  have : MorphismProperty.RespectsIso (@Syntomic.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine syntomic_of_lci_fibers D.f' fun y' => ?_
  obtain ⟨y, rfl⟩ := D.iY_thickening.2 y'
  exact (D.prop_fiberToSpecResidueField_iff (@Syntomic.{u}) y).1
    (MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback D.f (D.Y.fromSpecResidueField y)) hf)

/-- **Stacks 06AG, syntomic case.** Syntomicity is invariant under a cartesian finite-order
deformation with flat ambient source. -/
@[stacks 06AG "syntomic"]
theorem CartesianFiniteOrderDeformationDiagram.syntomic_iff
    (D : CartesianFiniteOrderDeformationDiagram.{u}) : Syntomic D.f ↔ Syntomic D.f' := by
  refine ⟨fun hf => ?_,
    CartesianFiniteOrderDeformationDiagram.property_of_baseChange @Syntomic.{u} D⟩
  have : Flat D.f := AlgebraicGeometry.flat hf
  have : LocallyOfFinitePresentation D.f := AlgebraicGeometry.locallyOfFinitePresentation hf
  have : LocallyOfFinitePresentation D.f' := D.locallyOfFinitePresentation_iff.1 inferInstance
  have : Flat D.f' := D.flat_iff.1 inferInstance
  have : MorphismProperty.RespectsIso (@Syntomic.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine syntomic_of_lci_fibers D.f' fun y' => ?_
  obtain ⟨y, rfl⟩ := D.iY_thickening.2 y'
  exact (D.prop_fiberToSpecResidueField_iff (@Syntomic.{u}) y).1
    (MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback D.f (D.Y.fromSpecResidueField y)) hf)

end Stacks.Thickenings

end
