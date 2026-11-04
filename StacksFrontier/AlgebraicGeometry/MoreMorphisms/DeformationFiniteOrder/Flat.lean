module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Reduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram
public import StacksFrontier.AlgebraicGeometry.Thickenings.Flatness

/-!
# Flatness along a finite-order deformation

In either of the two standing deformation situations the morphism between the special fibres is
flat if and only if its ambient deformation is.

One direction is base change: the special-fibre morphism is the base change of its deformation
along the base thickening, and flatness is stable under base change. The other direction is the
content of Tag 0CF3 for a flat deformation diagram — flatness of the special-fibre morphism lifts
to the ambient morphism because the ambient source is flat and locally of finite presentation
over the ambient base and the ambient target is locally of finite type over it — and of Tag 06AF
for a cartesian finite-order deformation diagram, where the base thickening is of finite order
and only flatness of the ambient source over the ambient base is assumed.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.flat_iff`: **Stacks 0CF4**, flat case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.flat_iff`: **Stacks 06AG**, flat
  case.

## Implementation notes

The structure morphisms of the two sources over the two bases are the composites through the
targets, so the two `rfl`s supplied to
`Stacks.Flatness.flat_of_flat_baseChange_thickening` are the factorisations that lemma asks for;
it is stated with the four structure morphisms as independent data rather than with composites.
In the finite-order situation the four structure morphisms are instead fields of the diagram, and
the two factorisations are the fields recording that the horizontal morphisms are over their
bases.

## References

* [Stacks Project, Tag 06AF](https://stacks.math.columbia.edu/tag/06AF)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF3](https://stacks.math.columbia.edu/tag/0CF3)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Flatness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "flat"]
theorem FlatDeformationDiagram.flat_iff (D : FlatDeformationDiagram.{u}) :
    Flat D.f ↔ Flat D.f' := by
  refine ⟨fun hf ↦ ?_, fun hf' ↦
    MorphismProperty.of_isPullback (D.isPullback_X.of_bot D.comm_f D.isPullback_Y) hf'⟩
  have : LocallyOfFiniteType D.g' := D.finiteType_Y'
  have : Flat (D.f' ≫ D.g') := D.flat_X'
  have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
  exact Stacks.Flatness.flat_of_flat_baseChange_thickening D.iX D.iY D.iS D.f D.f'
    (D.f ≫ D.g) (D.f' ≫ D.g') D.g D.g' D.iX_thickening D.iY_thickening D.iS_thickening
    D.comm_f.symm rfl rfl D.isPullback_X D.isPullback_Y hf

/-- **Stacks 06AG, flat case.** Flatness is invariant under a cartesian finite-order deformation
with flat ambient source. -/
@[stacks 06AG "flat"]
theorem CartesianFiniteOrderDeformationDiagram.flat_iff
    (D : CartesianFiniteOrderDeformationDiagram.{u}) : Flat D.f ↔ Flat D.f' :=
  ⟨AlgebraicGeometry.flat_of_flat_reduction D.iX_thickening D.iY_thickening D.iS_finiteOrder
      D.X_cartesian D.Y_cartesian D.f_thickening_comm.symm D.f_over_S D.f'_over_S' D.X'_flat,
    CartesianFiniteOrderDeformationDiagram.property_of_baseChange @Flat.{u} D⟩

end Stacks.Thickenings

end
