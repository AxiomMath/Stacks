module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.FromThickeningMorphism
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Extension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Finiteness conditions in a flat deformation diagram

Both horizontal morphisms of a flat deformation diagram are automatically locally of finite type,
and the ambient one is locally of finite presentation: the ambient source is locally of finite
presentation over the ambient base and the ambient target is locally of finite type over it, and
the special-fibre morphism is a base change of the ambient one. A flat deformation diagram is
therefore in particular a cartesian, locally finite type morphism of thickenings, to which the
results of Tag 0BPG apply.

## Main definitions

* `Stacks.Thickenings.FlatDeformationDiagram.toCartesianFiniteTypeMorphism`: the underlying
  cartesian, locally finite type morphism of thickenings.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.locallyOfFiniteType_f'`
* `Stacks.Thickenings.FlatDeformationDiagram.locallyOfFiniteType_f`
* `Stacks.Thickenings.FlatDeformationDiagram.locallyOfFinitePresentation_f'`
* `Stacks.Thickenings.FlatDeformationDiagram.locallyOfFinitePresentation_f`

## References

* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings.FlatDeformationDiagram

variable (D : FlatDeformationDiagram.{u})

/-- The ambient morphism of a flat deformation diagram is locally of finite type. -/
theorem locallyOfFiniteType_f' : LocallyOfFiniteType D.f' :=
  have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
  locallyOfFiniteType_of_comp D.f' D.g'

/-- The ambient morphism of a flat deformation diagram is locally of finite presentation. -/
theorem locallyOfFinitePresentation_f' : LocallyOfFinitePresentation D.f' :=
  have : LocallyOfFiniteType D.g' := D.finiteType_Y'
  have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
  locallyOfFinitePresentation_of_comp D.f' D.g'

/-- The special-fibre morphism of a flat deformation diagram is locally of finite type. -/
theorem locallyOfFiniteType_f : LocallyOfFiniteType D.f :=
  MorphismProperty.of_isPullback D.isPullback_f D.locallyOfFiniteType_f'

/-- The special-fibre morphism of a flat deformation diagram is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_f : LocallyOfFinitePresentation D.f :=
  MorphismProperty.of_isPullback D.isPullback_f D.locallyOfFinitePresentation_f'

/-- The underlying cartesian, locally finite type morphism of thickenings of a flat deformation
diagram. -/
noncomputable def toCartesianFiniteTypeMorphism : CartesianFiniteTypeMorphism.{u} where
  X := D.X
  X' := D.X'
  Y := D.Y
  Y' := D.Y'
  i := D.iX
  j := D.iY
  morphism := D.arrowHom
  sourceThickening := D.iX_thickening
  targetThickening := D.iY_thickening
  locallyOfFiniteType_left := D.locallyOfFiniteType_f
  locallyOfFiniteType_right := D.locallyOfFiniteType_f'
  cartesian := D.isPullback_f.flip

/-- The special-fibre morphism of `D.toCartesianFiniteTypeMorphism` is `D.f`. -/
@[simp]
theorem toCartesianFiniteTypeMorphism_f : D.toCartesianFiniteTypeMorphism.f = D.f := rfl

/-- The ambient morphism of `D.toCartesianFiniteTypeMorphism` is `D.f'`. -/
@[simp]
theorem toCartesianFiniteTypeMorphism_f' : D.toCartesianFiniteTypeMorphism.f' = D.f' := rfl

end Stacks.Thickenings.FlatDeformationDiagram

end
