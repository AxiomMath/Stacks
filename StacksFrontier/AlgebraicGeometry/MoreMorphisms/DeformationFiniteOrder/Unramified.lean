module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Reduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.FiberCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Fibers
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Unramifiedness along a finite-order deformation

In either of the two standing deformation situations the morphism between the special fibres is
unramified if and only if its ambient deformation is.

One direction is base change: unramifiedness is stable under base change, and the special-fibre
morphism is the base change of its deformation along the base thickening. The other direction is
the fibrewise criterion: the ambient morphism is locally of finite type, and each of its fibres
is a fibre of the special-fibre morphism, the deformation changing neither the fibres nor the
residue fields of the target.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.unramified_iff`: **Stacks 0CF4**, unramified case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.unramified_iff`: **Stacks 06AG**,
  unramified case.

## Implementation notes

The fibrewise criterion `AlgebraicGeometry.unramified_of_fibres` asks for each fibre to be a
coproduct of spectra of finite separable extensions of the residue field, which is the same
condition as unramifiedness of the fibre by
`AlgebraicGeometry.unramified_iff_iso_coproduct_spectra_finite_separable`. Unramifiedness of the
fibre is what the deformation provides, through
`Stacks.Thickenings.prop_fiberToSpecResidueField_iff_of_isPullback`, so the decomposition is
obtained from that equivalence rather than transported by hand across the residue-field
isomorphism.

Local finite type of the ambient morphism comes from local finite presentation over the ambient
base in the flat deformation diagram, and from the local-finite-type case of Tag 06AG in the
cartesian finite-order one, where only the special-fibre morphism is known to be locally of
finite type — which it is, being unramified.

## References

* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- If `f` is the base change of a locally finite type `f'` along a thickening `j`, then
unramifiedness of `f` implies that of `f'`. -/
private theorem unramified_of_isPullback_of_isThickening {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'} [LocallyOfFiniteType f'] (hj : IsThickening j)
    (h : IsPullback i f f' j) (hf : Unramified f) : Unramified f' := by
  have : MorphismProperty.RespectsIso (@Unramified.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine unramified_of_fibres f' fun y' => ?_
  obtain ⟨y, rfl⟩ := hj.2 y'
  exact (unramified_iff_iso_coproduct_spectra_finite_separable
    (Y'.residueField (j y)) (f'.fiberToSpecResidueField (j y))).1
    ((prop_fiberToSpecResidueField_iff_of_isPullback hj h (@Unramified.{u}) y).1
      (MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) hf))

/-- Unramifiedness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "unramified"]
theorem FlatDeformationDiagram.unramified_iff (D : FlatDeformationDiagram.{u}) :
    Unramified D.f ↔ Unramified D.f' := by
  refine ⟨fun hf => ?_, fun hf' =>
    unramified_isStableUnderBaseChange.of_isPullback D.isPullback_f hf'⟩
  have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
  have : LocallyOfFiniteType D.f' := locallyOfFiniteType_of_comp D.f' D.g'
  exact unramified_of_isPullback_of_isThickening D.iY_thickening D.isPullback_f hf

/-- **Stacks 06AG, unramified case.** Unramifiedness is invariant under a cartesian finite-order
deformation with flat ambient source. -/
@[stacks 06AG "unramified"]
theorem CartesianFiniteOrderDeformationDiagram.unramified_iff
    (D : CartesianFiniteOrderDeformationDiagram.{u}) : Unramified D.f ↔ Unramified D.f' := by
  refine ⟨fun hf => ?_, property_of_baseChange @Unramified.{u} D⟩
  have : LocallyOfFiniteType D.f' := D.locallyOfFiniteType_iff.1 inferInstance
  exact unramified_of_isPullback_of_isThickening D.iY_thickening D.isPullback_f hf

end Stacks.Thickenings

end
