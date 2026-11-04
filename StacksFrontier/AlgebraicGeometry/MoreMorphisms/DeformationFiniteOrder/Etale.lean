module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FlatFibers
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Étaleness along a finite-order deformation

In either of the two standing deformation situations the morphism between the special fibres is
étale if and only if its ambient deformation is.

One direction is base change: the special-fibre morphism is the base change of its deformation
along the base thickening, and étaleness is stable under base change. The other direction is the
fibrewise criterion for étaleness: the ambient morphism is flat, because flatness is invariant
under the deformation, and locally of finite presentation, because it is so over the ambient base
while the ambient target is locally of finite type there; and each of its fibres is a fibre of
the special-fibre morphism, hence étale over the residue field of its base point.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.etale_iff`: **Stacks 0CF4**, étale case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.etale_iff`: **Stacks 06AG**, étale
  case. Here local finite presentation of the ambient morphism comes from the corresponding case
  of the same lemma instead, the ambient source not being assumed locally of finite presentation
  over the ambient base.

## Implementation notes

The fibrewise criterion `AlgebraicGeometry.etale_of_flat_of_fibers_finite_separable` (Tag 02GM)
asks for each fibre to be a coproduct of spectra of finite separable extensions of the residue
field, which is the same condition as étaleness of the fibre by
`AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable` (Tag 03PC over a field).
Étaleness of the fibre is what the deformation provides, so the decomposition is obtained from
that equivalence rather than transported by hand.

## References

* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
* [Stacks Project, Tag 02GM](https://stacks.math.columbia.edu/tag/02GM)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- If `f'` is flat and locally of finite presentation, and `f` is étale and the base change of
`f'` along a thickening, then `f'` is étale. -/
private theorem etale_of_isPullback_of_flat {X Y X' Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} {j : Y ⟶ Y'} (hj : IsThickening j) (h : IsPullback i f f' j) (hf : Etale f)
    [Flat f'] [LocallyOfFinitePresentation f'] : Etale f' := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine etale_of_flat_of_fibers_finite_separable f' fun y' => ?_
  obtain ⟨y, rfl⟩ := hj.2 y'
  refine (etale_iff_iso_coproduct_spectra_finite_separable (Y'.residueField (j y))
    (f'.fiberToSpecResidueField (j y))).1 ?_
  exact (prop_fiberToSpecResidueField_iff_of_isPullback hj h (@Etale.{u}) y).1
    (MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) hf)

/-- Étaleness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "etale"]
theorem FlatDeformationDiagram.etale_iff (D : FlatDeformationDiagram.{u}) :
    Etale D.f ↔ Etale D.f' := by
  constructor
  · intro hf
    have : LocallyOfFiniteType D.g' := D.finiteType_Y'
    have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
    have : LocallyOfFinitePresentation D.f' := locallyOfFinitePresentation_of_comp D.f' D.g'
    have : Flat D.f' := D.flat_iff.1 inferInstance
    exact etale_of_isPullback_of_flat D.iY_thickening D.isPullback_f hf
  · intro hf'
    exact MorphismProperty.of_isPullback (D.isPullback_X.of_bot D.comm_f D.isPullback_Y) hf'

/-- **Stacks 06AG, étale case.** Étaleness is invariant under a cartesian finite-order
deformation with flat ambient source. -/
@[stacks 06AG "etale"]
theorem CartesianFiniteOrderDeformationDiagram.etale_iff
    (D : CartesianFiniteOrderDeformationDiagram.{u}) : Etale D.f ↔ Etale D.f' := by
  constructor
  · intro hf
    have : LocallyOfFinitePresentation D.f' := D.locallyOfFinitePresentation_iff.1 inferInstance
    have : Flat D.f' := D.flat_iff.1 inferInstance
    exact etale_of_isPullback_of_flat D.iY_thickening D.isPullback_f hf
  · exact CartesianFiniteOrderDeformationDiagram.property_of_baseChange @Etale.{u} D

end Stacks.Thickenings

end
