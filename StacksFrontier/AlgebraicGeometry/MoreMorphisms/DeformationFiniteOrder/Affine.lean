module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Reduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.FiniteType
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Affineness along a finite-order deformation

In a cartesian finite-order deformation diagram the morphism `f` of closed subschemes is affine
exactly when its ambient deformation `f'` is, and the same holds for the two properties built
from affineness: integrality and finiteness.

One direction is base change in each case. For the other, the point is that an open subscheme of
the ambient scheme of a thickening is affine as soon as its preimage in the closed subscheme is:
the restricted inclusion is again a thickening, and a thickening of an affine scheme is affine.
Applied to the preimage of an affine open of the ambient target, this turns affineness of `f`
into affineness of `f'`. Integrality is then universal closedness together with affineness, and
finiteness is integrality together with local finite type, so both follow from the cases of this
tag that are already available.

The same argument applies verbatim to a flat deformation diagram, where it gives the affine and
finite cases of Tag 0CF4: affineness only uses that the two inclusions are thickenings forming a
commutative square, and the two horizontal morphisms of a flat deformation diagram are locally of
finite type.

## Main results

* `Stacks.Thickenings.isAffineOpen_of_isThickening`
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isAffineHom_iff`: **Stacks 06AG**,
  affine case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isIntegralHom_iff`:
  **Stacks 06AG**, integral case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isFinite_iff`: **Stacks 06AG**,
  finite case.
* `Stacks.Thickenings.FlatDeformationDiagram.isAffineHom_iff`: **Stacks 0CF4**, affine case.
* `Stacks.Thickenings.FlatDeformationDiagram.isIntegralHom_iff`
* `Stacks.Thickenings.FlatDeformationDiagram.isFinite_iff`: **Stacks 0CF4**, finite case.

## Implementation notes

The decompositions of integrality and of finiteness are Mathlib's
`AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom` and
`AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`, which are Stacks Tags
01WM and 01WN read as characterizations.

## References

* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
* [Stacks Project, Tag 01WN](https://stacks.math.columbia.edu/tag/01WN)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- An open subscheme of the ambient scheme of a thickening is affine as soon as its preimage in
the closed subscheme is: the restriction of the inclusion to that open is again a closed
immersion and still surjective, hence a thickening with affine source. -/
theorem isAffineOpen_of_isThickening {X X' : Scheme.{u}} {i : X ⟶ X'} (hi : IsThickening i)
    {W : X'.Opens} (hW : IsAffineOpen (i ⁻¹ᵁ W)) : IsAffineOpen W :=
  have : IsAffine (i ⁻¹ᵁ W).toScheme := hW
  have : Surjective i := ⟨hi.2⟩
  isAffine_of_isThickening
    (i := i ∣_ W)
    ⟨IsZariskiLocalAtTarget.restrict hi.1 W,
      (surjective_iff _).mp (IsZariskiLocalAtTarget.restrict ‹Surjective i› W)⟩

/-- In a commutative square whose two vertical morphisms are thickenings, the top morphism is
affine as soon as the bottom one is. -/
private theorem isAffineHom_of_isThickening {X X' Y Y' : Scheme.{u}} {iX : X ⟶ X'}
    {iY : Y ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'} (hiX : IsThickening iX) (hiY : IsThickening iY)
    (h : iX ≫ f' = f ≫ iY) [IsAffineHom f] : IsAffineHom f' := by
  have _ : IsClosedImmersion iY := hiY.1
  refine ⟨fun V' hV' => isAffineOpen_of_isThickening hiX ?_⟩
  have heq : iX ⁻¹ᵁ (f' ⁻¹ᵁ V') = f ⁻¹ᵁ (iY ⁻¹ᵁ V') := by
    simpa using (congrArg (fun g : X ⟶ Y' => g ⁻¹ᵁ V') h)
  rw [heq]
  exact (hV'.preimage iY).preimage f

namespace CartesianFiniteOrderDeformationDiagram

/-- **Stacks 06AG, affine case.** Affineness is invariant under a cartesian finite-order
deformation with flat ambient source. -/
@[stacks 06AG "affine"]
theorem isAffineHom_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    IsAffineHom D.f ↔ IsAffineHom D.f' := by
  exact ⟨fun hf => isAffineHom_of_isThickening D.iX_thickening D.iY_thickening
    D.f_thickening_comm.symm, property_of_baseChange @IsAffineHom.{u} D⟩

/-- **Stacks 06AG, integral case.** Integrality is invariant under a cartesian finite-order
deformation with flat ambient source: it is universal closedness together with affineness. -/
@[stacks 06AG "integral"]
theorem isIntegralHom_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    IsIntegralHom D.f ↔ IsIntegralHom D.f' := by
  let φ : Arrow.mk D.iX ⟶ Arrow.mk D.iY := Arrow.homMk D.f D.f' D.f_thickening_comm
  have huc : UniversallyClosed D.f ↔ UniversallyClosed D.f' :=
    universallyClosed_left_iff_right φ D.iX_thickening D.iY_thickening
  rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom,
    IsIntegralHom.iff_universallyClosed_and_isAffineHom, huc, D.isAffineHom_iff]

/-- **Stacks 06AG, finite case.** Finiteness is invariant under a cartesian finite-order
deformation with flat ambient source: it is integrality together with local finite type. -/
@[stacks 06AG "finite"]
theorem isFinite_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    IsFinite D.f ↔ IsFinite D.f' := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType,
    IsFinite.iff_isIntegralHom_and_locallyOfFiniteType, D.isIntegralHom_iff,
    D.locallyOfFiniteType_iff]

end CartesianFiniteOrderDeformationDiagram

namespace FlatDeformationDiagram

/-- Affineness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "affine"]
theorem isAffineHom_iff (D : FlatDeformationDiagram.{u}) :
    IsAffineHom D.f ↔ IsAffineHom D.f' := by
  exact ⟨fun hf => isAffineHom_of_isThickening D.iX_thickening D.iY_thickening D.comm_f,
    fun hf' => MorphismProperty.of_isPullback D.isPullback_f hf'⟩

/-- Integrality is invariant under a flat deformation diagram: it is universal closedness
together with affineness. -/
theorem isIntegralHom_iff (D : FlatDeformationDiagram.{u}) :
    IsIntegralHom D.f ↔ IsIntegralHom D.f' := by
  rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom,
    IsIntegralHom.iff_universallyClosed_and_isAffineHom, D.universallyClosed_iff,
    D.isAffineHom_iff]

/-- Finiteness is invariant under a flat deformation diagram: it is integrality together with
local finite type, and both horizontal morphisms are locally of finite type. -/
@[stacks 0CF4 "finite"]
theorem isFinite_iff (D : FlatDeformationDiagram.{u}) : IsFinite D.f ↔ IsFinite D.f' := by
  have := D.locallyOfFiniteType_f
  have := D.locallyOfFiniteType_f'
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType,
    IsFinite.iff_isIntegralHom_and_locallyOfFiniteType, D.isIntegralHom_iff]
  exact ⟨fun h => ⟨h.1, inferInstance⟩, fun h => ⟨h.1, inferInstance⟩⟩

end FlatDeformationDiagram

end Stacks.Thickenings

end
