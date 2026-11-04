module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram

/-!
# Local quasi-finiteness along a finite-order deformation

In a flat deformation diagram the morphism between the special fibres is locally quasi-finite
if and only if its ambient deformation is.

Local quasi-finiteness in the sense of the Stacks project is the conjunction of two conditions:
being locally of finite type, and having discrete set-theoretic fibres. The first transfers
because `X' ⟶ S'` is locally of finite presentation, hence locally of finite type, and local
finite type descends to the special fibre by base change; the second transfers because the
scheme-theoretic fibres of the two morphisms over corresponding points are isomorphic, and the
target thickening is surjective on points, so every fibre of the deformation is accounted for.

## Main results

* `Stacks.Thickenings.FlatDeformationDiagram.locallyQuasiFinite_conditions_iff`

## Implementation notes

As in the definition of quasi-finiteness at a point, local quasi-finiteness bundles the local
finite-type condition and the fibre-isolation condition; these are Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`
respectively, and the statement below is the conjunction of the two.

## References

* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Local quasi-finiteness is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "locally_quasi_finite"]
theorem FlatDeformationDiagram.locallyQuasiFinite_conditions_iff
    (D : FlatDeformationDiagram.{u}) :
    (LocallyOfFiniteType D.f ∧ LocallyQuasiFinite D.f) ↔
      (LocallyOfFiniteType D.f' ∧ LocallyQuasiFinite D.f') := by
  have : LocallyOfFinitePresentation (D.f' ≫ D.g') := D.finitePresentation_X'
  have hcomp : LocallyOfFiniteType (D.f' ≫ D.g') := inferInstance
  have hcomp' : LocallyOfFiniteType (D.f ≫ D.g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback D.isPullback_X hcomp
  have hft : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f D.g
  have hft' : LocallyOfFiniteType D.f' := locallyOfFiniteType_of_comp D.f' D.g'
  have hfiber (y : D.Y) : _root_.IsDiscrete (D.f ⁻¹' {y}) ↔
      _root_.IsDiscrete (D.f' ⁻¹' {D.iY y}) := by
    rw [isDiscrete_iff_discreteTopology, isDiscrete_iff_discreteTopology]
    let m := pullback.map D.f (D.Y.fromSpecResidueField y) D.f'
      (D.Y'.fromSpecResidueField (D.iY y)) D.iX
      (Spec.map (D.iY.residueFieldMap y)) D.iY D.comm_f.symm (by simp)
    have : IsIso m := D.isIso_fiberMap y
    exact ((D.f.fiberHomeo y).discreteTopology_iff.symm.trans
      m.homeomorph.discreteTopology_iff).trans
        (D.f'.fiberHomeo (D.iY y)).discreteTopology_iff
  have hqf : LocallyQuasiFinite D.f ↔ LocallyQuasiFinite D.f' := by
    rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton,
      locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
    refine ⟨fun h y' => ?_, fun h y => (hfiber y).mpr (h _)⟩
    obtain ⟨y, rfl⟩ := D.iY_thickening.2 y'
    exact (hfiber y).mp (h y)
  exact ⟨fun h => ⟨hft', hqf.mp h.2⟩, fun h => ⟨hft, hqf.mpr h.2⟩⟩

end Stacks.Thickenings

end
