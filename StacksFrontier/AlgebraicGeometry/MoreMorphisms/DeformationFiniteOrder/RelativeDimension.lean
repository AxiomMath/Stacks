module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.FiniteType

/-!
# Relative dimension along a finite-order deformation

In a cartesian finite-order deformation diagram, and likewise in a flat deformation diagram, the
morphism `f` of closed subschemes is locally of finite type of relative dimension `d` exactly when
its ambient deformation `f'` is. The condition on `f` is stated as
`∃ _ : LocallyOfFiniteType f, RelativeDimension f d`.

## Main definitions

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.fiberHomeomorph`: the homeomorphism
  between the fibre of `f` over a point and the fibre of `f'` over its image.
* `Stacks.Thickenings.FlatDeformationDiagram.fiberHomeomorph`: the homeomorphism between the fibre
  of `f` over a point and the fibre of `f'` over its image.

## Main results

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.relativeDimension_iff`: `f` is
  locally of finite type of relative dimension `d` if and only if `f'` is.
* `Stacks.Thickenings.FlatDeformationDiagram.relativeDimension_iff`: `f` is locally of finite type
  of relative dimension `d` if and only if `f'` is.

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Being equidimensional of a given topological Krull dimension transfers along a homeomorphism. -/
private theorem equidimensional_and_krullDim_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) {d : WithBot ℕ∞}
    (h : TopologicalSpace.Equidimensional B ∧ topologicalKrullDim B = d) :
    TopologicalSpace.Equidimensional A ∧ topologicalKrullDim A = d :=
  ⟨TopologicalSpace.Equidimensional.of_homeomorph e h.1,
    e.isHomeomorph.topologicalKrullDim_eq.trans h.2⟩

namespace CartesianFiniteOrderDeformationDiagram

/-- The fibre of `f` over a point of the target and the fibre of its ambient deformation over the
image of that point are homeomorphic. -/
noncomputable def fiberHomeomorph (D : CartesianFiniteOrderDeformationDiagram.{u}) (y : D.Y) :
    D.f.fiber y ≃ₜ D.f'.fiber (D.iY y) :=
  have := isIso_fiberMapOfIsPullback D.iY_thickening D.isPullback_f y
  Scheme.homeoOfIso (asIso (fiberMapOfIsPullback D.isPullback_f y))

/-- Being locally of finite type of relative dimension `d` is invariant under a cartesian
finite-order deformation with flat ambient source. -/
@[stacks 06AG "relative_dimension"]
theorem relativeDimension_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) (d : ℕ) :
    (∃ _ : LocallyOfFiniteType D.f, RelativeDimension D.f d) ↔
      (∃ _ : LocallyOfFiniteType D.f', RelativeDimension D.f' d) := by
  constructor
  · rintro ⟨hft, hrd⟩
    refine ⟨D.locallyOfFiniteType_iff.1 hft, fun y' hne ↦ ?_⟩
    obtain ⟨y, rfl⟩ := D.iY_thickening.2 y'
    have e := D.fiberHomeomorph y
    exact equidimensional_and_krullDim_of_homeomorph e.symm (hrd y ⟨e.symm hne.some⟩)
  · rintro ⟨hft', hrd'⟩
    refine ⟨D.locallyOfFiniteType_iff.2 hft', fun y hne ↦ ?_⟩
    have e := D.fiberHomeomorph y
    exact equidimensional_and_krullDim_of_homeomorph e (hrd' (D.iY y) ⟨e hne.some⟩)

end CartesianFiniteOrderDeformationDiagram

namespace FlatDeformationDiagram

/-- The fibre of `f` over a point of the target and the fibre of its ambient deformation over the
image of that point are homeomorphic. -/
noncomputable def fiberHomeomorph (D : FlatDeformationDiagram.{u}) (y : D.Y) :
    D.f.fiber y ≃ₜ D.f'.fiber (D.iY y) :=
  Scheme.homeoOfIso (asIso (D.fiberMap y))

/-- Being locally of finite type of relative dimension `d` is invariant under a flat deformation
diagram. -/
@[stacks 0CF4 "relative_dimension"]
theorem relativeDimension_iff (D : FlatDeformationDiagram.{u}) (d : ℕ) :
    (∃ _ : LocallyOfFiniteType D.f, RelativeDimension D.f d) ↔
      (∃ _ : LocallyOfFiniteType D.f', RelativeDimension D.f' d) := by
  constructor
  · rintro ⟨_, hrd⟩
    refine ⟨D.locallyOfFiniteType_f', fun y' hne ↦ ?_⟩
    obtain ⟨y, rfl⟩ := D.iY_thickening.2 y'
    have e := D.fiberHomeomorph y
    exact equidimensional_and_krullDim_of_homeomorph e.symm (hrd y ⟨e.symm hne.some⟩)
  · rintro ⟨_, hrd'⟩
    refine ⟨D.locallyOfFiniteType_f, fun y hne ↦ ?_⟩
    have e := D.fiberHomeomorph y
    exact equidimensional_and_krullDim_of_homeomorph e (hrd' (D.iY y) ⟨e hne.some⟩)

end FlatDeformationDiagram

end Stacks.Thickenings

end
