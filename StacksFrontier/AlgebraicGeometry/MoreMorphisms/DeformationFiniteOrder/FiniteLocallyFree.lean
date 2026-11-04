module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Affine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.FiniteType
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Flat

/-!
# Finite local freeness along a finite-order deformation

In a cartesian finite-order deformation diagram, and likewise in a flat deformation diagram, the
morphism `f` of closed subschemes is finite locally free exactly when its ambient deformation `f'`
is, and the two then have the same rank at corresponding points. Being finite locally free is
spelled as the conjunction of `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.Flat` and
`AlgebraicGeometry.LocallyOfFinitePresentation` (Stacks Tag 02KB), and the rank is
`AlgebraicGeometry.Scheme.Hom.finrank`.

## Main results

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.finrank_eq`: the rank of `f` at a
  point of the target equals the rank of `f'` at its image.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isFiniteLocallyFree_iff`: `f` is
  finite locally free if and only if `f'` is.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isFiniteLocallyFreeOfRank_iff`: `f` is
  finite locally free of rank `d` if and only if `f'` is.
* `Stacks.Thickenings.FlatDeformationDiagram.finrank_eq`: the rank of `f` at a point of the target
  equals the rank of `f'` at its image.
* `Stacks.Thickenings.FlatDeformationDiagram.isFiniteLocallyFree_iff`: `f` is finite locally free
  if and only if `f'` is.
* `Stacks.Thickenings.FlatDeformationDiagram.isFiniteLocallyFreeOfRank_iff`: `f` is finite locally
  free of rank `d` if and only if `f'` is.
* `Stacks.Thickenings.FlatDeformationDiagram.finiteLocallyFree_iff`: the conjunction of the two
  previous equivalences.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Finite local freeness of rank `d` transfers along `iY` once finite local freeness does and ranks
agree at corresponding points. -/
private theorem isFiniteLocallyFreeOfRank_iff_of_finrank_eq {X Y X' Y' : Scheme} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (iY : Y ⟶ Y') (hs : ∀ y', ∃ y, iY y = y')
    (h : (IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f) ↔
      (IsFinite f' ∧ Flat f' ∧ LocallyOfFinitePresentation f'))
    (hrank : Flat f' → IsFinite f' → ∀ y, f.finrank y = f'.finrank (iY y)) (d : ℕ) :
    (IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧ ∀ y, f.finrank y = d) ↔
      (IsFinite f' ∧ Flat f' ∧ LocallyOfFinitePresentation f' ∧ ∀ y', f'.finrank y' = d) := by
  constructor
  · rintro ⟨hfin, hflat, hfp, hrk⟩
    obtain ⟨hfin', hflat', hfp'⟩ := h.1 ⟨hfin, hflat, hfp⟩
    refine ⟨hfin', hflat', hfp', fun y' ↦ ?_⟩
    obtain ⟨y, rfl⟩ := hs y'
    exact (hrank hflat' hfin' y).symm.trans (hrk y)
  · rintro ⟨hfin', hflat', hfp', hrk'⟩
    obtain ⟨hfin, hflat, hfp⟩ := h.2 ⟨hfin', hflat', hfp'⟩
    exact ⟨hfin, hflat, hfp, fun y ↦ (hrank hflat' hfin' y).trans (hrk' (iY y))⟩

namespace CartesianFiniteOrderDeformationDiagram

/-- The rank of `f` at a point of the target agrees with the rank of its ambient deformation `f'`
at the image of that point. -/
theorem finrank_eq (D : CartesianFiniteOrderDeformationDiagram.{u})
    [Flat D.f'] [IsFinite D.f'] (y : D.Y) :
    D.f.finrank y = D.f'.finrank (D.iY y) :=
  Scheme.Hom.finrank_of_isPullback D.iX D.f D.f' D.iY D.isPullback_f y

/-- In a cartesian finite-order deformation diagram, `f` is finite, flat and locally of finite
presentation if and only if `f'` is. -/
@[stacks 06AG "finite_locally_free"]
theorem isFiniteLocallyFree_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    (IsFinite D.f ∧ Flat D.f ∧ LocallyOfFinitePresentation D.f) ↔
      (IsFinite D.f' ∧ Flat D.f' ∧ LocallyOfFinitePresentation D.f') := by
  rw [D.isFinite_iff, D.flat_iff, D.locallyOfFinitePresentation_iff]

/-- In a cartesian finite-order deformation diagram, `f` is finite locally free of rank `d` if and
only if `f'` is. -/
@[stacks 06AG "finite_locally_free_of_rank"]
theorem isFiniteLocallyFreeOfRank_iff (D : CartesianFiniteOrderDeformationDiagram.{u})
    (d : ℕ) :
    (IsFinite D.f ∧ Flat D.f ∧ LocallyOfFinitePresentation D.f ∧
        ∀ y : D.Y, D.f.finrank y = d) ↔
      (IsFinite D.f' ∧ Flat D.f' ∧ LocallyOfFinitePresentation D.f' ∧
        ∀ y' : D.Y', D.f'.finrank y' = d) := by
  exact isFiniteLocallyFreeOfRank_iff_of_finrank_eq D.f D.f' D.iY D.iY_thickening.2
    D.isFiniteLocallyFree_iff (fun _ _ ↦ D.finrank_eq) d

end CartesianFiniteOrderDeformationDiagram

namespace FlatDeformationDiagram

/-- The rank of `f` at a point of the target agrees with the rank of its ambient deformation `f'`
at the image of that point. -/
theorem finrank_eq (D : FlatDeformationDiagram.{u}) [Flat D.f'] [IsFinite D.f'] (y : D.Y) :
    D.f.finrank y = D.f'.finrank (D.iY y) :=
  Scheme.Hom.finrank_of_isPullback D.iX D.f D.f' D.iY D.isPullback_f y

/-- In a flat deformation diagram, `f` is finite, flat and locally of finite presentation if and
only if `f'` is. -/
theorem isFiniteLocallyFree_iff (D : FlatDeformationDiagram.{u}) :
    (IsFinite D.f ∧ Flat D.f ∧ LocallyOfFinitePresentation D.f) ↔
      (IsFinite D.f' ∧ Flat D.f' ∧ LocallyOfFinitePresentation D.f') := by
  rw [D.isFinite_iff, D.flat_iff]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, D.locallyOfFinitePresentation_f'⟩,
    fun h ↦ ⟨h.1, h.2.1, D.locallyOfFinitePresentation_f⟩⟩

/-- In a flat deformation diagram, `f` is finite locally free of rank `d` if and only if `f'`
is. -/
theorem isFiniteLocallyFreeOfRank_iff (D : FlatDeformationDiagram.{u}) (d : ℕ) :
    (IsFinite D.f ∧ Flat D.f ∧ LocallyOfFinitePresentation D.f ∧
        ∀ y : D.Y, D.f.finrank y = d) ↔
      (IsFinite D.f' ∧ Flat D.f' ∧ LocallyOfFinitePresentation D.f' ∧
        ∀ y' : D.Y', D.f'.finrank y' = d) := by
  exact isFiniteLocallyFreeOfRank_iff_of_finrank_eq D.f D.f' D.iY D.iY_thickening.2
    D.isFiniteLocallyFree_iff (fun _ _ ↦ D.finrank_eq) d

/-- Being finite locally free, and being finite locally free of a given rank `d`, are each
invariant under a flat deformation diagram. -/
@[stacks 0CF4 "finite_locally_free"]
theorem finiteLocallyFree_iff (D : FlatDeformationDiagram.{u}) :
    ((IsFinite D.f ∧ Flat D.f ∧ LocallyOfFinitePresentation D.f) ↔
      (IsFinite D.f' ∧ Flat D.f' ∧ LocallyOfFinitePresentation D.f')) ∧
    ∀ d : ℕ, (IsFinite D.f ∧ Flat D.f ∧ LocallyOfFinitePresentation D.f ∧
        ∀ y : D.Y, D.f.finrank y = d) ↔
      (IsFinite D.f' ∧ Flat D.f' ∧ LocallyOfFinitePresentation D.f' ∧
        ∀ y' : D.Y', D.f'.finrank y' = d) :=
  ⟨D.isFiniteLocallyFree_iff, D.isFiniteLocallyFreeOfRank_iff⟩

end FlatDeformationDiagram

end Stacks.Thickenings

end
