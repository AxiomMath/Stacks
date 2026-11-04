module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded

/-!
# Bounds on fibre degrees descend along a surjective base change

Let `f' : X' ⟶ Y'` be a base change of a morphism of schemes `f : X ⟶ Y` along a surjective
morphism `Y' ⟶ Y`. Every integer bound on the degrees of the fibres of `f'` is also a bound on the
degrees of the fibres of `f`; in particular universally bounded fibres descend along a surjective
base change.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_of_isPullback_of_surjective`: an integer bounding the
  fibre degrees of `f'` bounds the fibre degrees of `f`.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_isPullback_of_surjective`: if `f'` has
  universally bounded fibres, so does `f`.

## Implementation notes

The statements are given for an arbitrary cartesian square rather than for a chosen pullback
object.

## References

* [Stacks Project, Tag 03J8](https://stacks.math.columbia.edu/tag/03J8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Let `f'` be a base change of `f` along a surjective morphism. An integer bounding the degrees
of the fibres of `f'` also bounds the degrees of the fibres of `f`. -/
@[stacks 03J8 "specified bound"]
theorem boundsFiberDegrees_of_isPullback_of_surjective {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [Surjective g]
    (n : ℤ) (h : BoundsFiberDegrees f' n) : BoundsFiberDegrees f n := by
  intro y
  obtain ⟨y', rfl⟩ := g.surjective y
  obtain ⟨r, hr, hrank⟩ := h y'
  refine ⟨r, hr, ?_⟩
  let : Algebra ↑(Y.residueField (g y')) ↑(Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  have hsq : IsPullback (pullback.map _ _ _ _ g' (Spec.map (g.residueFieldMap y')) g
        sq.w.symm (by simp))
      (f'.fiberToSpecResidueField y') (f.fiberToSpecResidueField (g y'))
      (Spec.map (CommRingCat.ofHom
        (algebraMap ↑(Y.residueField (g y')) ↑(Y'.residueField y')))) :=
    isPullback_fiberToSpecResidueField_of_isPullback sq y'
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_isPullback_of_field
    (K := ↑(Y.residueField (g y'))) (L := ↑(Y'.residueField y')) hsq r hrank

/-- Let `f'` be a base change of `f` along a surjective morphism. If `f'` has universally bounded
fibres, then so does `f`. -/
@[stacks 03J8 "universally bounded fibres"]
theorem hasUniversallyBoundedFibers_of_isPullback_of_surjective {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [Surjective g] (h : HasUniversallyBoundedFibers f') : HasUniversallyBoundedFibers f := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, boundsFiberDegrees_of_isPullback_of_surjective sq n hn⟩

end AlgebraicGeometry

end
