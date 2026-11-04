module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsDifferentials
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality

/-!
# Base change of a family of nodal curves

Let `f : X ⟶ S` be at-worst-nodal of relative dimension one and let `f' : X' ⟶ S'` be an
arbitrary base change of `f`, presented by a cartesian square with top edge `g' : X' ⟶ X` and
bottom edge `g : S' ⟶ S`. Then `f'` is again at-worst-nodal of relative dimension one.

## Main results

* `AlgebraicGeometry.isPullback_comap_subschemeι`: the closed subscheme cut out by the inverse
  image of an ideal sheaf is the fibre product of the closed subscheme it cuts out.
* `AlgebraicGeometry.relativeSingularIdeal_comap_of_isPullback`: formation of the relative
  singular subscheme commutes with base change, phrased for `relativeSingularIdeal`.
* `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne.of_isPullback`: being at-worst-nodal
  of relative dimension one is preserved by an arbitrary base change.

## Implementation notes

The base change is an arbitrary cartesian square rather than Mathlib's chosen pullback object,
and no hypothesis is imposed on `g : S' ⟶ S`.

## References

* [Stacks Project, Tag 0C5B](https://stacks.math.columbia.edu/tag/0C5B)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 01UI](https://stacks.math.columbia.edu/tag/01UI)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02GA](https://stacks.math.columbia.edu/tag/02GA)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The closed subscheme cut out by the inverse image `I.comap g'` of an ideal sheaf `I` on `X`
along an arbitrary morphism `g' : X' ⟶ X` is the fibre product over `X` of `X'` with the closed
subscheme cut out by `I`. -/
public theorem isPullback_comap_subschemeι {X' X : Scheme.{u}} (I : X.IdealSheafData)
    (g' : X' ⟶ X) :
    IsPullback (Scheme.IdealSheafData.subschemeMap _ _ g' (I.le_map_comap g'))
      (I.comap g').subschemeι I.subschemeι g' :=
  (isPullback_of_isClosedImmersion (I.comap g').subschemeι I.subschemeι
    (Scheme.IdealSheafData.subschemeMap _ _ g' (I.le_map_comap g')) g' (by simp)
    (by simp [Scheme.IdealSheafData.ker_subschemeι])).flip

/-- Formation of the relative singular subscheme commutes with base change: in a cartesian
square with right edge `f : X ⟶ S` locally of finite type, left edge `f' : X' ⟶ S'` and top
edge `g' : X' ⟶ X`, the inverse image of `Sing(f)` along `g'` is `Sing(f')`. -/
public theorem relativeSingularIdeal_comap_of_isPullback {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] :
    (relativeSingularIdeal f).comap g' = relativeSingularIdeal f' :=
  fittingIdeal_relativeDifferentials_comap g' f' f g h 1

/-- Let `f : X ⟶ S` be at-worst-nodal of relative dimension one. Then so is any base change
`f' : X' ⟶ S'` of `f`, presented by an arbitrary cartesian square. -/
@[stacks 0C5B]
public theorem IsAtWorstNodalOfRelativeDimensionOne.of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g)
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    IsAtWorstNodalOfRelativeDimensionOne f' := by
  obtain ⟨⟨hsyn, hdim⟩, hsing⟩ := hf
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hsyn
  refine ⟨⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback h hsyn,
    fun x' ↦ (topologicalKrullDimAt_fiber_eq_of_isPullback h x').trans (hdim (g' x'))⟩, ?_⟩
  rw [← relativeSingularIdeal_comap_of_isPullback g' f' f g h]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((isPullback_comap_subschemeι (relativeSingularIdeal f) g').paste_vert h) hsing

end AlgebraicGeometry

end
