module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials

/-!
# Unramified morphisms over a locally Noetherian base

Over a locally Noetherian target the two notions of unramifiedness agree.

## Main results

* `AlgebraicGeometry.unramified_iff_gUnramified` identifies unramified and G-unramified
  morphisms over a locally Noetherian target.

## Implementation notes

Both notions are the conjunction of a finiteness condition with the vanishing of the sheaf of
relative differentials, and over a locally Noetherian target local finite type and local finite
presentation agree.

## References

* [Stacks Project, Tag 04EV](https://stacks.math.columbia.edu/tag/04EV)
* [Stacks Project, Tag 02G5](https://stacks.math.columbia.edu/tag/02G5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Over a locally Noetherian target, a morphism of schemes is unramified if and only if it is
G-unramified. -/
@[stacks 04EV]
theorem unramified_iff_gUnramified {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] :
    Unramified f ↔ GUnramified f := by
  rw [unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials,
    gUnramified_iff_locallyOfFinitePresentation_and_isZero_relativeDifferentials]
  constructor <;> rintro ⟨h, hz⟩ <;> exact ⟨inferInstance, hz⟩

end AlgebraicGeometry
