module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Ring
public import StacksFrontier.AlgebraicGeometry.Properties.LocalRingProperty

/-!
# Seminormal and absolutely weakly normal schemes

A scheme is seminormal, respectively absolutely weakly normal, when every point has an affine
open neighbourhood whose ring of sections has the corresponding ring-theoretic property.
Both conditions imply reducedness.

## Main definitions

* `AlgebraicGeometry.IsSeminormal` is the predicate that a scheme is seminormal.
* `AlgebraicGeometry.IsAbsolutelyWeaklyNormal` is the predicate that a scheme is absolutely
  weakly normal.

## Main results

* `AlgebraicGeometry.seminormal_isReduced` states that a seminormal scheme is reduced.
* `AlgebraicGeometry.absolutelyWeaklyNormal_isReduced` states that an absolutely weakly
  normal scheme is reduced.

## Implementation notes

Both predicates specialize the general affine-local ring-property predicate
`AlgebraicGeometry.IsLocally`. They are abbreviations, so clients can use the pointwise
affine neighbourhood formulation directly. Reducedness of schemes is expressed by
`AlgebraicGeometry.IsReduced`; the corresponding statements for rings, which use Mathlib's
`IsReduced` class, are recorded separately alongside the ring-theoretic definitions.

## References

* [Stacks Project, Tag 0EUN](https://stacks.math.columbia.edu/tag/0EUN)
* [Stacks Project, Tag 0EUQ](https://stacks.math.columbia.edu/tag/0EUQ)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A scheme is seminormal if every point has an affine open neighbourhood whose ring of
sections is seminormal. -/
@[stacks 0EUN "part (1)"]
abbrev IsSeminormal (X : Scheme.{u}) : Prop :=
  IsLocally (fun (R : Type u) [CommRing R] => IsSeminormalRing R) X

/-- A scheme is absolutely weakly normal if every point has an affine open neighbourhood
whose ring of sections is absolutely weakly normal. -/
@[stacks 0EUN "part (2)"]
abbrev IsAbsolutelyWeaklyNormal (X : Scheme.{u}) : Prop :=
  IsLocally (fun (R : Type u) [CommRing R] => IsAbsolutelyWeaklyNormalRing R) X

/-- **Stacks Project, Tag 0EUQ.** A seminormal scheme is reduced. -/
@[stacks 0EUQ "seminormal schemes"]
theorem seminormal_isReduced {X : Scheme.{u}} (hX : IsSeminormal X) :
    IsReduced X :=
  (isReduced_iff_isLocally_isReduced X).2 fun x =>
    let ⟨U, hx, hU⟩ := hX x
    ⟨U, hx, seminormalRing_isReduced hU⟩

/-- **Stacks Project, Tag 0EUQ.** An absolutely weakly normal scheme is reduced. -/
@[stacks 0EUQ "absolutely weakly normal schemes"]
theorem absolutelyWeaklyNormal_isReduced {X : Scheme.{u}}
    (hX : IsAbsolutelyWeaklyNormal X) : IsReduced X :=
  seminormal_isReduced fun x =>
    let ⟨U, hx, hU⟩ := hX x
    ⟨U, hx, hU.1⟩

end AlgebraicGeometry

end
