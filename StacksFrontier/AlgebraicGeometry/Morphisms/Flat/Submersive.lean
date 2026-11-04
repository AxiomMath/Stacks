module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact surjective flat morphisms are submersive

A quasi-compact, surjective, flat morphism of schemes is a quotient map on underlying spaces, so a
subset of its target is open, respectively closed, exactly when its preimage is open, respectively
closed.

## Main results

* `AlgebraicGeometry.Flat.isOpen_iff_isOpen_preimage`: a subset of the target is open if and only
  if its preimage is open.
* `AlgebraicGeometry.Flat.isClosed_iff_isClosed_preimage`: a subset of the target is closed if and
  only if its preimage is closed.

## References

* [Stacks Project, Tag 02JY](https://stacks.math.columbia.edu/tag/02JY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f]

/-- A subset of the target of a quasi-compact, surjective, flat morphism of schemes is open if and
only if its preimage is open. -/
@[stacks 02JY "the open half: `T` is open if and only if `f ⁻¹' T` is open"]
public theorem Flat.isOpen_iff_isOpen_preimage {T : Set Y} : IsOpen T ↔ IsOpen (f ⁻¹' T) :=
  (Flat.isQuotientMap_of_surjective f).isCoinducing.isOpen_preimage.symm

/-- A subset of the target of a quasi-compact, surjective, flat morphism of schemes is closed if
and only if its preimage is closed. -/
@[stacks 02JY "the closed half: `T` is closed if and only if `f ⁻¹' T` is closed"]
public theorem Flat.isClosed_iff_isClosed_preimage {T : Set Y} :
    IsClosed T ↔ IsClosed (f ⁻¹' T) :=
  (Flat.isQuotientMap_of_surjective f).isCoinducing.isClosed_preimage.symm

end AlgebraicGeometry

end
