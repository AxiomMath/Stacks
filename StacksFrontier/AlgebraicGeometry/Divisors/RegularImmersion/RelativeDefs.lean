module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Relative `H₁`-regular immersions

Let `f : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` an immersion.  Over the base `S` the
immersion is called *relatively `H₁`-regular* when `Z ⟶ S` is flat and `i` is an `H₁`-regular
immersion.  This is the relative companion of relative quasi-regularity, which is
`Stacks.AlgebraicGeometry.IsRelativeQuasiRegularImmersion`.

## Main definitions

* `AlgebraicGeometry.IsRelativeH1RegularImmersion`: the predicate above.

## Implementation notes

The predicate is an abbreviation of the conjunction of flatness of the composite `Z ⟶ S` and
`H₁`-regularity of the immersion, so a client may use the two conjuncts directly and no
unfolding API is needed.  The `H₁`-regular condition is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsH1RegularImmersion`, part (3) of Stacks tag 063J.

Part (1) of Stacks tag 063S, relative quasi-regularity, is already in the library as
`Stacks.AlgebraicGeometry.IsRelativeQuasiRegularImmersion`, and carries the tag there; the two
parts are therefore stated in different files.

## References

* [Stacks Project, Tag 063S](https://stacks.math.columbia.edu/tag/063S)
* [Stacks Project, Tag 063J](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- **Part (2) of Stacks tag 063S.**  An immersion into a scheme over a base is a *relative
`H₁`-regular immersion* when the immersed scheme is flat over the base and the immersion is
`H₁`-regular. -/
@[stacks 063S "part (2): relative H₁-regular immersion"]
abbrev IsRelativeH1RegularImmersion {Z X S : Scheme.{u}}
    (f : X ⟶ S) (i : Z ⟶ X) [IsImmersion i] : Prop :=
  Flat (i ≫ f) ∧ IsH1RegularImmersion i

end AlgebraicGeometry

end
