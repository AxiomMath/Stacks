module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# The second arrow of the conormal sequence of an immersion

Let `i : Z ⟶ X` be an immersion of algebraic spaces over an algebraic space `B`, with structure
morphism `b : X ⟶ B`.  The second arrow of the canonical sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
of Stacks 05ZA is the comparison map `c_i` of Stacks 04CX for the commutative square with top
edge `i`, right edge `b`, left edge `i ≫ b` and bottom edge the identity of `B`.

That comparison map is `AlgebraicGeometry.Space.pullbackDifferentialsMap`, which is also the
first arrow of the transitivity sequence of Stacks 05Z8.  This file registers it under
Stacks 05ZA, as is done for the corresponding arrow of Stacks 01UZ for schemes.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square.
* [Stacks Project, Tag 05Z8](https://stacks.math.columbia.edu/tag/05Z8), the transitivity
  sequence.
-/

@[expose] public section

add_to_stacks 05ZA "the canonical second arrow `i^*Ω_{X/B} ⟶ Ω_{Z/B}`, the comparison map of
  04CX for the square over the identity of the base"
  AlgebraicGeometry.Space.pullbackDifferentialsMap

end
