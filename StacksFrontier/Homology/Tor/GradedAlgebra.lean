module

public import StacksFrontier.Homology.Tor.GradedAlgebra.Defs
public import StacksFrontier.Homology.Tor.GradedAlgebra.ResolutionProduct
public import StacksFrontier.Homology.Tor.GradedAlgebra.Existence
public import StacksFrontier.Homology.Tor.GradedAlgebra.Functoriality

/-!
# The graded Tor algebra

For a commutative ring `R`, an `R`-algebra `A` and an `R`-algebra `B`, the groups
`Torⁿᴿ(B, A)` form a canonical unital associative `ℤ`-graded `A`-algebra. Its multiplication is
the canonical Tor cross product followed by the map on Tor induced by the multiplication of
`B`, and an `R`-algebra homomorphism `B ⟶ C` induces a homomorphism of these graded algebras.

This file only re-exports its parts `Defs`, `ResolutionProduct`, `Existence`, `Functoriality`.

## Main definitions

* `GradedTor.torPiece` is the `ℤ`-graded family of Tor modules, with zero components in
  negative degrees, and `GradedTor.torPieceMap` its degreewise functoriality.
* `GradedTor.torMultiplication` is the multiplication in nonnegative degrees: the Tor cross
  product followed by the map induced by multiplication on `B`.
* `GradedTor.Algebra` packages the unital graded-algebra operations on this family, and
  `GradedTor.AlgebraHom` a degree-preserving homomorphism of them.
* `GradedTor.canonicalAlgebra` is the graded algebra attached to `B`, and
  `GradedTor.canonicalMap` the graded algebra homomorphism attached to an `R`-algebra map.
* `GradedTor.FunctorialAlgebra` packages the algebras and their maps together, and
  `GradedTor.canonical` is the canonical such system.

## Main results

* `GradedTor.existsUnique_algebra` and `GradedTor.canonicalAlgebra_unique`: the prescribed
  multiplication determines the graded algebra structure uniquely, so it is independent of all
  construction choices.
* `GradedTor.canonical_mul_ofNat` identifies multiplication with the Tor cross product
  followed by multiplication on `B`.
* `GradedTor.torPieceMap_isAlgebraHom` is the statement that the functorial maps on Tor
  preserve the unit and the homogeneous multiplication of these graded algebras.
* `GradedTor.canonical_unique` and `GradedTor.existsUnique_functorialAlgebra`: the objectwise
  construction and the algebra-homomorphism property determine the functorial system uniquely.

## Implementation notes

The ring universes and the universe of algebra carriers are independent. Algebra carriers are
transported to the common module universe used by the Tor cross product. The grading is indexed
by `ℤ`; negative pieces are the zero module. The graded object is packaged by its homogeneous
pieces rather than by a choice of direct-sum presentation, so the structure equations are
stated degreewise and the degree bookkeeping appears as explicit `cast`s along `zero_add`,
`add_zero` and `add_assoc`.

## References

* [The Stacks Project, Tag 068J](https://stacks.math.columbia.edu/tag/068J)
* [The Stacks Project, Tag 068K](https://stacks.math.columbia.edu/tag/068K)
-/
