module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting the proper part of a space over a henselian pair

Let `(A, I)` be a henselian pair and let `X` be an algebraic space over `Spec A` whose fibre over
`Spec (A ⧸ I)` decomposes with a proper part. Stacks 0CWI lifts that decomposition to `X` itself:
there is an open subspace and a closed subspace of `X` whose restriction to the closed fibre
recovers the given decomposition, with the closed part proper.

This file registers the tag. The theorem is
`AlgebraicGeometry.Space.exists_isOpenSubspace_isClosedSubspace_isProper_of_henselianPair`, proved
in `StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair`, and declares nothing of
its own.

## References

* [Stacks Project, Tag 0CWI](https://stacks.math.columbia.edu/tag/0CWI)
-/

add_to_stacks 0CWI "the whole tag, on the theorem proved in ClopenLiftOverHenselianPair"
  AlgebraicGeometry.Space.exists_isOpenSubspace_isClosedSubspace_isProper_of_henselianPair
