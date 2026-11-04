module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.FiniteFibres
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite morphisms are the proper morphisms with finite fibres

A morphism of schemes is finite if and only if it is proper and all its fibres are finite. This
is the equivalence of the first two conditions of
`AlgebraicGeometry.IsFinite.tfae_isProper_finite_preimage_singleton`, which holds for an
arbitrary target.

## Main results

* `AlgebraicGeometry.IsFinite.tfae_isProper_finite_preimage_singleton`:
  [Stacks Project, Tag 02OG], its first two conditions.

## Implementation notes

The source assumes the target locally Noetherian and argues through the theorem on formal
functions. The equivalence holds for an arbitrary target, by Zariski's main theorem, so the
locally Noetherian hypothesis of the source is dropped.

## References

* [Stacks Project, Tag 02OG](https://stacks.math.columbia.edu/tag/02OG)
-/

@[expose] public section

add_to_stacks 02OG "the equivalence of the first two conditions, for an arbitrary target; the
  source assumes it locally Noetherian"
  AlgebraicGeometry.IsFinite.tfae_isProper_finite_preimage_singleton
