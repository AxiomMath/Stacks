module

public import StacksFrontier.Homology.PseudoCoherent.Products.Comparison
public import StacksFrontier.Homology.PseudoCoherent.Products.Characterization

/-!
# Pseudo-coherence and products

For a commutative ring `R` and a bounded-above object `K` of `D(R)`, pseudo-coherence is
equivalent to the derived tensor product with `K` commuting with arbitrary products of modules.
The analogous characterization of `m`-pseudo-coherence asks for an isomorphism on cohomology
above `m` and a surjection in degree `m`.

## Main definitions

* `StacksDraft.PseudoCoherence.DerivedTensorProduct`: a derived tensor bifunctor on `D(R)`,
  the total left derived functor of tensoring cochain complexes.
* `StacksDraft.PseudoCoherence.DerivedProducts`: a choice of categorical products in `D(R)`.
* `StacksDraft.PseudoCoherence.tensorProductComparison`, `tensorPowerComparison` and
  `tensorRingPowerComparison`: the canonical comparison morphism
  `K ⊗ᴸ (∏ a, Q a) ⟶ ∏ a, (K ⊗ᴸ Q a)` and its specializations to a constant family and to a
  power of the coefficient ring.

## Main results

* `StacksDraft.PseudoCoherence.pseudoCoherent_iff_derivedTensor_preserves_products`: both
  four-way characterizations, of pseudo-coherence and of `m`-pseudo-coherence.

## Implementation notes

The derived tensor product and arbitrary products are supplied as universally characterized
data. The coefficient ring is replaced by a canonically equivalent small copy, so that the module
universe is independent of the original ring carrier, and product indices range over that entire
module universe. Both products in each comparison are taken in `D(R)`, with modules embedded in
degree zero.

## References

* [Stacks Project, Tag 0CYB](https://stacks.math.columbia.edu/tag/0CYB)
-/
