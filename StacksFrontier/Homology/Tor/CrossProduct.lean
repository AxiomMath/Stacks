module

public import StacksFrontier.Homology.Tor.CrossProduct.System
public import StacksFrontier.Homology.Tor.CrossProduct.ChainComparison
public import StacksFrontier.Homology.Tor.CrossProduct.DerivedProductAgreement
public import StacksFrontier.Homology.Tor.CrossProduct.Canonical

/-!
# The cross product on Tor along a ring map

For a homomorphism of commutative rings `R → A`, projective resolutions of two `R`-modules
give a canonical cross product on the left derived functors of extension of scalars. The
construction is natural in both modules and is normalized in degree zero. Specialized to an
`R`-algebra `A`, it is the canonical product
`Torⁿᴿ(M, A) ⊗[A] Torᵐᴿ(N, A) → Torⁿ⁺ᵐᴿ(M ⊗[R] N, A)`.

## Main definitions

* `TorCrossProduct.torBaseChange` is `Torⁿᴿ(-, A)`, valued in `A`-modules.
* `TorCrossProduct.ChainHomologyProduct` records the cocycle-level product on the homology of
  two nonnegatively graded chain complexes.
* `TorCrossProduct.liftedCochain` is the concrete cochain representative obtained from a
  scalar-extended resolution by universe change and the reindexing `n ↦ -n`.
* `TorCrossProduct.LiftedTensorComparison` specifies the comparison of lifted tensor
  complexes by its value on every homogeneous summand.
* `TorCrossProduct.ResolutionModel` records the normalized comparison
  `Tot(P ⊗ Q) → T` and the map it induces after extension of scalars.
* `TorCrossProduct.System` packages the products in all bidegrees, their resolution model,
  and their degree-zero normalization.
* `TorCrossProduct.canonical` is the canonical system, and `TorCrossProduct.product` its
  component in a given bidegree.
* `RingTheory.TorProducts.torBaseChange` is `Torⁿᴿ(-, A)` for an `R`-algebra `A`, and
  `RingTheory.TorProducts.torProduct` the canonical product, natural in both variables.

## Main results

* `TorCrossProduct.canonical_nonempty` constructs the canonical system from projective
  resolutions. Its resolution field states normalization on `H₀`, uniqueness up to chain
  homotopy, and agreement with the canonical product on the cohomology of a derived tensor
  product.
* `RingTheory.TorProducts.torProduct_resolution`,
  `RingTheory.TorProducts.torProduct_degree_zero` and
  `RingTheory.TorProducts.torProduct_unique` are the resolution characterization, the
  degree-zero identification, and the uniqueness of the product.

## Implementation notes

The module categories use a universe containing the universes of both rings and an additional
module-carrier universe. Thus modules whose carriers originally lie in independent universes
may first be transported by `ModuleCat.uliftFunctor` to their common maximum; no equality of the
ring and module universes is imposed. Naturality is encoded by making every product a natural
transformation. The fields `ResolutionModel.μ_unique`, `ResolutionModel.product_eq`, and
`System.product_unique` characterize the selected map independently of all resolution choices.
For the comparison with the derived cohomology product, `A` is explicitly lifted to the common
module universe, scalars are transported along `ULift.ringEquiv`, and a chain complex in
nonnegative homological degrees is extended by zero to a cochain complex in nonpositive
degrees. Thus the derived objects in the comparison are definitionally the images of the
scalar-extended resolutions. The homology transport is the composite of
`HomologicalComplex.extendHomologyIso` and `CategoryTheory.ShortComplex.mapHomologyIso`. The
total-complex comparison is specified by sending each homogeneous pure tensor to the same
tensor, with no additional sign. Its induced homology isomorphism makes the equality with the
derived product an equality of maps from the homology of these specific complexes.

Parts: `System`, `ChainComparison`, `DerivedProductAgreement`, `Canonical`.

## References

* [The Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [The Stacks Project, Tag 068J](https://stacks.math.columbia.edu/tag/068J)
* [The Stacks Project, Tag 0649](https://stacks.math.columbia.edu/tag/0649)
* [The Stacks Project, Tag 064A](https://stacks.math.columbia.edu/tag/064A)
-/
