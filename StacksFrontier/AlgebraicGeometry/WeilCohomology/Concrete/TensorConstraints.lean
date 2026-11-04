module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Commutativity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.ProductPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Associativity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Unit

/-!
# The constraints of the tensor product of correspondences

Stacks 0FG7 takes as associativity and commutativity constraints of the category of
correspondences those of products of schemes, and `Spec k` as unit. This file proves the
corresponding laws for the tensor product of correspondences between smooth projective schemes
of mixed dimension (`Stacks.WeilCohomology.tensor`), formed with the canonical diagonal classes:

* transporting `(c₁ ⊗ c₂) ⊗ c₃` along the associativity isomorphisms gives `c₁ ⊗ (c₂ ⊗ c₃)`;
* transporting `c ⊗ c'` along the factor switches gives `c' ⊗ c`;
* for `P ≅ Spec k`, transporting `[Δ_P] ⊗ c` and `c ⊗ [Δ_P]` along the projections gives `c`.

They are obtained from the constant-dimension statements of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorAssociativity` on the blocks of the
decompositions into equidimensional parts, the block of a product being read in the
corresponding part of the product through the open and closed immersions of
`Stacks.WeilCohomology.tensorBlockHom`.

The proofs are split into
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Commutativity`,
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.ProductPushforward`,
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Associativity` and
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Unit`.

## Main results

* `Stacks.WeilCohomology.corrEquivOfIso_tensor_tensor`: associativity.
* `Stacks.WeilCohomology.corrEquivOfIso_tensor_swap`: commutativity.
* `Stacks.WeilCohomology.corrEquivOfIso_tensor_diagonalCorr_left` and
  `Stacks.WeilCohomology.corrEquivOfIso_tensor_diagonalCorr_right`: the unit laws.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/
