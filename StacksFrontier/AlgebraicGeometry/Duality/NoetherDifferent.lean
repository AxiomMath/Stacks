module

public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Localization

/-!
# The Noether different

Let `B` be a commutative algebra over a commutative ring `A`. The kernel of the multiplication
map `B ⊗[A] B → B` is the diagonal ideal of `B/A`; its annihilator inside `B ⊗[A] B` is the
*diagonal annihilator* `J`, and the image of `J` under multiplication is the *Noether different*
of `B/A`, an ideal of `B`. The three basic computations are its behaviour on a product of
algebras, under flat base change of the ground ring, and under a localization of `B` whose
spectrum is an open immersion.

The mathematics lives in the three modules this one re-exports:
`Stacks.Discriminant.diagonalAnnihilator`, `noetherDifferent` and the product computation in
`StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic` with `@[stacks 0BVL]`; flat
base change in `…NoetherDifferent.FlatBaseChange` with `@[stacks 0BVM]`; and the localization
statement in `…NoetherDifferent.Localization` with `@[stacks 0BVN]`.

## References

* [Stacks Project, Tag 0BVL](https://stacks.math.columbia.edu/tag/0BVL)
* [Stacks Project, Tag 0BVM](https://stacks.math.columbia.edu/tag/0BVM)
* [Stacks Project, Tag 0BVN](https://stacks.math.columbia.edu/tag/0BVN)
-/
