module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs
import StacksCore.Tactic.StacksAttribute

/-!
# The direct-image algebra of a quasi-compact quasi-separated morphism is quasi-coherent

Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of algebraic spaces over a scheme
`S`. The sheaf of `𝒪_X`-algebras `f_* 𝒪_Y` is quasi-coherent: its underlying `𝒪_X`-module is
the direct image of the structure sheaf of `Y`, which is quasi-coherent by [Stacks, Tag 03M9].
This is the first assertion of [Stacks, Tag 081X].

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_qcqs`: the quasi-coherence of
  `f_* 𝒪_Y`.

## References

* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

add_to_stacks 081X "quasi-coherence of the pushforward algebra"
  AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_qcqs
