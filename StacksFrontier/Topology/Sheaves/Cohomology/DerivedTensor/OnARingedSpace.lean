module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on a ringed space

Let `(X, O_X)` be a ringed space and let `F^•` be an object of `D(O_X)`. Derived tensoring
with `F^•`,

`- ⊗_{O_X}^{L} F^• : D(O_X) ⟶ D(O_X)`,

is an exact functor of triangulated categories, computed by the ordinary total tensor complex
as soon as one of the two arguments is represented by a K-flat complex.

All of that data — the bifunctor on `D(O_X)`, its comparisons with the total tensor complex at
K-flat representatives, the canonical map to the total tensor complex for arbitrary
representatives, and exactness in each variable — is bundled by
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` for a ringed site, and
`Stacks.Cohomology.TorAmplitude.derTensor` is its canonical inhabitant read at the ringed
space `X`, i.e. at the site of opens of `X` with structure sheaf `O_X`. Fixing the right-hand
argument, the exact functor of this tag is `(derTensor X).tensor.flip.obj F`, and its
exactness is the `exact_left` field. This file therefore records Tag 06YH on that bundled
construction rather than making a second, independent choice of the same derived functor.

## Main results

No new results are proved here. Tag 06YH is registered on
`Stacks.Cohomology.TorAmplitude.derTensor`.

## References

* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

add_to_stacks 06YH "the derived tensor product on a ringed space, with its exactness"
  Stacks.Cohomology.TorAmplitude.derTensor
