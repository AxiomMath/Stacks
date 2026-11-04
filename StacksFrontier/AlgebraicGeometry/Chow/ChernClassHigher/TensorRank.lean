module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological

/-!
# Rank preservation under pullback for a tensor product

`Stacks.Chow.PullbackPreservesRank F r` is the hypothesis the Chern class cap products of
chapter 42 carry in place of an instance: that `g^*ℱ` is finite locally free of rank `r` for
every morphism of schemes `g`. This file proves it is multiplicative in a tensor product.

The two ingredients are already in the library and only have to be put together. The pullback of
a tensor product is the tensor product of the pullbacks ([Stacks, Tag 01CD],
`Stacks.Chow.pullbackTensorObjIso`), and the rank of a tensor product is the product of the ranks
(`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf`). Applying the rank
hypotheses of the two factors at the same `g` and transporting along the comparison gives the
rank `r · s` of `g^*(ℰ ⊗ ℱ)`.

## Main results

* `Stacks.Chow.pullbackPreservesRank_tensorObj` — rank preservation under pullback is
  multiplicative in a tensor product.

## Implementation notes

The rank multiplicativity lemma is stated at the spelling
`Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩`
while the comparison isomorphism and the cap products are stated at
`AlgebraicGeometry.Scheme.Modules.tensorObj`, the same bifunctor with its sheaf of rings written
over `X.ringCatSheaf`. The two are abbreviations for the same term, so the rank is accepted at
the second spelling with no conversion; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTensorExact` for the same
identification used for exactness.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **Rank preservation under pullback is multiplicative in a tensor product.** If `g^*ℰ` has
rank `r` and `g^*ℱ` has rank `s` for every morphism of schemes `g`, then `g^*(ℰ ⊗_{𝒪_X} ℱ)` has
rank `r · s` for every `g`: the pullback of the tensor product is the tensor product of the
pullbacks by [Stacks, Tag 01CD], and the rank of a tensor product is the product of the ranks. -/
theorem pullbackPreservesRank_tensorObj {X : Scheme.{u}} {E F : X.Modules} {r s : ℕ}
    (hE : PullbackPreservesRank E r) (hF : PullbackPreservesRank F s) :
    PullbackPreservesRank (Scheme.Modules.tensorObj E F) (r * s) := fun {T} g =>
  have := hE g
  have := hF g
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (pullbackTensorObjIso g E F).symm
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf T
      ((Scheme.Modules.pullback g).obj E) ((Scheme.Modules.pullback g).obj F) r s)

end Stacks.Chow

end
