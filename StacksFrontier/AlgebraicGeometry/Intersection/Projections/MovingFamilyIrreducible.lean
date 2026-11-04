module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProduct
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection

/-!
# Irreducibility and dimension of the schemes of the Moving Lemma

The projective space of a nonzero finite-dimensional vector space is irreducible, because a basis
identifies it with `Proj k[T₀, …, Tₙ]`; so the line `ℓ` and `𝐏(V)` are irreducible, and over an
algebraically closed field so is their product. This file records the last of those three facts,
the first two being found by instance search, together with the dimension of the ambient product
`ℓ × 𝐏(V)`, which is `dim 𝐏(V) + 1`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_movingAmbient_of_finrank`: the
  product `ℓ × 𝐏(V)` is irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_movingAmbient_eq`: its dimension
  is `dim 𝐏(V) + 1`.

## Implementation notes

The irreducibility of the projective space of a nonzero finite-dimensional vector space is the
instance `AlgebraicGeometry.ProjectiveSpaceOfModule.irreducibleSpace_projectiveSpaceOfModule` of
`StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection`, so the line and `𝐏(V)` are
irreducible by instance search and only the product needs an argument: a product of
geometrically irreducible schemes over a separably closed field is irreducible.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k : Type u) [Field k]

variable (V : Type u) [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- **The product `ℓ × 𝐏(V)` is irreducible** over an algebraically closed field. -/
public theorem irreducibleSpace_movingAmbient_of_finrank [IsAlgClosed k] :
    IrreducibleSpace (movingAmbient k V L) :=
  irreducibleSpace_movingAmbient k V L

/-- **The dimension of `ℓ × 𝐏(V)` is `dim 𝐏(V) + 1`** when `L` has corank two. -/
public theorem topologicalKrullDim_movingAmbient_eq
    (hL : Module.finrank k (lineSpace k V L) = 2) :
    topologicalKrullDim (movingAmbient k V L) =
      topologicalKrullDim (projectiveSpaceOfModule k V) + 1 := by
  rw [topologicalKrullDim_movingAmbient, topologicalKrullDim_movingLine k V L hL, add_comm]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
