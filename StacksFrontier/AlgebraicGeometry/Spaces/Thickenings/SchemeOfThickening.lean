module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCoverByScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion

/-!
# A thickening of a scheme is a scheme

Let `S` be a scheme and let `X ⊂ X'` be a thickening of algebraic spaces over `S`. If `X` is
(representable by) a scheme, then so is `X'`. This is [Stacks Project, Tag 05ZR].

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable`: **Stacks 05ZR**
  in the subspace form of Stacks 05ZK, part (1).
* `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`:
  **Stacks 05ZR** in the morphism form `AlgebraicGeometry.Space.IsThickeningHom`.
* `AlgebraicGeometry.IsAlgebraicSpace.isRepresentable_of_isRepresentable_reduction`, registered
  for **Stacks 07VU** in
  `StacksFrontier/AlgebraicGeometry/Spaces/ThickeningSchemeRepresentableClosedImmersion.lean`: an
  algebraic space whose reduction is a scheme is a scheme.

## Implementation notes

The proof is the reduction to the affine case. A point of `X'` comes from a point of the thin
side `G`, which lies in an affine open subscheme `W ⊂ G`. By Stacks 05ZP
(`AlgebraicGeometry.Space.existsUnique_isOpenSubspace_preimage_eq_of_isThickening`) there is an
open subspace `W' ⊂ X'` with `W = G ×_{X'} W'`; the inverse image of `G` in `W'` is a thickening
of `W'` (Stacks 09ZX, `AlgebraicGeometry.Space.isThickening_preimage`) isomorphic to `W`, hence
affine, so `W'` is affine by `AlgebraicGeometry.Space.C1573.isAffineSpace_of_isThickening` (a
thickening of an affine algebraic space is affine). Every point of `X'` thus lies in a
representable open subspace, and `X'` is a scheme by
`AlgebraicGeometry.Space.isRepresentable_of_forall_mem_isRepresentable_isOpenSubspace`.

This route does not pass through Stacks 07VU or 07VT, whose library forms carry hypotheses.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/- **Stacks 05ZR.** Let `G ⊂ X'` be a thickening of algebraic spaces over `S`, in the subspace
form of Stacks 05ZK, part (1). If `G` is (representable by) a scheme, then so is `X'`. The
statement is `AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable`
(`StacksFrontier/AlgebraicGeometry/Spaces/ThickeningSchemeRepresentableClosedImmersion.lean`),
registered here for 05ZR. -/
add_to_stacks 05ZR AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable

/- **Stacks 05ZR, morphism form.** Let `i : X ⟶ X'` be a thickening of algebraic spaces over
`S`, in the sense of `AlgebraicGeometry.Space.IsThickeningHom`. If `X` is (representable by) a
scheme, then so is `X'`. The statement is
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`, registered here
for 05ZR. -/
add_to_stacks 05ZR "the morphism form"
  AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable

end AlgebraicGeometry.Space

end
