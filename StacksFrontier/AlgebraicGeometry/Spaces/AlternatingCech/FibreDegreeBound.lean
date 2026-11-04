module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.QuasicoherentHigherVanishing

/-!
# The fibre bound of Stacks 072B is a bound on the degrees of the fibres

The integer `d` in [Stacks, Tag 072B] (Proposition 69.7.2) is read as a bound on the degrees of the
fibres of `f`. This module explains that reading; the proposition, read that way, is registered on
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isSeparated`.

## The printed wording

The source reads: *Let `X` be a quasi-compact and separated algebraic space over a scheme `S`,
`U` an affine scheme and `f : U → X` a surjective étale morphism. Let `d` be an upper bound for
the size of the fibres of `|U| → |X|`. Then for any quasi-coherent `𝒪_X`-module `ℱ` we have
`Hᵠ(X, ℱ) = 0` for `q ≥ d`.*

## The degree reading

`d` bounds the *degrees* of the fibres of `f`: every base change of `f` to a field `k` is finite
locally free of rank at most `d` (equivalently, over each geometric point of `X` there are at most
`d` geometric points of `U`). This is the condition of [Stacks, Tag 03JL] with an explicit
constant.

**Why the proof needs this reading.** The proof of 072B uses the alternating Čech spectral
sequence of the covering `f` [Stacks, Tag 0728] and concludes from "`W_p = ∅` for `p ≥ d`", where
`W_p` is the complement of all the diagonals in the `(p+1)`-fold fibre product `U ×_X ⋯ ×_X U`.
That step holds for the degree reading and fails for the point-count reading: for
`X = Spec k` and `U = Spec k'` with `k'/k` a separable quadratic extension, every fibre of
`|U| → |X|` has exactly one point, but `f` has degree `2`, and
`W_1 = U ×_X U ∖ Δ ≅ Spec k'` is not empty. (The conclusion still holds in that example, as `X` is
affine; the literal point-count reading is neither proved nor refuted by the source and is out of
scope.)

**The reading of `d` in 072C.** [Stacks, Tag 072C] (Lemma 69.7.3), the place where 072B is
applied, chooses "an integer `d` bounding the degrees of the fibres of `U → X`", obtained from the
universal boundedness of the fibres [Stacks, Tag 03JL] via Decent Spaces, Lemma 68.5.1. So the
degree reading is exactly what the application supplies. In this library that choice is
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers`
(in `StacksFrontier/AlgebraicGeometry/Spaces/CohomologicalDimension.lean`), stated with
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`
(in `StacksFrontier/AlgebraicGeometry/Spaces/Decent/UniversallyBoundedFibres.lean`).

## The Lean statement

The proposition under the degree reading is
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isSeparated`
(in `StacksFrontier/AlgebraicGeometry/Spaces/AlternatingCech/QuasicoherentHigherVanishing.lean`).
Its binder `hd` is the degree bound: for every field `k`, every `T` over `S` with
`T ≅ Spec k` and every `ξ : T → X`, the base change of `f` along `ξ` is a morphism
`V → T` that is finite locally free of some rank `r ≤ d`
(`Stacks.Morphisms.IsFiniteLocallyFreeOfRank`, in
`StacksFrontier/AlgebraicGeometry/Morphisms/FiniteLocallyFreeOfRank.lean`). Separatedness is the
absolute notion `AlgebraicGeometry.Space.IsAbsolutelySeparated`
(in `StacksFrontier/AlgebraicGeometry/Spaces/Separated.lean`) of [Stacks, Tag 03BO];
quasi-compactness of `X` follows from the affine surjection and is not assumed.

## References

* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
-/

