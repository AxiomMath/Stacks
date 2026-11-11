module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableDischarged
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineSpaceChartsRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenCoverRepresentable

/-!
# The Hilbert functor of an affine scheme over an affine base is representable

Let `X ⟶ S` be a morphism of affine schemes and let `d` be a natural number. Then the degree-`d`
Hilbert functor of points of `X` over `S` is representable.

## Main results

* `Stacks.Hilbert.affineSpaceRepresentability`: the degree-`d` Hilbert functor of an affine space
  `𝔸(n; S)` over an affine scheme `S` is representable.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine`: the degree-`d`
  Hilbert functor of an affine scheme over an affine base is representable.
* `Stacks.Hilbert.isRepresentable_hilbertFunctorOfRank_of_isAffine`: the same statement, phrased
  with `CategoryTheory.Functor.IsRepresentable`.

## Implementation notes

The affine-space case is the gluing criterion
`Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isOpenHilbertSubfunctor` applied to the
chart subfunctors `Stacks.Hilbert.chartSubfunctor`, which are open, representable and cover the
field-valued points. The general case follows from it by
`Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine'`, which embeds `X` as a closed
subscheme of an affine space over `S`.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Hilbert

/-- For an affine scheme `S`, any index type `n` and any `d`, the degree-`d` Hilbert functor of
`𝔸(n; S)` over `S` is representable. -/
theorem affineSpaceRepresentability : AffineSpaceRepresentability.{u} := fun S _ n d =>
  exists_representsHilbertFunctorOfRank_of_isOpenHilbertSubfunctor (affineSpaceOver S n) d
    (chartSubfunctor S n d) (isOpenHilbertSubfunctor_chartSubfunctor (S := S) (n := n) (d := d))
    (fun W => chartSubfunctor_representableBy W)
    (fun k _ g Z => exists_mem_chartSubfunctor_of_specField k g Z)

/-- Let `X ⟶ S` be a morphism of affine schemes and let `d` be a natural number. Then the
degree-`d` Hilbert functor of points of `X` over `S` is representable by a scheme over `S`. -/
@[stacks 0B99 "the degree-`d` Hilbert functor of an affine scheme over an affine base is \
representable by a scheme over `S`"]
theorem exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine {S : Scheme.{u}}
    [IsAffine S] (X : Over S) [IsAffine X.left] (d : ℕ) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) :=
  exists_representsHilbertFunctorOfRank_of_isAffine' X d affineSpaceRepresentability

/-- The degree-`d` Hilbert functor of an affine scheme over an affine base is representable. -/
theorem isRepresentable_hilbertFunctorOfRank_of_isAffine {S : Scheme.{u}} [IsAffine S]
    (X : Over S) [IsAffine X.left] (d : ℕ) : (hilbertFunctorOfRank X d).IsRepresentable := by
  obtain ⟨⟨H, h⟩⟩ := exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine X d
  exact h.representableBy.isRepresentable

end Stacks.Hilbert

end
