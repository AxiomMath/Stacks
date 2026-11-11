module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints

/-!
# The reduction of affine representability to affine space

Let `X ⟶ S` be a morphism of affine schemes and let `d` be a natural number. This file reduces
representability of the degree-`d` Hilbert functor of points of `X` over `S` to two inputs:
the Hilbert functor of a closed subscheme is represented by a closed subscheme of the
representing scheme of the ambient one (Stacks 0B97), and the degree-`d` Hilbert functor of an
affine space over an affine base is representable.

The reduction is the source's: `X` is a closed subscheme of an affine space over `S`, the
affine space on the index set of all global functions of `X`, and the Hilbert functor of a
closed subscheme is represented by a closed subscheme of the Hilbert scheme of the ambient
scheme.

## Main definitions

* `Stacks.Hilbert.ClosedImmersionRepresentability` — the proposition asserted by Stacks Tag
  0B97, proved as `Stacks.Hilbert.closedImmersionRepresentability`.
* `Stacks.Hilbert.AffineSpaceRepresentability` — the proposition that the degree-`d` Hilbert
  functor of an affine space over an affine base is representable, proved as
  `Stacks.Hilbert.affineSpaceRepresentability`.

## Main results

* `Stacks.Hilbert.exists_isClosedImmersion_toAffineSpace` — a scheme affine over an affine base
  is, over that base, a closed subscheme of an affine space.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine` — the reduction step:
  representability for `X` affine over an affine base, given the two propositions above.

## Implementation notes

Both inputs are proved in this development: `Stacks.Hilbert.closedImmersionRepresentability`
in `StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableDischarged` and
`Stacks.Hilbert.affineSpaceRepresentability` in
`StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableUnconditional`, the
latter by gluing the chart subfunctors `F_W` of the source along Stacks 01JJ. Stacks Tag 0B99
itself is registered on
`Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine` in that module,
which supplies both inputs to the reduction proved here.

*The index set of the affine space.* No finiteness hypothesis is imposed on `X ⟶ S`, so the
polynomial algebra is taken on the index set of all global functions of `X` and the immersion
sends the coordinate indexed by a function to that function. This matches the source, which
takes a polynomial ring on a sufficiently large index set.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 0B95](https://stacks.math.columbia.edu/tag/0B95)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 00O0](https://stacks.math.columbia.edu/tag/00O0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Hilbert

/-! ### The two inputs of the reduction -/

/-- **The assertion of Stacks 0B97.** Let `i : X ⟶ Y` be a morphism of schemes over `S` which is
a closed immersion and let `d` be a natural number. If `H_Y` represents the degree-`d` Hilbert
functor of `Y`, then the degree-`d` Hilbert functor of `X` is represented by a closed subscheme
of `H_Y`, whose universal family is the one of `H_Y` cut down along `i`.

It is proved as `Stacks.Hilbert.closedImmersionRepresentability`. -/
def ClosedImmersionRepresentability : Prop :=
  ∀ {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y), IsClosedImmersion i.left →
    ∀ (d : ℕ) (H_Y : Over S) (hY : RepresentsHilbertFunctorOfRank Y H_Y d),
      Nonempty (ClosedSubschemeRepresentingHilbertFunctor i d H_Y hY)

/-- **The case of affine space in Stacks 0B99.** For an affine scheme `S`, any index type `n`
and any natural number `d`, the degree-`d` Hilbert functor of the affine space `𝔸(n; S)` over
`S` is representable.

It is proved as `Stacks.Hilbert.affineSpaceRepresentability`, by the source's universal
construction of a commutative algebra of rank `d` with a marked basis. -/
def AffineSpaceRepresentability : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (n : Type u) (d : ℕ),
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank (Over.mk (𝔸(n; S) ↘ S)) H d)

/-! ### The reduction to affine space -/

/-- A scheme affine over an affine base is, over that base, a closed subscheme of an affine
space: the one on the index set of all global functions, into which it is immersed by sending
the coordinate indexed by a function to that function. -/
theorem exists_isClosedImmersion_toAffineSpace {S : Scheme.{u}} [IsAffine S] (X : Over S)
    [IsAffine X.left] :
    ∃ (n : Type u) (i : X ⟶ Over.mk (𝔸(n; S) ↘ S)), IsClosedImmersion i.left := by
  refine ⟨Γ(X.left, ⊤), Over.homMk (AffineSpace.homOfVector X.hom id) (by simp), ?_⟩
  change IsClosedImmersion (AffineSpace.homOfVector X.hom id)
  refine IsClosedImmersion.of_surjective_of_isAffine _ fun b => ⟨AffineSpace.coord _ b, ?_⟩
  exact AffineSpace.homOfVector_appTop_coord _ _ _

/-! ### Representability over an affine base -/

/-- **The reduction step in the proof of Stacks 0B99.** Let `X ⟶ S` be a morphism of affine
schemes and let `d` be a natural number. Given Stacks 0B97 and representability for an affine
space over an affine base, the degree-`d` Hilbert functor of points of `X` over `S` is
represented by a scheme over `S`.

Over an affine base, `X` is a closed subscheme of an affine space; its Hilbert functor is
therefore represented by a closed subscheme of the Hilbert scheme of that affine space. Both
inputs are proved in this development, and Stacks 0B99 itself is
`Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine`. -/
theorem exists_representsHilbertFunctorOfRank_of_isAffine {S : Scheme.{u}} [IsAffine S]
    (X : Over S) [IsAffine X.left] (d : ℕ) (h0B97 : ClosedImmersionRepresentability.{u})
    (hAffineSpace : AffineSpaceRepresentability.{u}) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  obtain ⟨n, i, hi⟩ := exists_isClosedImmersion_toAffineSpace X
  obtain ⟨⟨H_Y, hY⟩⟩ := hAffineSpace S n d
  obtain ⟨Z⟩ := h0B97 i hi d H_Y hY
  exact ⟨Z.H_X, Z.represents⟩

end Stacks.Hilbert

end
