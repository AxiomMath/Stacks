module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints

/-!
# Representability of the Hilbert functor of points over an affine base

Let `X ⟶ S` be a morphism of affine schemes and let `d` be a natural number. Then the degree-`d`
Hilbert functor of points of `X` over `S` is representable by a scheme over `S`.

The proof is the reduction to affine space: `X` is a closed subscheme of an affine space over
`S`, the affine space on the index set of all global functions of `X`, and the Hilbert functor
of a closed subscheme is represented by a closed subscheme of the Hilbert scheme of the ambient
scheme.

## Main definitions

* `Stacks.Hilbert.ClosedImmersionRepresentability` — the assertion of Stacks Tag 0B97, carried
  as a hypothesis.
* `Stacks.Hilbert.AffineSpaceRepresentability` — the assertion that the degree-`d` Hilbert
  functor of an affine space over an affine base is representable, carried as a hypothesis.

## Main results

* `Stacks.Hilbert.exists_isClosedImmersion_toAffineSpace` — a scheme affine over an affine base
  is, over that base, a closed subscheme of an affine space.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine` — **Stacks Tag 0B99**: the
  degree-`d` Hilbert functor of an affine scheme over an affine base is representable.

## Implementation notes

*What is proved unconditionally and what is carried.* The closed immersion into affine space and
the deduction of representability from it are proved here. The two inputs the source's proof
cites are carried as explicit named hypotheses, because neither is available in this development:
`Stacks.Hilbert.ClosedImmersionRepresentability` is Stacks 0B97, whose conclusion is already
recorded as the structure `Stacks.Hilbert.ClosedSubschemeRepresentingHilbertFunctor` but which is
not proved; `Stacks.Hilbert.AffineSpaceRepresentability` is the case of affine space, which the
source proves by the explicit universal construction described below. Both are named
hypotheses, so the theorem below is an implication and is proved in full. Note that the second
is an instance of the conclusion, an affine space over an affine base being affine: what is
established here is the source's reduction step, not the universal construction.

*The construction the affine-space hypothesis stands for.* Writing `S = Spec(R)` and
`A = R[x_i; i ∈ I]`, the source covers the Hilbert functor of `Spec(A)` by the subfunctors `F_W`
indexed by the `d`-element subsets `W ⊆ A`, where a family `Z` over `T` lies in `F_W(T)` when
`⨁_{f ∈ W} 𝒪_T ⟶ (Z ⟶ T)_* 𝒪_Z`, `(g_f) ↦ ∑ g_f · f|_Z`, is surjective. Each `F_W` is
represented by the spectrum of `R[c_{kl}^m, b^l, b_i^l]` modulo the relations making
`⨁_l R e_l` a commutative `R`-algebra with unit `∑ b^l e_l` in which `f_l ↦ e_l`; the `F_W`
cover by Nakayama's lemma applied to a basis of a fibre, are open by Stacks 00O0, and the
Hilbert functor is a sheaf by Stacks 0B95, so Stacks 01JJ glues the representing schemes. Of
these inputs this development has only the separatedness clause of 0B95
(`Stacks.Hilbert.isSeparated_fpqcTopology_hilbertFunctorOfRank`) and 00O0
(`StacksFrontier.RingTheory.Module.Projective.Locus`); the subfunctors, their representing affine
schemes and the form of 01JJ for a sheaf on the schemes over `S` are all absent, so the
affine-space case is carried whole.

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

/-! ### The two cited inputs, carried as hypotheses -/

/-- **The assertion of Stacks 0B97.** Let `i : X ⟶ Y` be a morphism of schemes over `S` which is
a closed immersion and let `d` be a natural number. If `H_Y` represents the degree-`d` Hilbert
functor of `Y`, then the degree-`d` Hilbert functor of `X` is represented by a closed subscheme
of `H_Y`, whose universal family is the one of `H_Y` cut down along `i`.

This is not proved in this development; the results of this file take it as a hypothesis. -/
def ClosedImmersionRepresentability : Prop :=
  ∀ {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y), IsClosedImmersion i.left →
    ∀ (d : ℕ) (H_Y : Over S) (hY : RepresentsHilbertFunctorOfRank Y H_Y d),
      Nonempty (ClosedSubschemeRepresentingHilbertFunctor i d H_Y hY)

/-- **The case of affine space in Stacks 0B99.** For an affine scheme `S`, any index type `n`
and any natural number `d`, the degree-`d` Hilbert functor of the affine space `𝔸(n; S)` over
`S` is representable.

This is the half of Stacks 0B99 proved by the explicit universal construction of a commutative
algebra of rank `d` with a marked basis; it is not available in this development, and the
results of this file take it as a hypothesis. -/
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

/-- **Stacks 0B99,** conditional on Stacks 0B97 and on the case of affine space, both carried as
hypotheses. Let `X ⟶ S` be a morphism of affine schemes and let `d` be a natural number. Then
the degree-`d` Hilbert functor of points of `X` over `S` is represented by a scheme over `S`.

Over an affine base, `X` is a closed subscheme of an affine space; its Hilbert functor is
therefore represented by a closed subscheme of the Hilbert scheme of that affine space. -/
@[stacks 0B99 "the reduction of the affine case to the case of an affine space, conditional on \
two inputs carried as hypotheses: Stacks 0B97, and representability for an affine space over an \
affine base.  The latter is an instance of this very conclusion, since an affine space over an \
affine base is affine; what is proved here is therefore the source's reduction step, the closed \
immersion of an affine scheme into an affine space, and not the universal construction that \
makes the affine-space case true"]
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
