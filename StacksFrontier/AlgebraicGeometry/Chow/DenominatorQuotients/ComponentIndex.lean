module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The minimal primes of a local ring index the components through the point

Let `X` be a scheme and `ξ` a point of `X`. The canonical morphism `X.fromSpecStalk ξ` from the
spectrum of the local ring at `ξ` has as image the set of generizations of `ξ`, and
`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes` says that it restricts to a bijection from the
minimal primes over the stalk of an ideal sheaf `Z` onto the generic points of the irreducible
components of the support of `Z` through `ξ`. This file reads that statement at `Z = ⊥`, where
the support is all of `X`:

  `minimalPrimes 𝒪_{X, ξ}  ≃  {generic points of irreducible components of X through ξ}`,

realised by `X.fromSpecStalk ξ`. Nothing is assumed of `X` — not Noetherian, not integral, not
reduced — because nothing is assumed by the statement being specialised.

This is the index correspondence that the right-hand side of
`Stacks.Chow.exists_affineOpen_sheafMultiplicity_denominatorQuotients_sub_eq` has to be
re-indexed along: the length formula of [Stacks, Tag 02QH] produces a sum over the minimal primes
of `𝒪_{X, ξ}`, while part (4) of [Stacks, Tag 02SW] states its right-hand side as a sum over the
irreducible components of `X` of delta-dimension `k + 1`.

## Main results

* `Stacks.Chow.mem_componentGenericPointsThrough_bot_iff` — membership of
  `Stacks.Chow.componentGenericPointsThrough ⊥ ξ` is "generizes `ξ` and is maximal for
  specialization", the support condition being vacuous.
* `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot` — the displayed bijection.

## Implementation notes

The specialisation needs two facts about `⊥` and neither is a restatement of anything this file
proves: Mathlib's `AlgebraicGeometry.IdealSheafData.support_bot` makes the support condition
vacuous, and the stalk of the zero ideal sheaf is the zero ideal, which is a one-line `simp` on
the definition of `AlgebraicGeometry.IdealSheafData.stalk` as a supremum of images.

That second fact is **already in the tree, privately**: `stalk_bot` in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/EmbeddedResolution/CurveStrictTransform.lean`
is the same one-line statement with the same one-line proof, and there is nothing corresponding in
Mathlib. It is re-proved here rather than exposed there, because exposing a private one-liner in
another development's file is a larger change than restating it; a reader consolidating this area
should merge the two.

`minimalPrimes R` is Mathlib's abbreviation for `Ideal.minimalPrimes ⊥`, so once the stalk of `⊥`
is `⊥` the two index sets agree by `rewrite` rather than by a transport. The two set equalities
are proved first and rewritten into the `Set.BijOn` goal, which is sound here because both sets
are plain `Set`s carrying no instances — unlike the `Submodule` statements elsewhere in this
development, where `rewrite` is unusable.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- The stalk of the zero ideal sheaf is the zero ideal: it is a supremum of images of the zero
ideal. See the implementation notes on the private duplicate of this statement elsewhere in the
tree. -/
lemma idealSheafData_stalk_bot (ξ : X) :
    AlgebraicGeometry.IdealSheafData.stalk (⊥ : X.IdealSheafData) ξ = ⊥ := by
  simp [AlgebraicGeometry.IdealSheafData.stalk]

/-- **For the zero ideal sheaf the support condition is vacuous**, so a point is a generic point
of a component of the support through `ξ` exactly when it generizes `ξ` and is maximal for the
specialization order. -/
theorem mem_componentGenericPointsThrough_bot_iff (ξ η : X) :
    η ∈ componentGenericPointsThrough (⊥ : X.IdealSheafData) ξ ↔
      η ⤳ ξ ∧ ∀ η' : X, η' ⤳ η → η' = η := by
  have hsupp : ∀ y : X, y ∈ ((⊥ : X.IdealSheafData).support : Set X) := fun y => by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_bot]
    trivial
  exact ⟨fun h => ⟨h.2.1, fun η' hη' => h.2.2 η' (hsupp η') hη'⟩,
    fun h => ⟨hsupp η, h.1, fun η' _ hη' => h.2 η' hη'⟩⟩

/-- **The minimal primes of the local ring at `ξ` are the generic points of the irreducible
components of `X` through `ξ`.** The bijection is the canonical morphism from the spectrum of the
local ring, and this is `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes` at the zero ideal sheaf,
whose support is all of `X`. No hypothesis on `X`.

This is the re-indexing the right-hand side of the coefficient identity of
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.MultiplicityDifference` needs in order
to become the component sum of part (4) of [Stacks, Tag 02SW]. -/
@[ega "I 7.2.8.1" "more general", ega "IV 5.1.12" "special case"]
theorem bijOn_fromSpecStalk_minimalPrimes_bot (ξ : X) :
    Set.BijOn ⇑(X.fromSpecStalk ξ)
      {q : PrimeSpectrum (X.presheaf.stalk ξ) | q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)}
      {η : X | η ⤳ ξ ∧ ∀ η' : X, η' ⤳ η → η' = η} := by
  have hmin : ∀ q : PrimeSpectrum (X.presheaf.stalk ξ),
      q.asIdeal ∈
          (AlgebraicGeometry.IdealSheafData.stalk (⊥ : X.IdealSheafData) ξ).minimalPrimes ↔
        q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ) := by
    intro q
    rw [idealSheafData_stalk_bot]
  have hiff : ∀ q : PrimeSpectrum (X.presheaf.stalk ξ),
      (X.fromSpecStalk ξ q ⤳ ξ ∧ ∀ η' : X, η' ⤳ X.fromSpecStalk ξ q → η' = X.fromSpecStalk ξ q) ↔
        q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ) := fun q =>
    ((mem_componentGenericPointsThrough_bot_iff ξ (X.fromSpecStalk ξ q)).symm.trans
      (fromSpecStalk_mem_componentGenericPointsThrough_iff (⊥ : X.IdealSheafData) ξ q)).trans
        (hmin q)
  refine ⟨fun q hq => (hiff q).mpr hq,
    (X.fromSpecStalk ξ).isEmbedding.injective.injOn, fun η hη => ?_⟩
  obtain ⟨q, rfl⟩ : η ∈ Set.range ⇑(X.fromSpecStalk ξ) := by
    rw [Scheme.range_fromSpecStalk]
    exact hη.1
  exact ⟨q, (hiff q).mp hη, rfl⟩

end Stacks.Chow

end
