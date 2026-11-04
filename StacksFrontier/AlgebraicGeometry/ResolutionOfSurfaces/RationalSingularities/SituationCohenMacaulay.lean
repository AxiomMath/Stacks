module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Normal
public import StacksFrontier.RingTheory.Depth.Dimension
import all StacksFrontier.RingTheory.AdicCompletion.Normal
import StacksCore.Tactic.StacksAttribute

/-!
# The base ring of Situation [Stacks, Tag 0B4W] is Cohen–Macaulay

In Situation [Stacks, Tag 0B4W] the ring `A` is a Noetherian local normal domain with
`dim(A) = 2`. Such a ring is Cohen–Macaulay, and the proof is two inequalities:

* `depth_𝔪(A) ≥ min(2, dim A) = 2` is the depth half `(S_2)` of Serre's criterion for normality,
  [Stacks, Tag 031S], read at the maximal ideal;
* `depth_𝔪(A) ≤ dim Supp(A) = dim(A) = 2` is [Stacks, Tag 00LK].

So `depth_𝔪(A) = dim(A)`, which is `Module.IsMaximalCohenMacaulay A A`, which for a Noetherian
local ring is Cohen–Macaulayness.

## Main results

* `AlgebraicGeometry.isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two` — a normal
  Noetherian local ring of dimension two is Cohen–Macaulay.
* `AlgebraicGeometry.RationalSingularitySituation.isCohenMacaulayLocalRing` — the same at the base
  ring of Situation [Stacks, Tag 0B4W], where the three hypotheses are fields of the situation.

## Why this is needed

`Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension` and
`Dualizing.subsingleton_ext_residueField_single_of_ne_localRingDimension` of
`…/RingTheory/Dualizing/CohenMacaulayNormalizedShift.lean` pin the normalizing shift of a
dualizing *module* — which `Stacks.Duality.IsDualizingRingModule` leaves existential — to
`-dim(A)`, and they take `IsCohenMacaulayLocalRing A` to do it. That is the hypothesis the
normalization convention of [Stacks, Tag 0A7M] needs in order to evaluate `RHom_A(κ, ω_A)` in the
blowup situation, so without this file every statement in that chain carries it.

## Implementation notes

The depth half of Serre's criterion is used in its **local** form,
`serre_conditions_of_isNormalRing` of `…/RingTheory/AdicCompletion/Normal.lean`, which has
already transported the criterion's statement about `A_𝔪` back to `A` along
`IsLocalization.atUnits`. That declaration is `private`
there, so it is reached by `import all` — the pattern of
`…/RingTheory/Dualizing/MatlisExtComparison.lean`. It would be better de-privatised, but
`…/RingTheory/AdicCompletion/Normal.lean` is outside the part of the tree this change touches.

The global form of the criterion, `isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_`
`and_min_two_le_depth` of `…/RingTheory/Serre/Criterion.lean`, is public and would do as well at
the cost of redoing that transport.

## References

* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 00LK](https://stacks.math.columbia.edu/tag/00LK)
* [Stacks Project, Tag 00NF](https://stacks.math.columbia.edu/tag/00NF)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **A normal Noetherian local ring of dimension two is Cohen–Macaulay.**

The depth is at least two by the `(S_2)` half of Serre's criterion for normality,
[Stacks, Tag 031S], in the local form `serre_conditions_of_isNormalRing`, whose bound is
`min(2, dim A) ≤ depth_𝔪(A)`; and at most two because depth is bounded by the dimension of the
support, [Stacks, Tag 00LK], which for `A` over itself is `dim(A)`. Equality of depth and
dimension is `Module.IsMaximalCohenMacaulay A A`, which
`isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay` identifies with Cohen–Macaulayness.

Dimension two is used only through `min(2, 2) = 2`; the same argument gives the statement in
dimension at most two, and in dimension at most one it is
`isCohenMacaulayLocalRing_of_ringKrullDim_le_one`. -/
@[ega "IV 5.8.6" "(ii), special case",
  ega "IV 7.2.10" "(i), special case",
  sga "2 XI 3.11" "(ii), special case"]
theorem isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsNormalRing A) (h2 : ringKrullDim A = 2) :
    IsCohenMacaulayLocalRing A := by
  have hne : (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A A) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hle := Module.depth_le_supportDim A (IsLocalRing.maximalIdeal A) A hne
  rw [Module.supportDim_self_eq_ringKrullDim, h2] at hle
  have hge : (2 : WithBot ℕ∞) ≤
      (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) := by
    have hs := (serre_conditions_of_isNormalRing A hA).2
    rwa [h2, min_self] at hs
  rw [isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay, Module.IsMaximalCohenMacaulay, h2]
  exact le_antisymm hle hge

/-- **The base ring of Situation [Stacks, Tag 0B4W] is Cohen–Macaulay.** Its three inputs are
fields of the situation: `A` is Noetherian because it is Nagata, it is a normal domain, and its
Krull dimension is two.

A normal domain over a local ring is a normal *ring* by
`IsNormalRing.of_isIntegrallyClosed`, so this is
`AlgebraicGeometry.isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two`. -/
theorem RationalSingularitySituation.isCohenMacaulayLocalRing
    (S : RationalSingularitySituation.{u}) :
    IsCohenMacaulayLocalRing S.A :=
  isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two
    (IsNormalRing.of_isIntegrallyClosed S.A) S.dimension_two

end AlgebraicGeometry

end
