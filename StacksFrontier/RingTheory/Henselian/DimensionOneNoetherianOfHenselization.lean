module

public import StacksFrontier.RingTheory.Henselian.ReducedDimensionOneNoetherianOfHenselization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dimension one and Noetherianity are invariant under henselization, without reducedness

A Noetherian local ring `R` of Krull dimension one has these two properties also for any
henselization `H`, in any universe. This is
`StacksDraft.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization` with the
reducedness dropped from both the hypotheses and the conclusion.

The reason for having the statement without reducedness is that the local rings of a *good*
algebraic space — one that is locally Noetherian but need not be reduced — are Noetherian of
dimension one at a point of codimension one and nothing more; only for an integral space are
they reduced. The sums over the irreducible components of Stacks 0EQ2, 0EQA and 0EQQ are read on
the henselian local ring of such a space, so they need these two properties of it separately
from reducedness, which holds for the quotients by the ideals of the components and not for the
ring itself.

Nothing is new in the proof: dimension invariance is Stacks 06LK and Noetherianity is
Stacks 06LJ, both available for a henselization in the *same* universe as `R` alongside a strict
henselization in `StacksFrontier.RingTheory.Henselian.PermanenceOfProperties`, and the
cross-universe uniqueness of henselizations transports them to an arbitrary `H`.

## Main results

* `StacksDraft.ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization`: a henselization of
  a Noetherian local ring of dimension one is Noetherian of dimension one.

## References

* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ)
* [Stacks Project, Tag 06LK](https://stacks.math.columbia.edu/tag/06LK)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace StacksDraft

/-- **Dimension one and Noetherianity are invariant under henselization.** If a local ring `R` is
Noetherian of Krull dimension one, then so is any henselization `H` of it, even one living in a
different universe.

The same-universe statements (Stacks 06LK, 06LJ) are applied to the henselization and strict
henselization supplied by `IsLocalRing.henselizationTower`, and transported to `H` along the
cross-universe isomorphism `StacksDraft.exists_ringEquiv_of_isHenselization`. This is
`StacksDraft.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization` with
reducedness dropped from both sides. -/
@[sga "4 VIII 4.1" "special case", sga "5 I 3.1.3" "special case"]
theorem ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization
    {R : Type u} {H : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H]
    (hdim : ringKrullDim R = 1) :
    ringKrullDim H = 1 ∧ IsNoetherianRing H := by
  let κ := SeparableClosure (ResidueField R)
  let T := henselizationTower R κ
  obtain ⟨e, -⟩ := exists_ringEquiv_of_isHenselization (R := R) (H := H) (H' := T.henselization)
  have hnoethT : IsNoetherianRing T.henselization :=
    (isNoetherianRing_iff_henselizations R T.henselization T.strictHenselization κ).1.mp
      inferInstance
  exact ⟨(ringKrullDim_eq_of_ringEquiv e).trans
      ((ringKrullDim_eq_henselization_eq_strictHenselization R T.henselization
        T.strictHenselization κ).1.symm.trans hdim),
    isNoetherianRing_of_ringEquiv T.henselization e.symm⟩

end StacksDraft

end
