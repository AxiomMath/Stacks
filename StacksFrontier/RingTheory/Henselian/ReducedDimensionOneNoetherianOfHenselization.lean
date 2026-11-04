module

public import StacksFrontier.RingTheory.Henselian.HenselizationCompletion
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducedness, dimension one, and Noetherianity are invariant under henselization

A local ring `R` which is reduced, Noetherian, and of Krull dimension one has these three
properties also for any henselization `H`, in any universe. Reducedness and Noetherianity are
Stacks 06DH and 06LJ, dimension invariance is Stacks 06LK; each is already available for a
henselization in the *same* universe as `R`, alongside a strict henselization, in
`StacksFrontier.RingTheory.Henselian.PermanenceOfProperties`. The cross-universe uniqueness of
henselizations of `StacksFrontier.RingTheory.Henselian.HenselizationCompletion` transports the
same-universe statement to an arbitrary henselization `H`, exactly as it already does there for
regularity.

## Main results

* `StacksDraft.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization`: a
  reduced Noetherian local ring of Krull dimension one has a henselization, in any universe,
  which is reduced, Noetherian, and of Krull dimension one.

## References

* [Stacks Project, Tag 06DH](https://stacks.math.columbia.edu/tag/06DH)
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ)
* [Stacks Project, Tag 06LK](https://stacks.math.columbia.edu/tag/06LK)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace StacksDraft

/-- **Reducedness, dimension one, and Noetherianity are invariant under henselization.** If a
local ring `R` is reduced, Noetherian, and of Krull dimension one, then so is any henselization
`H` of `R`, even one living in a different universe.

The same-universe statements (Stacks 06DH, 06LK, 06LJ) are applied to the henselization and
strict henselization supplied by `IsLocalRing.henselizationTower`, and transported to `H` along
the cross-universe isomorphism `StacksDraft.exists_ringEquiv_of_isHenselization`. -/
@[ega "IV 18.6.9" "(i), special case",
  sga "4 VIII 4.1" "special case",
  sga "5 I 3.1.3" "special case"]
theorem isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization
    {R : Type u} {H : Type v} [CommRing R] [IsLocalRing R] [IsReduced R] [IsNoetherianRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) H]
    (hdim : ringKrullDim R = 1) :
    IsReduced H ∧ ringKrullDim H = 1 ∧ IsNoetherianRing H := by
  let κ := SeparableClosure (ResidueField R)
  let T := henselizationTower R κ
  obtain ⟨e, -⟩ := exists_ringEquiv_of_isHenselization (R := R) (H := H) (H' := T.henselization)
  have hredT : IsReduced T.henselization :=
    ((isReduced_tfae_henselization_strictHenselization R T.henselization
      T.strictHenselization κ).out 1 2).mp (inferInstance : IsReduced R)
  have hdimT : ringKrullDim T.henselization = 1 :=
    (ringKrullDim_eq_henselization_eq_strictHenselization R T.henselization
      T.strictHenselization κ).1.symm.trans hdim
  have hnoethT : IsNoetherianRing T.henselization :=
    ((isNoetherianRing_iff_henselizations R T.henselization T.strictHenselization κ).1).1
      inferInstance
  exact ⟨isReduced_of_injective e e.injective,
    (ringKrullDim_eq_of_ringEquiv e).trans hdimT,
    isNoetherianRing_of_ringEquiv T.henselization e.symm⟩

end StacksDraft

end
