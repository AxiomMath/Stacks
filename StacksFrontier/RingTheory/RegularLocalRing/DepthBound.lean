module

public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# The depth of a regular local ring is its Krull dimension

A regular local ring is Cohen–Macaulay: its depth along the maximal ideal equals its Krull
dimension. That is `Module.IsMaximalCohenMacaulay R R`, the second conclusion of
`IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay`
([Stacks, Tag 00NQ]). This file records the equality on its own, and the lower bound on the
depth that it gives, which is what the depth hypotheses of the Enriques–Severi–Zariski theorems
are stated with.

## Main results

* `IsRegularLocalRing.depth_eq_ringKrullDim`: `depth_𝔪(R) = dim R` for `R` regular local.
* `IsRegularLocalRing.le_depth_of_le_ringKrullDim`: a lower bound on `dim R` is a lower bound on
  `depth_𝔪(R)`.
* `IsRegularLocalRing.two_le_depth_of_two_le_ringKrullDim`: the case needed by
  [Stacks, Tag 0FD9], whose hypothesis (2) is `depth(𝒪_{X,x}) ≥ 2` at the closed points.

## Implementation notes

`Module.depth` takes values in `ℕ∞` and `ringKrullDim` in `WithBot ℕ∞`, so the equality is
stated in `WithBot ℕ∞` — that is how `Module.IsMaximalCohenMacaulay` is defined — while the
bounds are stated in `ℕ∞`, which is where the consumers want them. The two are related by
`WithBot.coe_le_coe`.

The derivation of the bound at `2` existed only inside the proof of
`Module.free_of_isReflexive_of_ringKrullDim_le_two`
(`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RegularDimensionTwo.lean`), where it is taken
at `dim R = 2` exactly; nothing in the repository stated it as a lemma, or for a lower bound.

## References

* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
* [Stacks Project, Tag 00NF](https://stacks.math.columbia.edu/tag/00NF)
-/

@[expose] public section

namespace IsRegularLocalRing

variable (R : Type*) [CommRing R] [IsRegularLocalRing R]

/-- **A regular local ring is Cohen–Macaulay**: its depth along the maximal ideal is its Krull
dimension, [Stacks, Tag 00NQ]. -/
theorem depth_eq_ringKrullDim :
    ((Module.depth R (IsLocalRing.maximalIdeal R) R : ℕ∞) : WithBot ℕ∞) = ringKrullDim R :=
  (isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2

/-- **A lower bound on the Krull dimension of a regular local ring is a lower bound on its
depth.** -/
theorem le_depth_of_le_ringKrullDim {d : ℕ∞} (hdim : (d : WithBot ℕ∞) ≤ ringKrullDim R) :
    d ≤ Module.depth R (IsLocalRing.maximalIdeal R) R :=
  WithBot.coe_le_coe.mp ((depth_eq_ringKrullDim R).symm ▸ hdim)

/-- **A regular local ring of Krull dimension at least two has depth at least two.** This is the
depth hypothesis of [Stacks, Tag 0FD9] at a point whose local ring is regular — in particular at
every point of a scheme smooth over a field. -/
theorem two_le_depth_of_two_le_ringKrullDim (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R) :
    (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) R :=
  le_depth_of_le_ringKrullDim R (d := 2) (by exact_mod_cast hdim)

end IsRegularLocalRing

end
