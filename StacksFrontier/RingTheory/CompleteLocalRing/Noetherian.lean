module

public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian.FiniteProduct
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian.LeadingTerm
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian.FGMaximalIdeal

/-!
# Noetherian complete local rings

All rings here are commutative with unit. A *Noetherian complete local ring* is a Noetherian
local ring that is complete for the topology defined by its maximal ideal `m`.

If `R` is a Noetherian complete local ring, then for every proper ideal `J` of `R` the quotient
ring `R / J` is again a Noetherian complete local ring, and for every finite ring map `R → S` the
ring `S` is a finite product of Noetherian complete local rings. Moreover, a local ring that is
complete for its maximal-ideal-adic topology and whose maximal ideal is finitely generated is
Noetherian.

## Main definitions

* `IsNoetherianCompleteLocalRing R`: `R` is Noetherian, local, and complete with respect to its
  maximal ideal.
* `SingleStep R J a d`: each `a i` lies in `J ⊓ m ^ d i`, and every `x ∈ J ⊓ m ^ n` is congruent
  modulo `m ^ (n + 1)` to a combination `∑ i, c i * a i` with `c i ∈ m ^ (n - d i)`.

## Main results

* `quotient_isNoetherianCompleteLocalRing`: the quotient of a Noetherian complete local ring by
  a proper ideal is a Noetherian complete local ring.
* `finite_isProduct_isNoetherianCompleteLocalRing`: a finite algebra over a Noetherian complete
  local ring is a finite product of Noetherian complete local rings.
* `ideal_fg_of_adicComplete`: in a complete local ring, an ideal admitting single-step
  leading-term data is finitely generated.
* `complete_local_ring_noetherian`: a complete local ring with finitely generated maximal ideal
  is Noetherian.

## Conventions

A ring is *Noetherian* when every ideal is finitely generated, `IsNoetherianRing R`, and
*local* when it is nontrivial with a unique maximal ideal `IsLocalRing.maximalIdeal R`,
which is `IsLocalRing R`. It is *`I`-adically complete* when the canonical map
`R → lim_n R / I^n` is an isomorphism, equivalently when it is `I`-adically separated and
precomplete; this is `IsAdicComplete I R`, bundling `IsHausdorff I R` and
`IsPrecomplete I R`. A ring map `f : R → S` is *finite* when `S` is a finitely generated
`R`-module, and `S` is a *finite product* of `T_1, …, T_m` when there is a ring isomorphism
`S ≅ T_1 × ⋯ × T_m`.

The statement about quotients is restricted to proper ideals: `R / J` is local exactly when
`J ≠ ⊤`, since for `J = ⊤` the quotient is the zero ring, which is not local.

## References

* [Stacks Project, Tag 0325](https://stacks.math.columbia.edu/tag/0325)
* [Stacks Project, Tag 032B](https://stacks.math.columbia.edu/tag/032B)
-/
