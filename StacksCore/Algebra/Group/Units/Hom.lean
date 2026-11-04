module

public import Mathlib.Algebra.Group.Units.Hom
import StacksCore.Tactic.StacksAttribute

/-! # Local homomorphisms

Stacks tag 07BI, last sentence: a *local homomorphism of local rings* is a ring map
`φ : R → S` between local rings with `φ(𝔪_R) ⊆ 𝔪_S`.

Mathlib's `IsLocalHom` is stated the other way round — `φ` reflects units, i.e. `IsUnit (φ a)`
implies `IsUnit a` — and for a monoid map, not specifically a map of local rings. For local
rings the two conditions agree, which is exactly clauses (1) ⇔ (2) of
`IsLocalRing.local_hom_TFAE` (Stacks tag 07BJ, already tagged upstream). The reflects-units
form is the useful one in Lean because it needs no `IsLocalRing` instance to state, so it also
applies to the many maps that are local before either side is known to be local.
-/

@[expose] public section

add_to_stacks 07BI "A local homomorphism of local rings: `φ(𝔪_R) ⊆ 𝔪_S`. Mathlib states the
  equivalent reflects-units condition, which needs no `IsLocalRing` instance; the equivalence
  is `IsLocalRing.local_hom_TFAE` (tag 07BJ)." IsLocalHom
