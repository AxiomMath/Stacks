module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of the induced homomorphism of local rings

Let `A → B` be a homomorphism of commutative rings and let `q` be a prime of `B` lying over a
prime `p` of `A`. The ring map induces a local homomorphism `A_p → B_q` of the localizations,
and this file identifies its flatness with a statement about `B_q` as a module over `A` itself:
the homomorphism `A_p → B_q` is flat exactly when `B_q` is flat as an `A`-module.

This is the form in which flatness of a morphism of schemes at a point, which is flatness of
the induced map of local rings, is read off from an affine chart: on compatible affine opens the
map of local rings is the induced map of localizations, and the right-hand side of the
equivalence below is a condition on the localized module of sections.

## Main results

* `Module.flat_localizationAtPrime_iff_flat_localRingHom`: flatness of `A_p → B_q` is flatness
  of `B_q` as an `A`-module.

## Implementation notes

Mathlib's `RingHom.Flat.localRingHom` gives the implication from flatness of `A → B` to
flatness of `A_p → B_q`; the statement here is a different one, an equivalence in which the
left-hand side is unchanged but the right-hand side localizes only the target. The content is
that `A_p` is a localization of `A` and flatness over a ring is unaffected by replacing it with
a localization through which the module structure factors
(`Module.flat_iff_of_isLocalization`).

Since `Localization q.primeCompl` is by definition `LocalizedModule q.primeCompl B`, the
statement applies verbatim when the localization is presented as a localized module.
-/

@[expose] public section

namespace Module

/-- **Flatness of the induced map of local rings is flatness of the localized target over the
base.** For a prime `q` of `B` lying over a prime `p` of `A`, the induced local homomorphism
`A_p → B_q` is flat exactly when `B_q` is flat as a module over `A`. -/
@[sga "1 IV 6.8" "special case"]
theorem flat_localizationAtPrime_iff_flat_localRingHom {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    Module.Flat A (Localization.AtPrime q) ↔
      (Localization.localRingHom p q (algebraMap A B) Ideal.LiesOver.over).Flat := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun x =>
      (Localization.localRingHom_to_map p q (algebraMap A B) Ideal.LiesOver.over x).symm
  rw [RingHom.Flat, Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]

end Module
