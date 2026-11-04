module

public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Ring maps that identify local rings

A ring map `φ : A → B` *identifies local rings* if for every prime `𝔮` of `B` the canonical
map `A_{φ⁻¹(𝔮)} → B_𝔮` is an isomorphism.

## Main definitions

* `Algebra.IdentifiesLocalRings` is the predicate that an algebra identifies local rings.

## Main results

* `Algebra.identifiesLocalRings_self`: a ring identifies its own local rings.
* `Algebra.IdentifiesLocalRings.localRingEquiv` packages the defining bijection at a prime as
  a ring equivalence of local rings.

## Implementation notes

Part (1) of Stacks 096E, the *local isomorphism* property, is Mathlib's `Algebra.IsLocalIso`;
part (2) is `Algebra.IdentifiesLocalRings` below.

Mathlib's part (1) asks each `B_g` to be a *standard* open immersion over `A`, where the
source asks only that `Spec(B_g) → Spec(A)` be an open immersion. The two agree: an open
immersion of affines is standard after a further localization of the source, and the
`∀ 𝔮, ∃ g ∉ 𝔮` in front absorbs that localization.

"Isomorphism" is expressed as `Function.Bijective` of Mathlib's
`Localization.localRingHom`, which is the canonical map on localizations at a prime and its
preimage; a bijective ring homomorphism is a ring isomorphism, and
`Algebra.IdentifiesLocalRings.localRingEquiv` performs that packaging. The source prime is
spelled `q.comap (algebraMap R S)` with the defining equation `rfl`, so that the index of the
localization is syntactically the preimage and Mathlib's `localRingHom` simp set applies
without a rewrite.

The statement is over `CommSemiring`, matching `Algebra.IsLocalIso`, rather than over
`CommRing` as in the source.

## References

* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
-/

@[expose] public section

namespace Algebra

/-- An algebra *identifies local rings* if for every prime `q` of the target the canonical map
from the localization of the source at the preimage of `q` to the localization of the target at
`q` is an isomorphism. -/
@[stacks 096E "part (2): identifies local rings"]
abbrev IdentifiesLocalRings (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] :
    Prop :=
  ∀ (q : Ideal S) [q.IsPrime],
    Function.Bijective (Localization.localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl)

/-- A ring identifies its own local rings. -/
theorem identifiesLocalRings_self (R : Type*) [CommSemiring R] : IdentifiesLocalRings R R := by
  intro q _
  have h : Localization.localRingHom (q.comap (algebraMap R R)) q (algebraMap R R) rfl =
      Localization.localRingHom q q (RingHom.id R) (Ideal.comap_id q).symm := rfl
  rw [h, Localization.localRingHom_id]
  exact Function.bijective_id

/-- The ring equivalence of local rings at a prime of the target provided by an algebra that
identifies local rings. -/
noncomputable def IdentifiesLocalRings.localRingEquiv {R S : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] (h : IdentifiesLocalRings R S) (q : Ideal S) [q.IsPrime] :
    Localization.AtPrime (q.comap (algebraMap R S)) ≃+* Localization.AtPrime q :=
  RingEquiv.ofBijective _ (h q)

/-- As a ring homomorphism, `IdentifiesLocalRings.localRingEquiv` is the canonical map
`Localization.localRingHom` on localizations at a prime of the target and its preimage. -/
@[simp]
theorem IdentifiesLocalRings.coe_localRingEquiv {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] (h : IdentifiesLocalRings R S) (q : Ideal S) [q.IsPrime] :
    (h.localRingEquiv q : Localization.AtPrime (q.comap (algebraMap R S)) →+* _) =
      Localization.localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl :=
  rfl

end Algebra

end
