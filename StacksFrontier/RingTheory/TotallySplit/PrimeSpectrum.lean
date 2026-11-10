module

public import Mathlib.RingTheory.TotallySplit
public import StacksCore.Tactic.StacksAttribute

/-!
# The spectrum of a totally split algebra over a field

A totally split algebra over a field is isomorphic to a finite product of copies of that field,
so its spectrum is finite and its cardinality is the dimension of the algebra. Over a separably
closed field this applies to every étale algebra, which is how a degree is read off from a
point count after passing to a separable closure.

## Main results

* `Algebra.IsFiniteSplit.cardinalMk_primeSpectrum_eq_finrank`: the spectrum of a totally split
  algebra over a field has as many points as the algebra has dimensions.
* `Algebra.IsFiniteSplit.natCard_algHom_eq_finrank`: a totally split algebra over a field has as
  many rational points as the algebra has dimensions.

## Implementation notes

The hypothesis is `Algebra.IsFiniteSplit`, which is the weakest form under which the statement
holds; over a separably closed field Mathlib supplies it as an instance for every algebra that
is essentially of finite type and formally étale, so the étale case needs no separate statement.

The field and the algebra are allowed to live in different universes: the dimension is a natural
number, so only the cardinality of the spectrum carries a universe, and it is the universe of the
algebra.

## References

* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
-/

@[expose] public section

universe u v

namespace Algebra.IsFiniteSplit

/-- The spectrum of a totally split algebra over a field has exactly as many points as the
dimension of the algebra. -/
public theorem cardinalMk_primeSpectrum_eq_finrank {K : Type u} {A : Type v} [Field K]
    [CommRing A] [Algebra K A] [Algebra.IsFiniteSplit K A] :
    Cardinal.mk (PrimeSpectrum A) = Module.finrank K A := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K A
  have hrank : Module.finrank K A = n := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi]
    simp
  have epts : PrimeSpectrum A ≃ Fin n :=
    (PrimeSpectrum.comapEquiv e.toRingEquiv).toEquiv.trans <|
      (PrimeSpectrum.sigmaToPiHomeo (fun _ : Fin n ↦ K)).toEquiv.symm.trans <|
        (Equiv.sigmaEquivProd (Fin n) (PrimeSpectrum K)).trans <|
          Equiv.prodUnique (Fin n) (PrimeSpectrum K)
  rw [hrank, Cardinal.mk_eq_nat_iff]
  exact ⟨epts⟩

/-- A totally split algebra over a field has exactly as many rational points, that is algebra
maps to the field, as the dimension of the algebra. -/
public theorem natCard_algHom_eq_finrank {K : Type u} {A : Type v} [Field K]
    [CommRing A] [Algebra K A] [Algebra.IsFiniteSplit K A] :
    Nat.card (A →ₐ[K] K) = Module.finrank K A := by
  rw [Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K A)]
  change Cardinal.toNat (Cardinal.mk (PrimeSpectrum A)) = _
  rw [cardinalMk_primeSpectrum_eq_finrank (K := K), Cardinal.toNat_natCast]

end Algebra.IsFiniteSplit

end
