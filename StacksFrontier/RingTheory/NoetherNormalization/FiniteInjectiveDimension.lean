module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Dimension bound in Noether normalization

If `k[X₁, …, Xₛ] ⟶ A` is a finite injective map of `k`-algebras (a Noether normalization of `A`),
then `s ≤ dim A`: the map on spectra is surjective (lying over) and closed (integrality), so
specializations lift along it and the dimension of the target `𝔸ˢ_k`, which is `s`, is at most
that of `Spec A` ([Stacks, Tag 02JF]). This bounds the dimension of the base of the fibration
by curves `Spec A ⟶ 𝔸^{s-1}_k` used in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves.

## Main results

* `Stacks.NoetherNormalization.natCast_le_ringKrullDim_of_finite_of_injective`.
-/

@[expose] public section

namespace Stacks.NoetherNormalization

/-- **The number of variables of a Noether normalization is at most the dimension.**  If
`g : k[X₁, …, Xₛ] ⟶ A` is finite and injective, then `s ≤ dim A`. -/
theorem natCast_le_ringKrullDim_of_finite_of_injective (k : Type*) [Field k] {A : Type*}
    [CommRing A] [Algebra k A] {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hfin : g.toRingHom.Finite) :
    (s : WithBot ℕ∞) ≤ ringKrullDim A := by
  have hdim : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← hdim, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have hint : g.toRingHom.IsIntegral := hfin.to_isIntegral
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  refine Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
    (PrimeSpectrum.comap g.toRingHom) (PrimeSpectrum.continuous_comap _) ?_
    (Or.inl (PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint).specializingMap)
  intro P
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal A)
    (by
      intro x hx
      have : g x = 0 := hx
      rw [← map_zero g] at this
      rw [hinj this]
      exact P.asIdeal.zero_mem)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQP⟩

end Stacks.NoetherNormalization
