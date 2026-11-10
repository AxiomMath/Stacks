module

public import StacksFrontier.RingTheory.Etale.CurveFiniteEtaleAffineLine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# An affine curve minus finitely many points is finite étale over an open of `𝔸¹`

Let `A` be a domain of finite type and of Krull dimension one over a perfect field `k`. Then
there are nonzero `a ∈ A` and `g ∈ k[X]` and a finite étale morphism

`π : Spec A_a ⟶ Spec k[X]_g`

over `Spec k`, where `Spec A_a = D(a)` is the complement in `Spec A` of the finite set `V(a)`
and `Spec k[X]_g = D(g)` is an open of the affine line `𝔸¹_k`. This is the scheme-theoretic
form of `Stacks.GenericFiniteEtale.exists_finite_etale_away`; the reason points have to be
removed is recorded in the docstring of
`StacksFrontier.RingTheory.Etale.CurveFiniteEtaleAffineLine`.
It is the first step of the reduction of the weight bound of Weil II on curves (Deligne,
Weil II 3.3) to opens of the affine line.

## Main results

* `Stacks.GenericFiniteEtale.finite_zeroLocus_singleton`: in a one-dimensional noetherian domain
  a nonzero element lies in finitely many primes.
* `Stacks.GenericFiniteEtale.exists_finite_etale_specAway`: the finite étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace Stacks.GenericFiniteEtale

/-- **A nonzero element of a one-dimensional noetherian domain lies in finitely many primes**:
they are all maximal, hence minimal over it. -/
theorem finite_zeroLocus_singleton {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : ringKrullDim A ≤ 1) {a : A} (ha : a ≠ 0) :
    (PrimeSpectrum.zeroLocus ({a} : Set A)).Finite := by
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by exact_mod_cast hA)
  have hfin := (Ideal.span ({a} : Set A)).finite_minimalPrimes_of_isNoetherianRing A
  refine (hfin.preimage (Function.Injective.injOn fun _ _ h => PrimeSpectrum.ext h)).subset
    fun p hp => ?_
  have hap : a ∈ p.asIdeal := hp rfl
  have hpb : p.asIdeal ≠ ⊥ := fun h => ha (by rw [h] at hap; exact hap)
  refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q ⟨hq, hIq⟩ hqp => ?_⟩
  have hqb : q ≠ ⊥ := fun h => ha (by
    rw [h] at hIq; exact (Ideal.span_singleton_le_iff_mem _).1 hIq)
  exact ((hq.isMaximal_of_ne_bot hqb).eq_of_le p.isPrime.ne_top hqp).ge

/-- **An affine curve minus finitely many points is finite étale over an open of `𝔸¹_k`.**
For a domain `A` of finite type and of Krull dimension one over a perfect field `k` there are
nonzero `a ∈ A`, `g ∈ k[X]` and a finite étale `π : Spec A_a ⟶ Spec k[X]_g` over `Spec k`; the
complement `V(a)` of `Spec A_a` in `Spec A` is finite. -/
theorem exists_finite_etale_specAway (k : Type u) [Field k] [PerfectField k] (A : Type u)
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hA : ringKrullDim A = 1) :
    ∃ (a : A) (_ : a ≠ 0) (g : k[X]) (_ : g ≠ 0)
      (π : Spec (.of (Localization.Away a)) ⟶ Spec (.of (Localization.Away g))),
      IsFinite π ∧ Etale π ∧
      π ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away a))) ∧
      (PrimeSpectrum.zeroLocus ({a} : Set A)).Finite := by
  obtain ⟨a, ha, g, hg, ψ, hfin, het, hk⟩ := exists_finite_etale_away k A hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine ⟨a, ha, g, hg, Spec.map (CommRingCat.ofHom ψ), ?_, ?_, ?_,
    finite_zeroLocus_singleton hA.le ha⟩
  · exact (IsFinite.SpecMap_iff _).2 hfin
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).2 het
  · rw [← Spec.map_comp]
    congr 1
    ext x
    exact hk x

end Stacks.GenericFiniteEtale
