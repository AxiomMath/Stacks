module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# A dimension function on the spectrum of a finite-dimensional Noetherian ring is bounded

Let `A` be a Noetherian ring of finite Krull dimension `d` and `δ` a dimension function on
`Spec(A)`. Along a specialization `𝔮 ⤳ 𝔭` the drop `δ(𝔮) - δ(𝔭)` is the length of a chain of
immediate specializations from `𝔮` to `𝔭`, hence at most the coheight of `𝔮`, hence at most `d`.
Every prime specializes from one of the finitely many minimal primes, so `δ` takes values in a
bounded interval. For the dimension function of a dualizing complex, `A` has finite dimension by
[Stacks, Tag 0A80], so that dimension function is bounded.

## Main results

* `TopologicalSpace.DimensionFunction.sub_le_coheight` — the drop along a specialization is at
  most the coheight of its source.
* `TopologicalSpace.DimensionFunction.exists_bound_of_ringKrullDim_lt_top` — a dimension function
  on the spectrum of a finite-dimensional Noetherian ring is bounded.
* `Dualizing.exists_bound_dualizingDimensionFunction` — the dimension function of a dualizing
  complex is bounded.

## References

* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace TopologicalSpace.DimensionFunction

variable {A : Type*} [CommRing A]

/-- **The drop of a dimension function along a specialization is at most the coheight of its
source.** If `𝔮 ≤ 𝔭` are primes of `A` then `δ(𝔮) - δ(𝔭) ≤ coheight(𝔮)`: a non-trivial
specialization begins with an immediate one, along which `δ` drops by exactly one and the
coheight by at least one. -/
theorem sub_le_coheight (δ : DimensionFunction (PrimeSpectrum A)) :
    ∀ (n : ℕ) (q p : PrimeSpectrum A), q ≤ p → δ q - δ p = n →
      (n : ℕ∞) ≤ Order.coheight q := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro q p hqp hn
    have hne : q ≠ p := by
      rintro rfl
      omega
    obtain ⟨z, hz, hzp⟩ := δ.exists_isImmediateSpecialization
      ((PrimeSpectrum.le_iff_specializes q p).1 hqp) hne
    have hstep := δ.step_immediate hz
    have h := ih z p ((PrimeSpectrum.le_iff_specializes z p).2 hzp) (by omega)
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := Nat.cast_succ n
      _ ≤ Order.coheight z + 1 := by gcongr
      _ ≤ Order.coheight q := Order.coheight_add_one_le
        (lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes q z).2 hz.1) hz.2.1)

/-- **A dimension function on the spectrum of a finite-dimensional Noetherian ring is
bounded.** Every prime lies above one of the finitely many minimal primes, from which `δ` drops
by at most the Krull dimension. -/
theorem exists_bound_of_ringKrullDim_lt_top [IsNoetherianRing A]
    (δ : DimensionFunction (PrimeSpectrum A)) (hdim : ringKrullDim A < ⊤) :
    ∃ N : ℕ, ∀ p : PrimeSpectrum A, -(N : ℤ) ≤ δ p ∧ δ p ≤ N := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Order.krullDim (PrimeSpectrum A) ≤ d := by
    change Order.krullDim (PrimeSpectrum A) < ⊤ at hdim
    induction h : Order.krullDim (PrimeSpectrum A) using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe e =>
      rw [h] at hdim
      induction e using ENat.recTopCoe with
      | top => exact absurd hdim (lt_irrefl _)
      | coe m => exact ⟨m, le_rfl⟩
  let f : Ideal A → ℤ := fun q => if hq : q.IsPrime then |δ ⟨q, hq⟩| else 0
  obtain ⟨M, hM⟩ := ((minimalPrimes.finite_of_isNoetherianRing A).image f).bddAbove
  refine ⟨M.toNat + d, fun p => ?_⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
  have hqprime : q.IsPrime := hq.isPrime
  set Q : PrimeSpectrum A := ⟨q, hqprime⟩
  have hQp : Q ≤ p := hqp
  have hfQ : |δ Q| ≤ M := by simpa [f, hqprime] using hM ⟨q, hq, rfl⟩
  have hle : δ p ≤ δ Q := by
    rcases eq_or_ne Q p with h | h
    · rw [h]
    · exact (δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes Q p).1 hQp) h).le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, δ Q - δ p = n := ⟨(δ Q - δ p).toNat, by omega⟩
  have hnd : n ≤ d := by
    have h2 : ((n : ℕ∞) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) :=
      ((WithBot.coe_le_coe.2
        (sub_le_coheight δ n Q p hQp hn)).trans (Order.coheight_le_krullDim Q)).trans hd
    exact_mod_cast h2
  have habs := abs_le.1 hfQ
  constructor <;> push_cast <;> omega

end TopologicalSpace.DimensionFunction

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-- **The dimension function of a dualizing complex takes values in a bounded interval.** If `K`
is a dualizing complex over a Noetherian ring `A` then there is an `N : ℕ` with
`-N ≤ δ_K(𝔭) ≤ N` for every prime `𝔭` of `A`: the ring has finite Krull dimension by
[Stacks, Tag 0A80], and a dimension function on the spectrum of a finite-dimensional Noetherian
ring is bounded. -/
theorem exists_bound_dualizingDimensionFunction {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsDualizingComplex K) :
    ∃ N : ℕ, ∀ p : PrimeSpectrum A,
      -(N : ℤ) ≤ dualizingDimensionFunction.{u, u} K hK p ∧
        dualizingDimensionFunction.{u, u} K hK p ≤ (N : ℤ) :=
  (dualizingDimensionFunction.{u, u} K hK).exists_bound_of_ringKrullDim_lt_top
    (ringKrullDim_lt_top_of_isDualizingComplex hK)

end Dualizing
