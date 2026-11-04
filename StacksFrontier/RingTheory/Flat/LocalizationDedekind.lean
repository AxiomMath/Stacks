module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness over localizations of dimension at most one

A Noetherian integrally closed domain localized at a prime of height at most one is a Dedekind
domain, and over a Dedekind domain a torsion-free module is flat. So an injective map of domains
`A ⟶ B` becomes flat after localizing at a prime `q` of `B` whose contraction to `A` has height at
most one. In a two-dimensional local ring every prime other than the maximal ideal has height at
most one.

## Main results

* `Stacks.Flat.isDedekindDomain_localization_atPrime`: the localization of a Noetherian
  integrally closed domain at a prime of height at most one is a Dedekind domain.
* `Stacks.Flat.height_le_one_of_ne_maximalIdeal`: the primes of a two-dimensional Noetherian
  local ring other than its maximal ideal have height at most one.
* `Stacks.Flat.flat_localRingHom_of_isDedekindDomain`: an injective map of domains is flat at
  every prime of the target over which the source is locally Dedekind.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Flat

open IsLocalRing

/-- At a prime of height at most one, the localization of a Noetherian integrally closed domain
is a Dedekind domain. -/
theorem isDedekindDomain_localization_atPrime {A : Type u} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] (hp : p.height ≤ 1) :
    IsDedekindDomain (Localization.AtPrime p) := by
  have hdim : ringKrullDim (Localization.AtPrime p) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact_mod_cast hp
  have : Ring.KrullDimLE 1 (Localization.AtPrime p) := (Ring.krullDimLE_iff).mpr hdim
  have : Ring.DimensionLEOne (Localization.AtPrime p) :=
    ⟨fun hp0 hp => hp.isMaximal_of_ne_bot hp0⟩
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  exact { }

/-- In a local ring of dimension two, every prime other than the maximal ideal has height at
most one. -/
theorem height_le_one_of_ne_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 2) (p : Ideal A) [p.IsPrime]
    (hp : p ≠ maximalIdeal A) : p.height ≤ 1 := by
  have hlt : p < maximalIdeal A := lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp
  have hm : (maximalIdeal A).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [hdim] at this
    exact WithBot.coe_injective this
  have : (maximalIdeal A).FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hm]; exact ENat.natCast_ne_top 2
  have h := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  rw [hm] at h
  exact Order.le_of_lt_succ h

variable {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]

omit [IsDomain A] in
/-- Over a Dedekind localization, an injective map of domains localizes to a flat map. -/
theorem flat_localRingHom_of_isDedekindDomain (φ : A →+* B) (hφ : Function.Injective φ)
    (q : Ideal B) [q.IsPrime] [IsDedekindDomain (Localization.AtPrime (q.comap φ))] :
    (Localization.localRingHom (q.comap φ) q φ rfl).Flat := by
  set ψ := Localization.localRingHom (q.comap φ) q φ rfl
  have hψ : Function.Injective ψ :=
    IsLocalization.map_injective_of_injective' (S := B) (M := (q.comap φ).primeCompl) (f := φ)
      (Rₘ := Localization.AtPrime (q.comap φ)) (Sₘ := Localization.AtPrime q) (N := q.primeCompl)
      (hf := fun _ hx => hx) (hN := fun h => h q.zero_mem) (hf' := hφ)
  let := ψ.toAlgebra
  change Module.Flat _ _
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).mp hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  rw [Submonoid.smul_def, Algebra.smul_def] at hax
  exact (mul_eq_zero.mp hax).resolve_left fun h => ha0 (hψ (h.trans (map_zero ψ).symm))

end Stacks.Flat

end
