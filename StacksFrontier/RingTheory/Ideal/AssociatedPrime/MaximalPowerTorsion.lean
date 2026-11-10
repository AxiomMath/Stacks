module

public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.PowerTorsion
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# `𝔪`-power torsion over a local ring

Let `(A, 𝔪)` be a Noetherian local ring and let `M` be an `A`-module. The `𝔪`-power torsion of
`M` — Mathlib's `Ideal.primaryComponent M 𝔪`, the sections of `M` supported at the closed point —
is exactly the obstruction to `𝔪` being an associated prime of `M`:

* if `𝔪` is not an associated prime of `M`, the `𝔪`-power torsion vanishes, because an associated
  prime containing the annihilator of a nonzero torsion element contains `𝔪` and is therefore
  equal to `𝔪`;
* conversely `𝔪` is never an associated prime of `M / M[𝔪^∞]`, which is the case `J = 𝔪` of
  `associatedPrimes_quotient_primaryComponent`.

For an `A`-algebra `D` the `𝔪`-power torsion is moreover an ideal of `D`, so that the quotient
is again a ring; that ideal is `Stacks.primaryComponentIdeal`, and the second statement is
transported along `Submodule.Quotient.restrictScalarsEquiv` to the ring quotient by it.

## Main definitions

* `Stacks.primaryComponentIdeal` — the `I`-power torsion of an `A`-algebra, as an ideal.

## Main results

* `Stacks.eq_zero_of_mem_primaryComponent` — a module without `𝔪` as an associated prime has no
  nonzero `𝔪`-power torsion.
* `Stacks.not_isAssociatedPrime_maximalIdeal_quotient_primaryComponent`,
  `Stacks.not_isAssociatedPrime_maximalIdeal_quotient_primaryComponentIdeal` — `𝔪` is not an
  associated prime of the quotient by the `𝔪`-power torsion, as a module and as a ring.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Stacks

section Module

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- Membership in the `I`-power torsion, spelled with a power of `I` annihilating the element. -/
theorem mem_primaryComponent_iff {I : Ideal A} {x : M} :
    x ∈ Ideal.primaryComponent M I ↔ ∃ k : ℕ, ∀ a ∈ I ^ k, a • x = 0 := by
  rw [Ideal.primaryComponent_mem]
  refine exists_congr fun k => ?_
  rw [Submodule.mem_torsionBySet_iff]
  exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩

/-- An element annihilated by every element of some power `I ^ k` lies in the `I`-power
torsion. -/
theorem mem_primaryComponent_of_pow_smul_eq_zero {I : Ideal A} {x : M} {k : ℕ}
    (h : ∀ a ∈ I ^ k, a • x = 0) : x ∈ Ideal.primaryComponent M I :=
  mem_primaryComponent_iff.mpr ⟨k, h⟩

variable [IsLocalRing A]

/-- **A module without `𝔪` as an associated prime has no nonzero `𝔪`-power torsion.** -/
theorem eq_zero_of_mem_primaryComponent [IsNoetherianRing A]
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) M) {x : M}
    (hx : x ∈ Ideal.primaryComponent M (maximalIdeal A)) : x = 0 := by
  by_contra hx0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A x hx0
  obtain ⟨k, hk⟩ := mem_primaryComponent_iff.mp hx
  have hmk : maximalIdeal A ^ k ≤ Submodule.colon (⊥ : Submodule A M) {x} := fun a ha =>
    Submodule.mem_colon_singleton.mpr (by rw [hk a ha]; exact Submodule.zero_mem _)
  have hmP : maximalIdeal A ≤ P := fun a ha =>
    hP.isPrime.mem_of_pow_mem k (hle (hmk (Ideal.pow_mem_pow ha k)))
  exact hass ((maximalIdeal.isMaximal A).eq_of_le hP.isPrime.ne_top hmP ▸ hP)

/-- **A module whose `𝔪`-power torsion vanishes does not have `𝔪` as an associated prime.** -/
theorem not_isAssociatedPrime_maximalIdeal_of_forall_eq_zero [IsNoetherianRing A]
    (h : ∀ x : M, x ∈ Ideal.primaryComponent M (maximalIdeal A) → x = 0) :
    ¬ IsAssociatedPrime (maximalIdeal A) M := by
  intro hass
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hass
  have hx0 : x = 0 := by
    refine h x (mem_primaryComponent_of_pow_smul_eq_zero (k := 1) fun a ha => ?_)
    have hmem : a ∈ Submodule.colon (⊥ : Submodule A M) {x} := by
      rw [← hx]; simpa using ha
    simpa using Submodule.mem_colon_singleton.mp hmem
  refine hprime.ne_top ?_
  rw [hx, hx0, Submodule.colon_singleton_zero]

/-- **The maximal ideal is not an associated prime of the quotient by the `𝔪`-power torsion.** -/
theorem not_isAssociatedPrime_maximalIdeal_quotient_primaryComponent [IsNoetherianRing A] :
    ¬ IsAssociatedPrime (maximalIdeal A)
      (M ⧸ Ideal.primaryComponent M (maximalIdeal A)) := by
  intro h
  have hmem : maximalIdeal A ∈
      associatedPrimes A (M ⧸ Ideal.primaryComponent M (maximalIdeal A)) := h
  rw [associatedPrimes_quotient_primaryComponent M (maximalIdeal A)] at hmem
  exact hmem.2 (Set.mem_ofPred_eq ▸ le_rfl)

end Module

section Algebra

variable (A : Type u) [CommRing A] (D : Type v) [CommRing D] [Algebra A D]

/-- **The `I`-power torsion of an `A`-algebra, as an ideal.** Its underlying set is the `I`-power
torsion `Ideal.primaryComponent D I` of `D` regarded as an `A`-module. -/
def primaryComponentIdeal (I : Ideal A) : Ideal D where
  carrier := (Ideal.primaryComponent D I : Set D)
  zero_mem' := Submodule.zero_mem _
  add_mem' hx hy := Submodule.add_mem _ hx hy
  smul_mem' c x hx := by
    obtain ⟨k, hk⟩ := mem_primaryComponent_iff.mp hx
    refine mem_primaryComponent_of_pow_smul_eq_zero (k := k) fun a ha => ?_
    have h := hk a ha
    rw [smul_eq_mul, Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap A D a) c, mul_assoc,
      ← Algebra.smul_def, h, mul_zero]

/-- An element lies in `primaryComponentIdeal A D I` if and only if it lies in the `I`-power
torsion of `D` as an `A`-module. -/
@[simp]
theorem mem_primaryComponentIdeal {I : Ideal A} {x : D} :
    x ∈ primaryComponentIdeal A D I ↔ x ∈ Ideal.primaryComponent D I := Iff.rfl

/-- Restricting scalars of `primaryComponentIdeal A D I` to `A` gives the `I`-power torsion
`Ideal.primaryComponent D I`. -/
theorem restrictScalars_primaryComponentIdeal (I : Ideal A) :
    (primaryComponentIdeal A D I).restrictScalars A = Ideal.primaryComponent D I := rfl

variable [IsLocalRing A]

/-- **The maximal ideal is not an associated prime of the ring quotient by the `𝔪`-power
torsion.** -/
theorem not_isAssociatedPrime_maximalIdeal_quotient_primaryComponentIdeal [IsNoetherianRing A] :
    ¬ IsAssociatedPrime (maximalIdeal A)
      (D ⧸ primaryComponentIdeal A D (maximalIdeal A)) := by
  rw [← (Submodule.Quotient.restrictScalarsEquiv A
    (primaryComponentIdeal A D (maximalIdeal A))).isAssociatedPrime_iff]
  exact not_isAssociatedPrime_maximalIdeal_quotient_primaryComponent

end Algebra

end Stacks

end
