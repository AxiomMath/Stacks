module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bounding orders through a reduction map that is injective on prime-to-`ℓ` torsion

Let `red : M →+ N` be a homomorphism of additive commutative groups with `N` finite, and let `ℓ`
be a prime such that no nonzero element of `M` killed by a prime `q ≠ ℓ` lies in the kernel of
`red`. Then for every element `x` of finite order `n`, the part of `n` prime to `ℓ` is at most
`#N`: the element `ℓ ^ {v_ℓ(n)} • x` has order prime to `ℓ`, and its order is the order of its
image under `red`, since a drop of the order would produce an element of prime order `q ≠ ℓ` in
the kernel.

Two such bounds, for two different primes, bound the order itself.

## Main results

* `ordCompl_addOrderOf_le_of_injective_on_prime`: the bound `ordCompl[ℓ] n ≤ #N`.
* `addOrderOf_le_mul_of_ordCompl_le`: `n ≤ C₁ * C₂` from `ordCompl[ℓ₁] n ≤ C₁` and
  `ordCompl[ℓ₂] n ≤ C₂` for primes `ℓ₁ ≠ ℓ₂`.

These are the group-theoretic steps of the reduction argument showing that torsion points of
bounded degree of an abelian variety have bounded order.
-/

@[expose] public section

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- If `red : M →+ N` has no nonzero element of prime order `q ≠ ℓ` in its kernel and `N` is
finite, then the part prime to `ℓ` of the order of any element of finite order of `M` is at most
`#N`. -/
theorem ordCompl_addOrderOf_le_of_injective_on_prime [Finite N] (red : M →+ N) {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hred : ∀ q : ℕ, q.Prime → q ≠ ℓ → ∀ z : M, q • z = 0 → red z = 0 → z = 0)
    {x : M} (hx : IsOfFinAddOrder x) :
    ordCompl[ℓ] (addOrderOf x) ≤ Nat.card N := by
  set n := addOrderOf x with hn
  have hn0 : 0 < n := hx.addOrderOf_pos
  set y := (ordProj[ℓ] n) • x with hy
  have hdvd : ordProj[ℓ] n ∣ n := Nat.ordProj_dvd n ℓ
  have hyord : addOrderOf y = ordCompl[ℓ] n := by
    have h := addOrderOf_nsmul' x (n := ordProj[ℓ] n) (Nat.ordProj_pos n ℓ).ne'
    rw [← hn, Nat.gcd_eq_right hdvd] at h
    exact h
  set m := ordCompl[ℓ] n with hm
  have hm0 : 0 < m := Nat.ordCompl_pos ℓ hn0.ne'
  have hcop : ¬ ℓ ∣ m := Nat.not_dvd_ordCompl hℓ hn0.ne'
  set r := addOrderOf (red y) with hr
  have hrm : r ∣ m := by
    rw [hr, ← hyord]
    exact addOrderOf_map_dvd red y
  have hrm' : r = m := by
    by_contra hne
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrm hm0
    obtain ⟨t, ht⟩ := hrm
    have ht1 : 1 < t := by
      rcases t with _ | _ | t
      · rw [mul_zero] at ht; omega
      · exact absurd (by simp [ht]) hne
      · omega
    obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt ht1)
    have hqm : q ∣ m := ht ▸ Dvd.dvd.mul_left hqt r
    have hqℓ : q ≠ ℓ := fun h => hcop (h ▸ hqm)
    obtain ⟨s, hs⟩ := hqt
    set z := (r * s) • y with hz
    have hmz : m = q * (r * s) := by rw [ht, hs, Nat.mul_left_comm]
    have hqz : q • z = 0 := by
      rw [hz, smul_smul, ← hmz]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hyord ▸ dvd_refl m)
    have hredz : red z = 0 := by
      rw [hz, map_nsmul]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hr ▸ dvd_mul_right r s)
    have hz0 : z = 0 := hred q hq hqℓ z hqz hredz
    have hlt : r * s < m := by
      rw [hmz]
      have : 0 < r * s := Nat.pos_of_ne_zero (by
        intro h0; rw [h0, mul_zero] at hmz; omega)
      exact lt_mul_of_one_lt_left this hq.one_lt
    have : m ∣ r * s := by
      rw [← hyord]
      exact addOrderOf_dvd_of_nsmul_eq_zero hz0
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (by
      intro h0; rw [h0, mul_zero] at hmz; omega)) this) (not_le.mpr hlt)
  rw [← hrm']
  exact addOrderOf_le_card

/-- **Two prime-to-part bounds bound the order.** If `ℓ₁ ≠ ℓ₂` are primes and the parts of `n`
prime to `ℓ₁` and to `ℓ₂` are at most `C₁` and `C₂`, then `n ≤ C₁ * C₂`. -/
theorem le_mul_of_ordCompl_le {n : ℕ} (hn : n ≠ 0) {ℓ₁ ℓ₂ C₁ C₂ : ℕ} (h₁ : ℓ₁.Prime)
    (h₂ : ℓ₂.Prime) (hne : ℓ₁ ≠ ℓ₂) (hC₁ : ordCompl[ℓ₁] n ≤ C₁) (hC₂ : ordCompl[ℓ₂] n ≤ C₂) :
    n ≤ C₁ * C₂ := by
  have hdvd : ordProj[ℓ₁] n ∣ ordCompl[ℓ₂] n := by
    have hcop : Nat.Coprime (ordProj[ℓ₁] n) (ordProj[ℓ₂] n) :=
      Nat.coprime_pow_primes _ _ h₁ h₂ hne
    have h1 : ordProj[ℓ₁] n ∣ ordProj[ℓ₂] n * ordCompl[ℓ₂] n := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
      exact Nat.ordProj_dvd n ℓ₁
    exact hcop.dvd_of_dvd_mul_left h1
  have hpos : 0 < ordCompl[ℓ₂] n := Nat.ordCompl_pos ℓ₂ hn
  calc n = ordProj[ℓ₁] n * ordCompl[ℓ₁] n := (Nat.ordProj_mul_ordCompl_eq_self n ℓ₁).symm
    _ ≤ ordCompl[ℓ₂] n * ordCompl[ℓ₁] n :=
        Nat.mul_le_mul_right _ (Nat.le_of_dvd hpos hdvd)
    _ ≤ C₂ * C₁ := Nat.mul_le_mul hC₂ hC₁
    _ = C₁ * C₂ := mul_comm _ _

/-- **Two reductions bound the order.** Combining
`ordCompl_addOrderOf_le_of_injective_on_prime` for two primes `ℓ₁ ≠ ℓ₂`. -/
theorem addOrderOf_le_mul_of_ordCompl_le {x : M} (hx : IsOfFinAddOrder x) {ℓ₁ ℓ₂ C₁ C₂ : ℕ}
    (h₁ : ℓ₁.Prime) (h₂ : ℓ₂.Prime) (hne : ℓ₁ ≠ ℓ₂)
    (hC₁ : ordCompl[ℓ₁] (addOrderOf x) ≤ C₁) (hC₂ : ordCompl[ℓ₂] (addOrderOf x) ≤ C₂) :
    addOrderOf x ≤ C₁ * C₂ :=
  le_mul_of_ordCompl_le hx.addOrderOf_pos.ne' h₁ h₂ hne hC₁ hC₂

end
