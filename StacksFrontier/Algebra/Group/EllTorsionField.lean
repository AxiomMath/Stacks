module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import StacksFrontier.Algebra.Group.EllTorsionRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `ℓ`-torsion of the multiplicative and additive groups of an algebraically closed field

Let `k` be an algebraically closed field and let `ℓ` be a prime different from the
characteristic of `k`, that is, with `(ℓ : k) ≠ 0`. This file computes the `ℓ`-divisibility and
the dimension of the `ℓ`-torsion of the two groups that occur as the left-hand term of the Picard
sequences of [Stacks, Tag 0C1M] and [Stacks, Tag 0C1N] in the induction of [Stacks, Tag 0C20]:

* `k^*`, written `Additive kˣ` so that it is an additive group: it is `ℓ`-divisible because
  every element of an algebraically closed field is an `ℓ`-th power, and its `ℓ`-torsion is the
  group `μ_ℓ(k)` of `ℓ`-th roots of unity, which has exactly `ℓ` elements and is therefore
  one-dimensional over `ZMod ℓ`.
* `(k, +)`: it is `ℓ`-divisible because `ℓ` is invertible in `k`, and its `ℓ`-torsion is trivial
  for the same reason, so zero-dimensional.

The source records these two facts as "`(k,+)` and `k^*` are `ℓ`-divisible with
`(k,+)[ℓ] = 0` and `k^*[ℓ] ≅ F_ℓ`".

## Main results

* `Stacks.EllTorsion.card_rootsOfUnity_of_isAlgClosed` — an algebraically closed field in which
  `n` is invertible has exactly `n` `n`-th roots of unity.
* `Stacks.EllTorsion.exists_zsmul_eq_additive_units` — `k^*` is `ℓ`-divisible.
* `Stacks.EllTorsion.card_torsionBy_additive_units` — `k^*[ℓ]` has `ℓ` elements.
* `Stacks.EllTorsion.rank_torsionBy_additive_units` — `dim_{F_ℓ} k^*[ℓ] = 1`.
* `Stacks.EllTorsion.exists_zsmul_eq_self` — `(k, +)` is `ℓ`-divisible.
* `Stacks.EllTorsion.rank_torsionBy_self` — `dim_{F_ℓ} (k,+)[ℓ] = 0`.

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
-/

@[expose] public section

open Polynomial

universe u

namespace Stacks.EllTorsion

/-! ### Roots of unity in an algebraically closed field -/

/-- **An algebraically closed field in which `n` is invertible has exactly `n` `n`-th roots of
unity.** The polynomial `X^n - 1` splits because `k` is algebraically closed, so it has `n`
roots counted with multiplicity, and it is separable because `(n : k) ≠ 0`, so those roots are
distinct. -/
@[sga "3 VIII 2.1" "Equality direction"]
theorem card_rootsOfUnity_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    [NeZero n] (hn : (n : k) ≠ 0) : Nat.card (rootsOfUnity n k) = n := by
  classical
  have hnth : nthRoots n (1 : k) = (X ^ n - C 1 : k[X]).roots := rfl
  have hroots : Multiset.card (nthRoots n (1 : k)) = n := by
    rw [hnth, (Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits _),
      Polynomial.natDegree_X_pow_sub_C]
  have hnodup : (nthRoots n (1 : k)).Nodup := by
    rw [hnth, C_1]
    exact nodup_roots (X_pow_sub_one_separable_iff.mpr hn)
  have e : { x // x ∈ nthRoots n (1 : k) } ≃ { x // x ∈ (nthRoots n (1 : k)).toFinset } :=
    Equiv.subtypeEquivRight fun _ => Multiset.mem_toFinset.symm
  rw [Nat.card_congr (rootsOfUnityEquivNthRoots k n), Nat.card_congr e, Nat.card_eq_fintype_card,
    Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hroots]

/-! ### The multiplicative group -/

/-- **The `ℓ`-torsion of `k^*` is the group of `ℓ`-th roots of unity.** Being killed by `ℓ` in
the additive group `Additive kˣ` is being an `ℓ`-th root of unity in `kˣ`. -/
def torsionByAdditiveUnitsEquivRootsOfUnity (k : Type u) [Field k] (ℓ : ℕ) :
    AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ) ≃ rootsOfUnity ℓ k :=
  Equiv.subtypeEquiv Additive.toMul fun x => by
    change (ℓ : ℤ) • x = 0 ↔ _
    rw [mem_rootsOfUnity, ← toMul_eq_one, toMul_zsmul]
    simp

/-- **`k^*` is `ℓ`-divisible for `k` algebraically closed.** Every element of `k` is an `ℓ`-th
power, and an `ℓ`-th root of a unit is a unit. -/
theorem exists_zsmul_eq_additive_units (k : Type u) [Field k] [IsAlgClosed k] {ℓ : ℕ}
    (hℓ : 0 < ℓ) (a : Additive kˣ) : ∃ b : Additive kˣ, (ℓ : ℤ) • b = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul a : kˣ) : k) hℓ
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hℓ.ne'] at hz
    exact (Units.ne_zero _) hz.symm
  refine ⟨Additive.ofMul (Units.mk0 z hz0), Additive.toMul.injective ?_⟩
  rw [toMul_zsmul, toMul_ofMul]
  refine Units.ext ?_
  push_cast
  simpa using hz

/-- **The `ℓ`-torsion of `k^*` has exactly `ℓ` elements**, for `k` algebraically closed and `ℓ`
a prime different from the characteristic: it is the group of `ℓ`-th roots of unity. -/
theorem card_torsionBy_additive_units (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ)
    [NeZero ℓ] (hℓ : (ℓ : k) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) = ℓ := by
  rw [Nat.card_congr (torsionByAdditiveUnitsEquivRootsOfUnity k ℓ),
    card_rootsOfUnity_of_isAlgClosed k ℓ hℓ]

/-- **The `ℓ`-torsion of `k^*` is one-dimensional over `F_ℓ`**, for `k` algebraically closed and
`ℓ` a prime different from the characteristic: it is the group of `ℓ`-th roots of unity, which
has `ℓ` elements, and a vector space over the field `ZMod ℓ` with `ℓ` elements has dimension
one. -/
theorem rank_torsionBy_additive_units (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) = 1 := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  have hp := (Fact.out : ℓ.Prime)
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have hcard : Nat.card (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) = ℓ :=
    card_torsionBy_additive_units k ℓ hℓ
  have hfin : Finite (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) :=
    Nat.finite_of_card_ne_zero (hcard.trans_ne hp.ne_zero)
  let : Fintype (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod ℓ)
    (V := AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ))
  rw [← Nat.card_eq_fintype_card, hcard, ZMod.card] at hpow
  have hfr : Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) = 1 :=
    Nat.pow_right_injective hp.two_le (hpow.symm.trans (pow_one ℓ).symm)
  have : Module.Finite (ZMod ℓ) (AddSubgroup.torsionBy (Additive kˣ) (ℓ : ℤ)) :=
    Module.Finite.of_finite
  rw [← Module.finrank_eq_rank, hfr, Nat.cast_one]

/-! ### The additive group -/

/-- **`(k, +)` is `ℓ`-divisible when `ℓ` is invertible in `k`**: divide by `ℓ`. -/
theorem exists_zsmul_eq_self (k : Type u) [Field k] {ℓ : ℕ} (hℓ : (ℓ : k) ≠ 0) (a : k) :
    ∃ b : k, (ℓ : ℤ) • b = a := by
  refine ⟨(ℓ : k)⁻¹ * a, ?_⟩
  rw [zsmul_eq_mul]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hℓ, one_mul]

/-- **The `ℓ`-torsion of `(k, +)` is trivial when `ℓ` is invertible in `k`.** -/
theorem subsingleton_torsionBy_self (k : Type u) [Field k] {ℓ : ℕ} (hℓ : (ℓ : k) ≠ 0) :
    Subsingleton (AddSubgroup.torsionBy k (ℓ : ℤ)) := by
  have hzero : ∀ z : AddSubgroup.torsionBy k (ℓ : ℤ), (z : k) = 0 := by
    intro z
    have h : (ℓ : ℤ) • (z : k) = 0 := z.2
    rw [zsmul_eq_mul] at h
    push_cast at h
    exact (mul_eq_zero.mp h).resolve_left hℓ
  exact ⟨fun x y => Subtype.ext ((hzero x).trans (hzero y).symm)⟩

/-- **The `ℓ`-torsion of `(k, +)` is zero-dimensional over `F_ℓ`** when `ℓ` is a prime
different from the characteristic of `k`. -/
theorem rank_torsionBy_self (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy k (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy k (ℓ : ℤ)) = 0 := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy k (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  have : Subsingleton (AddSubgroup.torsionBy k (ℓ : ℤ)) := subsingleton_torsionBy_self k hℓ
  exact rank_subsingleton' (ZMod ℓ) (AddSubgroup.torsionBy k (ℓ : ℤ))

end Stacks.EllTorsion
