module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic.LinearCombination
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `ℤ/n` is self-injective

For every `n ≠ 0` the ring `ℤ/n` is an injective module over itself. Equivalently, by Baer's
criterion, every `ℤ/n`-linear map from an ideal of `ℤ/n` to `ℤ/n` is multiplication by an element.
Every ideal of `ℤ/n` is principal (its additive group is a subgroup of a cyclic group), and a
map out of the principal ideal `(a)` is determined by the image `y` of `a`, which is killed by
every `r` with `r a = 0`; such a `y` is a multiple of `a`, by Bézout for `gcd(a, n)`.

This is the first input of the quasi-Frobenius treatment of the coefficients `A = ℤ/ℓⁿ` in
Step 7 of the proof of [Stacks, Tag 03UG]: over a self-injective ring the dual `M ↦ Hom_A(M, A)`
is exact, which is what turns the universal coefficient isomorphism
`RΓ_c(U, L) ⊗ᴸ_A M ≅ RΓ_c(U, L ⊗_A M)` into a statement about an additive functor applied to a
perfect complex.

## Main results

* `ZMod.exists_eq_mul_of_forall_mul_eq_zero` — in `ℤ/n`, an element `y` killed by the
  annihilator of `a` is a multiple of `a`.
* `ZMod.exists_eq_span_singleton` — every ideal of `ℤ/n` is principal.
* `ZMod.baer_self` — Baer's criterion for `ℤ/n` over itself.
* `ZMod.injective_self` — `ℤ/n` is an injective `ℤ/n`-module.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 7.
-/

@[expose] public section

namespace ZMod

/-- In `ℤ/n`, an element `y` killed by every `r` with `r a = 0` is a multiple of `a`. -/
theorem exists_eq_mul_of_forall_mul_eq_zero (n : ℕ) [NeZero n] (a y : ZMod n)
    (h : ∀ r : ZMod n, r * a = 0 → r * y = 0) : ∃ z, y = a * z := by
  have ha : (((a.val : ℤ)) : ZMod n) = a := by simp
  have hy : (((y.val : ℤ)) : ZMod n) = y := by simp
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hbez := Int.gcd_eq_gcd_ab (a.val : ℤ) n
  obtain ⟨e, he⟩ := Int.gcd_dvd_right (a.val : ℤ) n
  obtain ⟨c, hc⟩ := Int.gcd_dvd_left (a.val : ℤ) n
  generalize ((Int.gcd (a.val : ℤ) n : ℕ) : ℤ) = d at hbez he hc
  generalize (a.val : ℤ) = a' at ha hbez hc
  generalize (y.val : ℤ) = y' at hy
  have he0 : e ≠ 0 := by rintro rfl; rw [mul_zero] at he; exact hn0 he
  have hea : ((e : ℤ) : ZMod n) * a = 0 := by
    rw [← ha, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c, by rw [hc, he]; ring⟩
  have hey := h _ hea
  rw [← hy, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd] at hey
  obtain ⟨b, hb⟩ := hey
  have hw : y' = d * b := mul_left_cancel₀ he0 (by rw [hb, he]; ring)
  refine ⟨((Int.gcdA a' n * b : ℤ) : ZMod n), ?_⟩
  rw [← hy, ← ha, hw, hbez]
  push_cast
  linear_combination (↑(Int.gcdB a' n) * ↑b : ZMod n) * ZMod.natCast_self n

/-- Every ideal of `ℤ/n` is principal: its additive group is a subgroup of the cyclic group
`ℤ/n`, hence cyclic, and a generator generates it as an ideal. -/
theorem exists_eq_span_singleton (n : ℕ) (I : Ideal (ZMod n)) :
    ∃ a : ZMod n, I = Submodule.span (ZMod n) {a} := by
  obtain ⟨⟨a, haI⟩, ha⟩ := IsAddCyclic.exists_generator (α := I.toAddSubgroup)
  refine ⟨a, le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr haI)⟩
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (ha ⟨x, hx⟩)
  have hk' : k • a = x := congrArg Subtype.val hk
  rw [← hk']
  exact Submodule.smul_of_tower_mem _ k (Submodule.mem_span_singleton_self a)

/-- **Baer's criterion for `ℤ/n` over itself.** Every `ℤ/n`-linear map from an ideal of `ℤ/n`
to `ℤ/n` is the restriction of multiplication by an element. -/
@[sga "4 XVIII 3.2.6"]
theorem baer_self (n : ℕ) [NeZero n] : Module.Baer (ZMod n) (ZMod n) := by
  intro I g
  obtain ⟨a, rfl⟩ := exists_eq_span_singleton n I
  set a₀ : Submodule.span (ZMod n) {a} := ⟨a, Submodule.mem_span_singleton_self a⟩
  obtain ⟨z, hz⟩ := exists_eq_mul_of_forall_mul_eq_zero n a (g a₀) fun r hr => by
    have h0 : r • a₀ = 0 := Subtype.ext (by simpa using hr)
    rw [← smul_eq_mul, ← g.map_smul, h0, map_zero]
  refine ⟨LinearMap.mulRight (ZMod n) z, fun x hx => ?_⟩
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have : (⟨r • a, hx⟩ : Submodule.span (ZMod n) {a}) = r • a₀ := rfl
  rw [this, g.map_smul, hz, LinearMap.mulRight_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- **`ℤ/n` is self-injective**: it is an injective module over itself for every `n ≠ 0`. -/
@[sga "4 XVIII 3.2.6"]
instance injective_self (n : ℕ) [NeZero n] : Module.Injective (ZMod n) (ZMod n) :=
  (baer_self n).injective

end ZMod
