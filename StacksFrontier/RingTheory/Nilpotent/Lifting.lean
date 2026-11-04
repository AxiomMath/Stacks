module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting `n`th roots along a locally nilpotent ideal
-/

@[expose] public section

end

/-!
Let `R` be a commutative ring, let `I ⊆ R` be a locally nilpotent ideal and let `n ≥ 1` be
invertible in `R/I`. Then the `n`th power map `1 + I → 1 + I`, `1 + x ↦ (1 + x)^n`, is a
bijection, and a unit `u ∈ Rˣ` is an `n`th power in `R` if and only if its image in `R/I` is an
`n`th power.

## Main definitions

* `Stacks.NilpotentIdeal.PowerMap.OneAddIdeal`: the set `1 + I`, as `{y : R // y - 1 ∈ I}`.
* `Stacks.NilpotentIdeal.PowerMap.powMap`: the `n`th power map on `1 + I`.

## Main results

* `Stacks.NilpotentIdeal.PowerMap.isUnit_quotient_mk_iff`: units are detected modulo a locally
  nilpotent ideal.
* `Stacks.NilpotentIdeal.PowerMap.powMap_bijective`: the `n`th power map on `1 + I` is a
  bijection.
* `Stacks.NilpotentIdeal.PowerMap.isUnit_pow_iff`: a unit of `R` is an `n`th power if and only
  if its image in `R/I` is.

## References

* [Stacks Project, Tag 0CAP](https://stacks.math.columbia.edu/tag/0CAP)
* [Stacks Project, Tag 0AMG](https://stacks.math.columbia.edu/tag/0AMG)
-/

@[expose] public section

namespace Stacks.NilpotentIdeal.PowerMap

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The set `1 + I = {1 + x : x ∈ I}`, rendered as `{y : R // y - 1 ∈ I}`. -/
abbrev OneAddIdeal : Type _ := {y : R // y - 1 ∈ I}

/-- For any ideal, `1 + I` is closed under taking `n`th powers: if `y - 1 ∈ I` then
`y ^ n - 1 ∈ I`. -/
theorem pow_sub_one_mem {y : R} (hy : y - 1 ∈ I) (n : ℕ) : y ^ n - 1 ∈ I := by
  simpa using I.mem_of_dvd (sub_dvd_pow_sub_pow y 1 n) hy

/-- The `n`th power map on `1 + I`, `1 + x ↦ (1 + x)^n`, as a self-map of the
subtype `{y : R // y - 1 ∈ I}`. -/
def powMap (n : ℕ) : OneAddIdeal I → OneAddIdeal I :=
  fun y => ⟨y.val ^ n, pow_sub_one_mem I y.property n⟩

/-- If `I` is locally nilpotent and `y - 1 ∈ I`, then `y` is a unit. -/
private theorem isUnit_of_sub_one_mem (hI : ∀ x ∈ I, IsNilpotent x) {y : R} (hy : y - 1 ∈ I) :
    IsUnit y := by
  simpa using (hI _ hy).isUnit_one_add

/-- If `I` is locally nilpotent and `mk I x` is a unit in `R/I`, then `x` is a unit in `R`. -/
private theorem isUnit_of_mk_isUnit_aux (hI : ∀ x ∈ I, IsNilpotent x) {x : R}
    (h : IsUnit ((Ideal.Quotient.mk I) x)) : IsUnit x := by
  obtain ⟨y0, hy0⟩ := h.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y0
  refine isUnit_of_mul_isUnit_left (y := y) (isUnit_of_sub_one_mem I hI ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hy0, sub_self]

/-- If `I` is locally nilpotent and `n` is invertible in `R/I`, then `(n : R)` is a unit in
`R`. -/
theorem natCast_isUnit (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ}
    (hnu : IsUnit ((n : R ⧸ I))) : IsUnit ((n : R)) :=
  isUnit_of_mk_isUnit_aux I hI (by simpa using hnu)

/-- If `I` is locally nilpotent, `n` is invertible mod `I` and `a ∈ I`, then
`(1+a)^n - 1 = a · w` for a unit `w`. -/
theorem one_add_pow_sub_one_factor (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ}
    (hnu : IsUnit ((n : R ⧸ I))) {a : R} (ha : a ∈ I) :
    ∃ w : R, IsUnit w ∧ (1 + a) ^ n - 1 = a * w := by
  refine ⟨∑ i ∈ Finset.range n, (1 + a) ^ i, ?_, ?_⟩
  · have hh : ∀ i ∈ Finset.range n, Ideal.Quotient.mk I ((1 + a) ^ i) = 1 := fun i _ => by
      rw [map_pow, map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr ha, add_zero, one_pow]
    have hmem : ∑ i ∈ Finset.range n, (1 + a) ^ i - n ∈ I := by
      refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
      rw [map_sub, map_natCast, map_sum, Finset.sum_congr rfl hh]
      simp
    simpa using
      (hI _ hmem).isUnit_add_left_of_commute (natCast_isUnit I hI hnu) (Commute.all _ _)
  · rw [← geom_sum_mul (1 + a) n]; ring

/-- If `I` is locally nilpotent, `n` is invertible mod `I`, `z ∈ I` and `(1+z)^n = 1`, then
`z = 0`. -/
theorem eq_zero_of_one_add_pow_eq_one (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ}
    (hnu : IsUnit ((n : R ⧸ I))) {z : R} (hz : z ∈ I) (h : (1 + z) ^ n = 1) :
    z = 0 := by
  obtain ⟨w, hwu, hwfac⟩ := one_add_pow_sub_one_factor I hI hnu hz
  rw [h, sub_self] at hwfac
  exact hwu.mul_right_eq_zero.mp ((mul_comm w z).trans hwfac.symm)

/-- If `I` is locally nilpotent and `mk I x` is a unit in `R/I`, then `x` is a unit in `R`. -/
@[ega "0 19.10.3" "more general"]
theorem isUnit_of_mk_isUnit (hI : ∀ x ∈ I, IsNilpotent x) {x : R}
    (h : IsUnit ((Ideal.Quotient.mk I) x)) : IsUnit x :=
  isUnit_of_mk_isUnit_aux I hI h

/-- Units are detected modulo a locally nilpotent ideal. -/
@[stacks 0AMG, ega "0 19.10.3" "more general", ega "0 7.1.12" "special case"]
theorem isUnit_quotient_mk_iff (hI : ∀ x ∈ I, IsNilpotent x) {x : R} :
    IsUnit x ↔ IsUnit ((Ideal.Quotient.mk I) x) :=
  ⟨fun hx ↦ hx.map (Ideal.Quotient.mk I), isUnit_of_mk_isUnit I hI⟩

/-! ### Injectivity and surjectivity of `powMap` -/

/-- If `I` is locally nilpotent and `n` is invertible in `R/I`, then `powMap I n` is
injective. -/
theorem powMap_injective (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ}
    (hnu : IsUnit ((n : R ⧸ I))) : Function.Injective (powMap I n) := by
  rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ heq
  obtain ⟨u, rfl⟩ : IsUnit y₂ := isUnit_of_sub_one_mem I hI hy₂
  have heq : y₁ ^ n = (u : R) ^ n := congrArg Subtype.val heq
  have hz : y₁ * ↑u⁻¹ - 1 ∈ I := by
    rw [show y₁ * ↑u⁻¹ - 1 = ((y₁ - 1) - (↑u - 1)) * ↑u⁻¹ by linear_combination u.mul_inv]
    exact I.mul_mem_right _ (I.sub_mem hy₁ hy₂)
  have h0 := eq_zero_of_one_add_pow_eq_one I hI hnu hz
    (by rw [add_sub_cancel, mul_pow, heq, ← mul_pow, u.mul_inv, one_pow])
  exact Subtype.ext (by linear_combination ↑u * h0 - y₁ * u.mul_inv)

/-- If `δ ∈ K`, then `∑_{i<n} (x + δ)^i x^(n-1-i) ≡ n x^(n-1)` modulo `K`. -/
theorem geom_sum₂_add_sub_natCast_mul_mem {K : Ideal R} {x δ : R} (hδ : δ ∈ K) (n : ℕ) :
    ∑ i ∈ Finset.range n, (x + δ) ^ i * x ^ (n - 1 - i) - n * x ^ (n - 1) ∈ K := by
  have hJ : (n : R) * x ^ (n - 1) = ∑ _i ∈ Finset.range n, x ^ (n - 1) := by simp
  rw [hJ, ← Finset.sum_sub_distrib]
  refine K.sum_mem fun i hi => ?_
  have hi : i + (n - 1 - i) = n - 1 := by grind
  rw [show (x + δ) ^ i * x ^ (n - 1 - i) - x ^ (n - 1)
      = ((x + δ) ^ i - x ^ i) * x ^ (n - 1 - i) by rw [sub_mul, ← pow_add, hi]]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (x + δ) x i
  rw [add_sub_cancel_left] at hc
  exact K.mul_mem_right _ (hc ▸ K.mul_mem_right _ hδ)

/-- First-order Taylor expansion of `x ↦ x ^ n`: if `δ ∈ K`, then
`(x + δ)^n - x^n - n x^(n-1) δ ∈ K ^ 2`. -/
theorem add_pow_sub_pow_sub_mem_sq {K : Ideal R} {x δ : R} (hδ : δ ∈ K) (n : ℕ) :
    (x + δ) ^ n - x ^ n - n * x ^ (n - 1) * δ ∈ K ^ 2 := by
  have hfac := (Commute.all (x + δ) x).geom_sum₂_mul n
  rw [add_sub_cancel_left] at hfac
  rw [← hfac, ← sub_mul, sq]
  exact Ideal.mul_mem_mul (geom_sum₂_add_sub_natCast_mul_mem hδ n) hδ

/-- One Newton step for `n`th roots: an `n`th root of `1 + b` modulo `(b^(j+1))` in `1 + I`
improves to one modulo `(b^(j+2))`. -/
theorem exists_one_add_pow_sub_mem_span_succ (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ}
    (hnu : IsUnit ((n : R ⧸ I))) {a b : R} {j : ℕ} (hbI : b ∈ I) (haI : a ∈ I)
    (hres : (1 + a) ^ n - (1 + b) ∈ Ideal.span {b ^ (j + 1)}) :
    ∃ a' ∈ I, (1 + a') ^ n - (1 + b) ∈ Ideal.span {b ^ (j + 2)} := by
  obtain ⟨c, hc⟩ :=
    ((natCast_isUnit I hI hnu).mul ((hI a haI).isUnit_one_add.pow (n - 1))).exists_right_inv
  have hδ : -(((1 + a) ^ n - (1 + b)) * c) ∈ Ideal.span {b ^ (j + 1)} :=
    neg_mem (Ideal.mul_mem_right _ _ hres)
  have hsub : Ideal.span {b ^ (j + 1)} ≤ I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (I.pow_mem_of_mem hbI _ j.succ_pos))
  refine ⟨a + -(((1 + a) ^ n - (1 + b)) * c), I.add_mem haI (hsub hδ), ?_⟩
  have h := add_pow_sub_pow_sub_mem_sq hδ n (x := 1 + a)
  rw [Ideal.span_singleton_pow, ← pow_mul] at h
  rw [show (1 + (a + -(((1 + a) ^ n - (1 + b)) * c))) ^ n - (1 + b)
      = (1 + a + -(((1 + a) ^ n - (1 + b)) * c)) ^ n - (1 + a) ^ n
        - n * (1 + a) ^ (n - 1) * -(((1 + a) ^ n - (1 + b)) * c) by
    linear_combination (-((1 + a) ^ n - (1 + b))) * hc]
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow b (by omega)) h

/-- If `I` is locally nilpotent and `n` is invertible in `R/I`, then `powMap I n` is
surjective: every `1 + b ∈ 1 + I` has an `n`th root in `1 + I`. -/
theorem powMap_surjective (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ} (_hn : 1 ≤ n)
    (hnu : IsUnit ((n : R ⧸ I))) : Function.Surjective (powMap I n) := by
  rintro ⟨y, hy⟩
  have hbI : y - 1 ∈ I := hy
  have key : ∀ j : ℕ, ∃ a ∈ I, (1 + a) ^ n - (1 + (y - 1)) ∈ Ideal.span {(y - 1) ^ (j + 1)} := by
    intro j
    induction j with
    | zero => exact ⟨0, I.zero_mem, Ideal.mem_span_singleton.mpr ⟨-1, by ring⟩⟩
    | succ j ih =>
      obtain ⟨_, haI, hres⟩ := ih
      exact exists_one_add_pow_sub_mem_span_succ I hI hnu hbI haI hres
  obtain ⟨N, hN⟩ := hI _ hbI
  obtain ⟨a, haI, hres⟩ := key N
  rw [pow_succ, hN, zero_mul, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hres
  exact ⟨⟨1 + a, by simpa using haI⟩, Subtype.ext (show (1 + a) ^ n = y by linear_combination hres)⟩

/-- If `I` is locally nilpotent and `n ≥ 1` is invertible in `R/I`, then the `n`th power map
`1 + x ↦ (1 + x)^n` on `1 + I` is a bijection. -/
@[stacks 0CAP "(1)"]
theorem powMap_bijective
    (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ} (hn : 1 ≤ n)
    (hnu : IsUnit ((n : R ⧸ I))) :
    Function.Bijective (powMap I n) :=
  ⟨powMap_injective I hI hnu, powMap_surjective I hI hn hnu⟩

/-- If `I` is locally nilpotent and `n ≥ 1` is invertible in `R/I`, then a unit `u ∈ Rˣ` is
an `n`th power in `R` if and only if its image in `R/I` is an `n`th power (as a unit) in `R/I`. -/
@[stacks 0CAP "(2)"]
theorem isUnit_pow_iff
    (hI : ∀ x ∈ I, IsNilpotent x) {n : ℕ} (hn : 1 ≤ n)
    (hnu : IsUnit ((n : R ⧸ I))) (u : Rˣ) :
    (∃ v : Rˣ, u = v ^ n) ↔
      (∃ w : (R ⧸ I)ˣ, (Ideal.Quotient.mk I (u : R) : R ⧸ I) = (w : R ⧸ I) ^ n) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Units.map (Ideal.Quotient.mk I : R →+* R ⧸ I).toMonoidHom v, by simp⟩
  · rintro ⟨w, hw⟩
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (w : R ⧸ I)
    obtain ⟨v₀, rfl⟩ := isUnit_of_mk_isUnit I hI (hr ▸ w.isUnit)
    have hvv : (v₀ : R) * ((v₀⁻¹ : Rˣ) : R) = 1 := v₀.mul_inv
    set x : R := (u : R) * ((v₀⁻¹ : Rˣ) : R) ^ n with hx
    have hmkx : Ideal.Quotient.mk I x = 1 := by
      rw [hx, map_mul, map_pow, hw, ← hr, ← mul_pow, ← map_mul, hvv, map_one, one_pow]
    have hxmem : x - 1 ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, map_one, hmkx, sub_self])
    obtain ⟨⟨z, hz⟩, hzpow⟩ := powMap_surjective I hI hn hnu ⟨x, hxmem⟩
    have hzn : z ^ n = x := congrArg Subtype.val hzpow
    obtain ⟨t, rfl⟩ : IsUnit z := isUnit_of_sub_one_mem I hI (by simpa using hz)
    refine ⟨v₀ * t, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mul, mul_pow, hzn, hx, mul_comm (u : R), ← mul_assoc,
      ← mul_pow, hvv, one_pow, one_mul]

end Stacks.NilpotentIdeal.PowerMap

end
