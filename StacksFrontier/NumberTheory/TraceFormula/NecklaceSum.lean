module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.NumberTheory.Divisors

/-!
# Sums over `ℤ/(q^n - 1)` by orbits of multiplication by `q`

Fix `q ≥ 2` and write `R_d = q^d - 1`. Multiplication by `q` permutes `ℤ/R_d`, with `q^d = 1`. Let
`S_d` be the set of orbits of exact size `d` (the closed points of degree `d` of `𝐆_m` over a
field with `q` elements, `ℤ/R_d` being the character group of `𝔽_{q^d}^×`). For `d ∣ n` the map
`ι : ℤ/R_d → ℤ/R_n`, `k ↦ k R_n / R_d`, identifies the points of exact period `d` of `ℤ/R_n`
with those of `ℤ/R_d`; summing over the periods gives, for every `H` on `ℤ/R_n` invariant under
multiplication by `q`,

`Σ_{t ∈ ℤ/R_n} H(t) = Σ_{d ∣ n} d Σ_{x ∈ S_d} H(ι(x))`.

## Main definitions

* `Stacks.TraceFormula.Necklace.Orbits q d`: the orbits `S_d`.

## Main results

* `Stacks.TraceFormula.Necklace.sum_eq_sum_divisors_orbits`: the identity above.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula.Necklace

open Function

variable (q : ℕ)

/-- `R_d = q^d - 1`. -/
public abbrev R (d : ℕ) : ℕ := q ^ d - 1

variable {q} [hq : Fact (2 ≤ q)]
include hq

/-- `R_d = q^d - 1` is positive for `d ≥ 1`. -/
public theorem R_pos {d : ℕ} (hd : 0 < d) : 0 < R q d := by
  have : 2 ≤ q ^ d := le_trans hq.out (Nat.le_self_pow hd.ne' q)
  simp only [R]
  omega

omit hq in
/-- `R_d ∣ R_n` whenever `d ∣ n`. -/
public theorem R_dvd_R {d n : ℕ} (h : d ∣ n) : R q d ∣ R q n := by
  obtain ⟨m, rfl⟩ := h
  simpa [R, pow_mul] using Nat.sub_dvd_pow_sub_pow (x := q ^ d) (y := 1) (n := m)

/-- The natural number `R_d` is `q^d - 1` in any ring. -/
private theorem natCast_R {S : Type*} [Ring S] (d : ℕ) :
    ((R q d : ℕ) : S) = (q : S) ^ d - 1 := by
  rw [R, Nat.cast_sub (Nat.one_le_pow _ _ (by have := hq.out; omega)), Nat.cast_pow, Nat.cast_one]

/-- `q^d = 1` in `ℤ/R_d`. -/
public theorem pow_eq_one (d : ℕ) : ((q : ZMod (R q d)) ^ d) = 1 :=
  sub_eq_zero.1 <| by rw [← natCast_R, ZMod.natCast_self]

omit hq

variable (q)

/-- Multiplication by `q` on `ℤ/R_d`. -/
public abbrev mulq (d : ℕ) (x : ZMod (R q d)) : ZMod (R q d) := (q : ZMod (R q d)) * x

/-- The `i`-th iterate of multiplication by `q` is multiplication by `q^i`. -/
public theorem iterate_mulq (d i : ℕ) (x : ZMod (R q d)) :
    (mulq q d)^[i] x = (q : ZMod _) ^ i * x := by
  induction i with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply', ih, mulq, ← mul_assoc, pow_succ']

include hq in
/-- Every point of `ℤ/R_d` is periodic of period `d` under multiplication by `q`. -/
public theorem isPeriodicPt_mulq (d : ℕ) (x : ZMod (R q d)) : IsPeriodicPt (mulq q d) d x := by
  change (mulq q d)^[d] x = x
  rw [iterate_mulq, pow_eq_one, one_mul]

/-- The points of exact period `d` of `ℤ/R_d`, for `d ≥ 1`. -/
public abbrev Free (d : ℕ) : Type :=
  {k : ZMod (R q d) // 0 < d ∧ minimalPeriod (mulq q d) k = d}

/-- There are finitely many points of exact period `d`. -/
public instance [Fact (2 ≤ q)] (d : ℕ) : Finite (Free q d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Finite.of_injective (β := Empty) (fun k => absurd k.2.1 (lt_irrefl 0))
      fun k => absurd k.2.1 (lt_irrefl 0)
  · have : NeZero (R q d) := ⟨(R_pos hd).ne'⟩
    exact Subtype.finite

/-- Two points are in the same orbit of multiplication by `q`. -/
public def orbitSetoid (d : ℕ) : Setoid (Free q d) where
  r k k' := ∃ i j : ℕ, (q : ZMod (R q d)) ^ i * k.1 = (q : ZMod (R q d)) ^ j * k'.1
  iseqv :=
    { refl := fun k => ⟨0, 0, rfl⟩
      symm := by
        rintro k k' ⟨i, j, h⟩
        exact ⟨j, i, h.symm⟩
      trans := by
        rintro k k' k'' ⟨i, j, h⟩ ⟨a, b, h'⟩
        refine ⟨i + a, j + b, ?_⟩
        calc (q : ZMod (R q d)) ^ (i + a) * k.1 = (q : ZMod _) ^ a * ((q : ZMod _) ^ i * k.1) := by
              rw [pow_add, mul_comm ((q : ZMod _) ^ i), mul_assoc]
          _ = (q : ZMod _) ^ j * ((q : ZMod _) ^ a * k'.1) := by rw [h, mul_left_comm]
          _ = _ := by rw [h', pow_add, mul_assoc] }

/-- **The orbits `S_d`** of exact size `d` of multiplication by `q` on `ℤ/(q^d - 1)`. -/
public abbrev Orbits (d : ℕ) : Type := Quotient (orbitSetoid q d)

/-- There are finitely many orbits `S_d`. -/
public instance [Fact (2 ≤ q)] (d : ℕ) : Finite (Orbits q d) := Quotient.finite _

/-- The orbits `S_d` form a finite type. -/
public instance [Fact (2 ≤ q)] (d : ℕ) : Fintype (Orbits q d) := Fintype.ofFinite _

/-- The points of exact period `d` form a finite type. -/
public instance [Fact (2 ≤ q)] (d : ℕ) : Fintype (Free q d) := Fintype.ofFinite _

/-! ### Orbits of exact size `d` -/

section OrbitCount

variable {q} [hq : Fact (2 ≤ q)]

/-- `q^i k`, a point of exact period `d` together with `k`. -/
public def qpow {d : ℕ} (k : Free q d) (i : ℕ) : Free q d :=
  ⟨(q : ZMod (R q d)) ^ i * k.1, k.2.1, by
    rw [← iterate_mulq, minimalPeriod_apply_iterate
      (mk_mem_periodicPts k.2.1 (isPeriodicPt_mulq q d k.1)), k.2.2]⟩

/-- The underlying element of `qpow k i` is `q^i k`. -/
public theorem qpow_val {d : ℕ} (k : Free q d) (i : ℕ) :
    (qpow k i).1 = (q : ZMod (R q d)) ^ i * k.1 :=
  rfl

/-- Within an orbit, `q^j k' = q^i k` gives `k' = q^a k`. -/
public theorem exists_qpow_eq {d : ℕ} {k k' : Free q d} (h : (orbitSetoid q d) k' k) :
    ∃ a : ℕ, a < d ∧ qpow k a = k' := by
  obtain ⟨j, i, hji⟩ := h
  have hd := k.2.1
  refine ⟨((d - 1) * j + i) % d, Nat.mod_lt _ hd, Subtype.ext ?_⟩
  rw [qpow_val]
  have hpow : ∀ m, (q : ZMod (R q d)) ^ (m % d) = (q : ZMod (R q d)) ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m d, pow_add, pow_mul, pow_eq_one, one_pow, one_mul]
  rw [hpow, pow_add, mul_assoc, ← hji, ← mul_assoc, ← pow_add]
  have : (d - 1) * j + j = d * j := by
    have := Nat.sub_one_mul d j
    have h1 : j ≤ d * j := Nat.le_mul_of_pos_left j hd
    omega
  rw [this, pow_mul, pow_eq_one, one_pow, one_mul]

open scoped Classical in
/-- **Every orbit has exactly `d` elements.** -/
public theorem card_fiber {d : ℕ} (x : Orbits q d) :
    (Finset.univ.filter fun k : Free q d => (Quotient.mk _ k : Orbits q d) = x).card = d := by
  classical
  induction x using Quotient.inductionOn with
  | h k =>
    have h := Finset.card_bij (s := Finset.range d)
      (t := Finset.univ.filter fun k' : Free q d =>
        (Quotient.mk _ k' : Orbits q d) = Quotient.mk _ k)
      (fun i _ => qpow k i) (fun i _ => ?_) (fun i hi j hj hij => ?_) (fun k' hk' => ?_)
    · rw [Finset.card_range] at h
      exact h.symm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Quotient.sound ⟨0, i, by rw [pow_zero, one_mul]; rfl⟩
    · have h := congrArg Subtype.val hij
      rw [qpow_val, qpow_val, ← iterate_mulq, ← iterate_mulq] at h
      have hk := k.2.2
      exact iterate_injOn_Iio_minimalPeriod (f := mulq q d) (x := k.1)
        (by rw [hk]; exact Finset.mem_range.1 hi) (by rw [hk]; exact Finset.mem_range.1 hj) h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk'
      obtain ⟨a, ha, rfl⟩ := exists_qpow_eq (Quotient.exact hk')
      exact ⟨a, Finset.mem_range.2 ha, rfl⟩

/-- **Summing an orbit-invariant function over the points of exact period `d`**: each orbit
contributes `d` times. -/
public theorem sum_free_eq_nsmul {A : Type*} [AddCommMonoid A] {d : ℕ} (G : ZMod (R q d) → A)
    (hG : ∀ t, G ((q : ZMod (R q d)) * t) = G t) :
    ∑ k : Free q d, G k.1 = d • ∑ x : Orbits q d, G (Quotient.out x).1 := by
  classical
  have hGpow : ∀ i t, G ((q : ZMod (R q d)) ^ i * t) = G t := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro t; rw [pow_succ', mul_assoc, hG, ih]
  have hinv : ∀ k : Free q d, G k.1 = G (Quotient.out (Quotient.mk (orbitSetoid q d) k)).1 := by
    intro k
    obtain ⟨a, -, ha⟩ := exists_qpow_eq (Quotient.exact (Quotient.out_eq (Quotient.mk _ k)))
    rw [← ha, qpow_val, hGpow]
  calc ∑ k : Free q d, G k.1
        = ∑ k : Free q d, G (Quotient.out (Quotient.mk (orbitSetoid q d) k)).1 :=
        Finset.sum_congr rfl fun k _ => hinv k
    _ = ∑ x : Orbits q d, ∑ k ∈ Finset.univ.filter (fun k : Free q d =>
          (Quotient.mk _ k : Orbits q d) = x), G (Quotient.out x).1 :=
        (Finset.sum_fiberwise' Finset.univ (fun k : Free q d => (Quotient.mk _ k : Orbits q d))
          (fun x => G (Quotient.out x).1)).symm
    _ = ∑ x : Orbits q d, d • G (Quotient.out x).1 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_const, card_fiber]
    _ = _ := Finset.smul_sum.symm

end OrbitCount

/-! ### The points of period `d` of `ℤ/R_n` -/

section Embedding

variable {q} [hq : Fact (2 ≤ q)] {d n : ℕ}

variable (q) in
omit hq in
/-- `R_d` kills `R_n / R_d` in `ℤ/R_n`, so `ι` is well defined. -/
public theorem R_nsmul_eq_zero (hdn : d ∣ n) :
    R q d • (((R q n / R q d : ℕ)) : ZMod (R q n)) = 0 := by
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (R_dvd_R hdn), ZMod.natCast_self]

/-- `ι : ℤ/R_d → ℤ/R_n`, `k ↦ k R_n / R_d`. -/
public def iota (hdn : d ∣ n) : ZMod (R q d) →+ ZMod (R q n) :=
  ZMod.lift (R q d) ⟨zmultiplesHom (ZMod (R q n)) ((R q n / R q d : ℕ) : ZMod (R q n)), by
    rw [zmultiplesHom_apply, natCast_zsmul, R_nsmul_eq_zero q hdn]⟩

omit hq in
/-- `ι` sends the class of `m` to the class of `m R_n / R_d`. -/
public theorem iota_natCast (hdn : d ∣ n) (m : ℕ) :
    iota hdn (m : ZMod (R q d)) = ((m * (R q n / R q d) : ℕ) : ZMod (R q n)) := by
  have : (m : ZMod (R q d)) = ((m : ℤ) : ZMod (R q d)) := by rw [Int.cast_natCast]
  rw [this, iota, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, Nat.cast_mul]

omit hq in
/-- `ι` commutes with multiplication by `q`. -/
public theorem iota_mul (hdn : d ∣ n) (k : ZMod (R q d)) :
    iota hdn ((q : ZMod (R q d)) * k) = (q : ZMod (R q n)) * iota hdn k := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

omit hq in
/-- `ι` commutes with multiplication by `q^i`. -/
public theorem iota_pow_mul (hdn : d ∣ n) (i : ℕ) (k : ZMod (R q d)) :
    iota hdn ((q : ZMod (R q d)) ^ i * k) = (q : ZMod (R q n)) ^ i * iota hdn k := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', mul_assoc, iota_mul, ih, ← mul_assoc, ← pow_succ']

/-- `ι : ℤ/R_d → ℤ/R_n` is injective. -/
public theorem iota_injective (hd : 0 < d) (hn : 0 < n) (hdn : d ∣ n) :
    Function.Injective (iota (q := q) hdn) := by
  have := NeZero.of_pos (R_pos (q := q) hd)
  rw [injective_iff_map_eq_zero]
  intro k hk
  rw [← ZMod.natCast_zmod_val k, iota_natCast, ZMod.natCast_eq_zero_iff] at hk
  have hc : 0 < R q n / R q d :=
    Nat.div_pos (Nat.le_of_dvd (R_pos hn) (R_dvd_R hdn)) (R_pos hd)
  conv_lhs at hk => rw [← Nat.mul_div_cancel' (R_dvd_R (q := q) hdn)]
  have h := Nat.dvd_of_mul_dvd_mul_right hc hk
  rw [← ZMod.natCast_zmod_val k, ZMod.natCast_eq_zero_iff]
  exact h

/-- `ι` preserves exact periods. -/
public theorem minimalPeriod_iota (hd : 0 < d) (hn : 0 < n) (hdn : d ∣ n) (k : ZMod (R q d)) :
    minimalPeriod (mulq q n) (iota hdn k) = minimalPeriod (mulq q d) k := by
  rw [minimalPeriod_eq_minimalPeriod_iff]
  intro i
  change (mulq q n)^[i] (iota hdn k) = iota hdn k ↔ (mulq q d)^[i] k = k
  rw [iterate_mulq, iterate_mulq, ← iota_pow_mul]
  exact (iota_injective hd hn hdn).eq_iff

/-- The points of exact period `d` of `ℤ/R_n` come from `ℤ/R_d`. -/
public theorem exists_iota_eq (hd : 0 < d) (hn : 0 < n) (hdn : d ∣ n) (t : ZMod (R q n))
    (ht : minimalPeriod (mulq q n) t = d) : ∃ k : ZMod (R q d), iota hdn k = t := by
  have := NeZero.of_pos (R_pos (q := q) hn)
  have hper : (q : ZMod (R q n)) ^ d * t = t := by
    rw [← iterate_mulq, ← ht]
    exact iterate_minimalPeriod
  have hz : ((R q d * t.val : ℕ) : ZMod (R q n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id, natCast_R, sub_mul, hper,
      one_mul, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at hz
  set c := R q n / R q d
  have hRc : R q n = R q d * c := (Nat.mul_div_cancel' (R_dvd_R hdn)).symm
  have hz' : R q d * c ∣ R q d * t.val := by rw [← hRc]; exact hz
  obtain ⟨m, hm⟩ := Nat.dvd_of_mul_dvd_mul_left (R_pos hd) hz'
  refine ⟨(m : ZMod (R q d)), ?_⟩
  rw [iota_natCast, mul_comm m c, ← hm, ZMod.natCast_zmod_val]

end Embedding

/-! ### The sum -/

section Sum

variable {q} [hq : Fact (2 ≤ q)]

/-- **The sum over `ℤ/(q^n - 1)` by orbits of multiplication by `q`**: for `H` invariant under
multiplication by `q`, `Σ_{t ∈ ℤ/R_n} H(t) = Σ_{d ∣ n} d Σ_{x ∈ S_d} H(ι(x))`. -/
public theorem sum_eq_sum_divisors_orbits {A : Type*} [AddCommMonoid A] {n : ℕ} (hn : 0 < n)
    (H : ZMod (R q n) → A) (hH : ∀ t, H ((q : ZMod (R q n)) * t) = H t) :
    haveI : NeZero (R q n) := ⟨(R_pos hn).ne'⟩
    ∑ t : ZMod (R q n), H t = ∑ d ∈ n.divisors.attach, d.1 •
      ∑ x : Orbits q d.1, H (iota (Nat.dvd_of_mem_divisors d.2) (Quotient.out x).1) := by
  classical
  have := NeZero.of_pos (R_pos (q := q) hn)
  have hmaps : ∀ t ∈ (Finset.univ : Finset (ZMod (R q n))),
      minimalPeriod (mulq q n) t ∈ n.divisors := by
    intro t _
    exact Nat.mem_divisors.2 ⟨(isPeriodicPt_mulq q n t).minimalPeriod_dvd, hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_attach n.divisors]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hd : 0 < d.1 := Nat.pos_of_mem_divisors d.2
  have hdn := Nat.dvd_of_mem_divisors d.2
  rw [← sum_free_eq_nsmul (fun k => H (iota hdn k)) fun t => by rw [iota_mul, hH]]
  symm
  refine Finset.sum_bij (fun k _ => iota hdn k.1) (fun k _ => ?_) (fun k _ k' _ h => ?_)
    (fun t ht => ?_) (fun k _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [minimalPeriod_iota hd hn hdn, k.2.2]
  · exact Subtype.ext (iota_injective hd hn hdn h)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨k, rfl⟩ := exists_iota_eq hd hn hdn t ht
    exact ⟨⟨k, hd, by rw [← minimalPeriod_iota hd hn hdn, ht]⟩, Finset.mem_univ _, rfl⟩

end Sum

end Stacks.TraceFormula.Necklace

end
