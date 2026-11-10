module

public import Mathlib

/-!
# Derivations which are logarithmic at a place, in residue characteristic zero

Let `O` be a Dedekind domain with fraction field `L`, let `v` be a height one prime of `O`, and
let `k ⊆ O` be a field of characteristic zero which maps onto the residue field `O ⧸ v`. Let `δ`
be a `k`-derivation of `L` such that `v(δ y)` is bounded above for `y ∈ O`, and suppose that some
nonzero `s ∈ v` satisfies `δ s = -s`. Then `δ` maps `O` into the valuation ring of `v`.

This is the tameness statement used for the affine line: over the point at infinity of the
affine line over a field of characteristic zero, the logarithmic derivation `t d/dt` extends to
every finite separable extension preserving the valuation rings above infinity.

The proof is elementary. Writing `a = δπ / π` for a uniformizer `π`, every `v`-integral element
`z` is `p(π) + π ^ N y` with `p` a polynomial over `k` and `y` integral, so that
`v(δ z) ≤ max (exp (-1) * v a) (exp (-N) * max (v a) M)` where `M` bounds `v ∘ δ` on `O`. Writing
`s = π ^ e u` with `v u = 1`, the relation `δ s = -s` reads `δ u + e a u = -u`; since `e` is a
unit (characteristic zero), `v a > 1` would give `v u = v a > 1`. Hence `v a ≤ 1`, and then
`v(δ y) ≤ 1`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuation_derivation_le_one`: the statement above.
-/

@[expose] public section

open WithZero Polynomial

namespace WithZero

/-- In `ℤᵐ⁰`, an element below `1` is at most `exp (-1)`. -/
theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le
  · rw [← exp_log h0] at hx ⊢
    rw [exp_le_exp]
    rw [exp_lt_one_iff] at hx
    omega

/-- In `ℤᵐ⁰`, `exp (-N) * M` drops below any nonzero element for `N` large. -/
theorem exists_exp_neg_mul_lt {x : ℤᵐ⁰} (hx : x ≠ 0) (M : ℤᵐ⁰) :
    ∃ N : ℕ, exp (-(N : ℤ)) * M < x := by
  rcases eq_or_ne M 0 with rfl | hM
  · exact ⟨0, by simpa using zero_lt_iff.mpr hx⟩
  · obtain ⟨m, rfl⟩ : ∃ m, M = exp m := ⟨log M, (exp_log hM).symm⟩
    obtain ⟨ξ, rfl⟩ : ∃ ξ, x = exp ξ := ⟨log x, (exp_log hx).symm⟩
    refine ⟨(m - ξ + 1).toNat, ?_⟩
    rw [← exp_add, exp_lt_exp]
    omega

/-- In `ℤᵐ⁰`, multiplying a nonzero element by `exp (-N)` with `N ≥ 1` makes it smaller. -/
theorem exp_neg_mul_lt {x : ℤᵐ⁰} (hx : x ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    exp (-(N : ℤ)) * x < x := by
  obtain ⟨ξ, rfl⟩ : ∃ ξ, x = exp ξ := ⟨log x, (exp_log hx).symm⟩
  rw [← exp_add, exp_lt_exp]
  omega

end WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {O L k : Type*} [CommRing O] [IsDedekindDomain O] [Field L] [Algebra O L]
  [IsFractionRing O L] [Field k] [Algebra k O] [Algebra k L] [IsScalarTower k O L]
  (v : HeightOneSpectrum O)

/-- The image of a nonzero element of the coefficient field `k ⊆ O` has valuation `1`. -/
theorem valuation_algebraMap_of_ne_zero {c : k} (hc : c ≠ 0) :
    v.valuation L (algebraMap k L c) = 1 := by
  rw [IsScalarTower.algebraMap_apply k O L, valuation_of_algebraMap,
    intValuation_eq_one_iff_mem_primeCompl]
  intro h
  exact v.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ h ((IsUnit.mk0 c hc).map (algebraMap k O)))

/-- A nonzero natural number has valuation `1` when `k` has characteristic zero. -/
theorem valuation_natCast_of_ne_zero [CharZero k] {n : ℕ} (hn : n ≠ 0) :
    v.valuation L (n : L) = 1 := by
  rw [← map_natCast (algebraMap k L)]
  exact v.valuation_algebraMap_of_ne_zero (Nat.cast_ne_zero.mpr hn)

/-- A natural number has valuation at most `1`. -/
theorem valuation_natCast_le_one (n : ℕ) : v.valuation L (n : L) ≤ 1 := by
  rw [← map_natCast (algebraMap O L)]
  exact v.valuation_le_one _

/-- An element of the complement of `v` has valuation `1`. -/
private theorem valuation_algebraMap_primeCompl (d : v.asIdeal.primeCompl) :
    v.valuation L (algebraMap O L d) = 1 := by
  rw [valuation_of_algebraMap, intValuation_eq_one_iff_mem_primeCompl]
  exact d.2

/-- An element of valuation `exp (-1)` is nonzero. -/
private theorem ne_zero_of_valuation_eq_exp_neg_one {π : L} (hπ : v.valuation L π = exp (-1)) :
    π ≠ 0 := by
  rintro rfl
  rw [map_zero] at hπ
  exact exp_ne_zero hπ.symm

/-- A power of an element of valuation `exp (-1)` has the expected valuation. -/
private theorem valuation_pow_of_eq_exp_neg_one {π : L} (hπ : v.valuation L π = exp (-1))
    (N : ℕ) : v.valuation L (π ^ N) = exp (-(N : ℤ)) := by
  rw [map_pow, hπ, ← exp_nsmul]
  congr 1
  simp

/-- The Leibniz rule for `π ^ N * y` when `δ π = π * a`. -/
private theorem derivation_pow_mul {R : Type*} [CommRing R] [Algebra R L] (δ : Derivation R L L)
    {π a : L} (hδπ : δ π = π * a) (N : ℕ) (y : L) :
    δ (π ^ N * y) = π ^ N * (δ y + (N : L) * a * y) := by
  have hpow : δ (π ^ N) = (N : L) * π ^ N * a := by
    rcases N with _ | N
    · simp
    · rw [Derivation.leibniz_pow, hδπ, nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hpow]
  ring

/-- A polynomial over `k` evaluated at a `v`-integral element is `v`-integral. -/
theorem valuation_aeval_le_one {π : L} (hπ : v.valuation L π ≤ 1) (p : k[X]) :
    v.valuation L (aeval π p) ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hp hq)
  | monomial n c =>
    rw [aeval_monomial, map_mul, map_pow]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [v.valuation_algebraMap_of_ne_zero hc, one_mul]
      exact pow_le_one' hπ n

/-- If `k` maps onto the residue field of `v`, every `v`-integral element of `L` is congruent to an
element of `k` modulo the maximal ideal of the valuation ring. -/
theorem exists_valuation_sub_lt_one (H : ∀ y : O, ∃ c : k, y - algebraMap k O c ∈ v.asIdeal)
    {z : L} (hz : v.valuation L z ≤ 1) : ∃ c : k, v.valuation L (z - algebraMap k L c) < 1 := by
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer z hz
  obtain ⟨cn, hcn⟩ := H n
  obtain ⟨cd, hcd⟩ := H d
  have hcd0 : cd ≠ 0 := by
    rintro rfl
    exact d.2 (by simpa using hcd)
  have hd1 := v.valuation_algebraMap_primeCompl (L := L) d
  refine ⟨cn / cd, ?_⟩
  have hc : algebraMap k O (cn / cd) * algebraMap k O cd = algebraMap k O cn := by
    rw [← map_mul, div_mul_cancel₀ _ hcd0]
  have key : (z - algebraMap k L (cn / cd)) * algebraMap O L d =
      algebraMap O L ((n - algebraMap k O cn) - algebraMap k O (cn / cd) *
        (d - algebraMap k O cd)) := by
    rw [sub_mul, hnd, IsScalarTower.algebraMap_apply k O L, ← map_mul, ← map_sub]
    congr 1
    linear_combination -hc
  have hlt : v.valuation L ((z - algebraMap k L (cn / cd)) * algebraMap O L d) < 1 := by
    rw [key, valuation_of_algebraMap, intValuation_lt_one_iff_mem]
    exact Ideal.sub_mem _ hcn (Ideal.mul_mem_left _ _ hcd)
  rwa [map_mul, hd1, mul_one] at hlt

/-- **Expansion in a uniformizer.** If `k` maps onto the residue field of `v` and `π` is a
uniformizer, every `v`-integral `z` is `p(π) + π ^ N * y` with `p` a polynomial over `k` and `y`
again `v`-integral. -/
theorem exists_eq_aeval_add_pow_mul (H : ∀ y : O, ∃ c : k, y - algebraMap k O c ∈ v.asIdeal)
    {π : L} (hπ : v.valuation L π = exp (-1)) (N : ℕ) {z : L} (hz : v.valuation L z ≤ 1) :
    ∃ (p : k[X]) (y : L), v.valuation L y ≤ 1 ∧ z = aeval π p + π ^ N * y := by
  induction N with
  | zero => exact ⟨0, z, hz, by simp⟩
  | succ N ih =>
    obtain ⟨p, y, hy, rfl⟩ := ih
    obtain ⟨c, hc⟩ := v.exists_valuation_sub_lt_one H hy
    have hπ0 := v.ne_zero_of_valuation_eq_exp_neg_one hπ
    refine ⟨p + monomial N c, (y - algebraMap k L c) / π, ?_, ?_⟩
    · rw [map_div₀, hπ, div_le_one₀ exp_pos]
      exact WithZero.le_exp_neg_one_of_lt_one hc
    · rw [map_add, aeval_monomial]
      field_simp
      ring

/-- **A uniform bound.** If `v ∘ δ` is bounded by `M` on `O`, it is bounded by `M` on all
`v`-integral elements of `L`. -/
theorem valuation_derivation_le_of_valuation_le_one {R : Type*} [CommRing R] [Algebra R L]
    (δ : Derivation R L L) {M : ℤᵐ⁰} (hM : ∀ y : O, v.valuation L (δ (algebraMap O L y)) ≤ M)
    {z : L} (hz : v.valuation L z ≤ 1) : v.valuation L (δ z) ≤ M := by
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer z hz
  have hd1 := v.valuation_algebraMap_primeCompl (L := L) d
  have h := congrArg δ hnd
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
  have h' : δ z * algebraMap O L d = δ (algebraMap O L n) - z * δ (algebraMap O L d) := by
    rw [← h]
    ring
  have h'' := congrArg (v.valuation L) h'
  rw [map_mul, hd1, mul_one] at h''
  rw [h'']
  refine (Valuation.map_sub _ _ _).trans (max_le (hM n) ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_left' hz).trans (hM d)

variable [CharZero k]

omit [CharZero k] in
/-- **The basic estimate.** Let `π` be a uniformizer with `δ π = π * a`. Then for every
`v`-integral `z` and every `N`,
`v(δ z) ≤ max (exp (-1) * v a) (exp (-N) * max (v a) M)`. -/
theorem valuation_derivation_le_max (H : ∀ y : O, ∃ c : k, y - algebraMap k O c ∈ v.asIdeal)
    (δ : Derivation k L L) {M : ℤᵐ⁰} (hM : ∀ y : O, v.valuation L (δ (algebraMap O L y)) ≤ M)
    {π a : L} (hπ : v.valuation L π = exp (-1)) (hδπ : δ π = π * a) (N : ℕ) {z : L}
    (hz : v.valuation L z ≤ 1) :
    v.valuation L (δ z) ≤ max (exp (-1) * v.valuation L a)
      (exp (-(N : ℤ)) * max (v.valuation L a) M) := by
  obtain ⟨p, y, hy, rfl⟩ := v.exists_eq_aeval_add_pow_mul H hπ N hz
  have hπN := v.valuation_pow_of_eq_exp_neg_one hπ N
  have e1 : δ (aeval π p) = aeval π (derivative p) * π * a := by
    rw [Derivation.map_aeval, smul_eq_mul, hδπ]
    ring
  have e2 : δ (π ^ N * y) = π ^ N * δ y + (N : L) * π ^ N * a * y := by
    rw [derivation_pow_mul δ hδπ]
    ring
  have hπ1 : v.valuation L π ≤ 1 := by rw [hπ]; exact exp_le_one_iff.mpr (by norm_num)
  rw [map_add, e1, e2]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ((Valuation.map_add _ _ _).trans
    (max_le ?_ ?_)))
  · refine le_max_of_le_left ?_
    rw [map_mul, map_mul, hπ]
    gcongr
    exact mul_le_of_le_one_left' (v.valuation_aeval_le_one hπ1 _)
  · refine le_max_of_le_right ?_
    rw [map_mul, hπN]
    gcongr
    exact (v.valuation_derivation_le_of_valuation_le_one δ hM hy).trans (le_max_right _ _)
  · refine le_max_of_le_right ?_
    rw [map_mul, map_mul, map_mul, hπN]
    calc v.valuation L (N : L) * exp (-(N : ℤ)) * v.valuation L a * v.valuation L y
        ≤ 1 * exp (-(N : ℤ)) * v.valuation L a * 1 := by
          gcongr
          · exact v.valuation_natCast_le_one N
      _ ≤ exp (-(N : ℤ)) * max (v.valuation L a) M := by
          rw [one_mul, mul_one]
          gcongr
          exact le_max_left _ _

/-- **Logarithmic derivations preserve the valuation ring, in residue characteristic zero.**
Let `O` be a Dedekind domain with fraction field `L`, `v` a height one prime of `O`, and `k ⊆ O`
a field of characteristic zero mapping onto the residue field `O ⧸ v`. Let `δ` be a
`k`-derivation of `L` with `v ∘ δ` bounded above on `O`, and let `s ∈ v` be nonzero with
`δ s = -s`. Then `v(δ y) ≤ 1` for every `y ∈ O`. -/
theorem valuation_derivation_le_one (H : ∀ y : O, ∃ c : k, y - algebraMap k O c ∈ v.asIdeal)
    (δ : Derivation k L L) {M : ℤᵐ⁰} (hM : ∀ y : O, v.valuation L (δ (algebraMap O L y)) ≤ M)
    {s : O} (hs : s ∈ v.asIdeal) (hs0 : s ≠ 0)
    (hδs : δ (algebraMap O L s) = -algebraMap O L s) (y : O) :
    v.valuation L (δ (algebraMap O L y)) ≤ 1 := by
  obtain ⟨π₀, hπ₀⟩ := v.valuation_exists_uniformizer' L
  set π : L := algebraMap O L π₀ with hπdef
  have hπ : v.valuation L π = exp (-1) := hπ₀
  have hπ0 := v.ne_zero_of_valuation_eq_exp_neg_one hπ
  set a : L := δ π / π with ha
  have hδπ : δ π = π * a := by rw [ha]; field_simp
  -- the valuation of `a` is at most `1`
  have hval_a : v.valuation L a ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have ha0 : v.valuation L a ≠ 0 := (zero_lt_one.trans hlt).ne'
    -- write `s = π ^ e * u` with `v u = 1`
    set sL : L := algebraMap O L s
    have hsL0 : sL ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O L)]
      exact hs0
    have hvs0 : v.valuation L sL ≠ 0 := (Valuation.ne_zero_iff _).mpr hsL0
    have hvs1 : v.valuation L sL < 1 := by
      rw [valuation_of_algebraMap, intValuation_lt_one_iff_mem]
      exact hs
    set e : ℕ := (-log (v.valuation L sL)).toNat
    have hlog : log (v.valuation L sL) < 0 := by
      rw [← exp_log hvs0, exp_lt_one_iff] at hvs1
      exact hvs1
    have he : v.valuation L sL = exp (-(e : ℤ)) := by
      rw [← exp_log hvs0]
      congr 1
      omega
    have he1 : e ≠ 0 := by omega
    set u : L := sL / π ^ e
    have hπe0 : π ^ e ≠ 0 := pow_ne_zero _ hπ0
    have hsu : sL = π ^ e * u := by simp only [u]; field_simp
    have hπe := v.valuation_pow_of_eq_exp_neg_one hπ e
    have hu1 : v.valuation L u = 1 := by
      have := congrArg (v.valuation L) hsu
      rw [map_mul, hπe, he] at this
      exact (mul_eq_left₀ exp_ne_zero).mp this.symm
    -- the relation `δ u + e a u = -u`
    have hrel : δ u + (e : L) * a * u = -u := by
      have h1 : δ sL = π ^ e * (δ u + (e : L) * a * u) := by
        rw [hsu, derivation_pow_mul δ hδπ]
      have h2 : δ sL = π ^ e * (-u) := by
        rw [hδs, hsu]
        ring
      exact mul_left_cancel₀ hπe0 (h1.symm.trans h2)
    -- estimate `δ u`
    obtain ⟨N₀, hN₀⟩ := exists_exp_neg_mul_lt ha0 M
    set N : ℕ := max N₀ 1
    have hN1 : 1 ≤ N := le_max_right _ _
    have hNM : exp (-(N : ℤ)) * M < v.valuation L a := by
      have hle : exp (-(N : ℤ)) ≤ exp (-(N₀ : ℤ)) := by
        rw [exp_le_exp]
        have := le_max_left N₀ 1
        omega
      exact lt_of_le_of_lt (by gcongr) hN₀
    have hδu : v.valuation L (δ u) < v.valuation L a := by
      refine lt_of_le_of_lt
        (v.valuation_derivation_le_max H δ hM hπ hδπ N hu1.le) (max_lt ?_ ?_)
      · simpa using exp_neg_mul_lt ha0 (N := 1) le_rfl
      · rw [mul_max]
        exact max_lt (exp_neg_mul_lt ha0 hN1) hNM
    have heau : v.valuation L ((e : L) * a * u) = v.valuation L a := by
      simp only [map_mul, v.valuation_natCast_of_ne_zero (k := k) he1, hu1, one_mul, mul_one]
    have hsum : v.valuation L (δ u + (e : L) * a * u) = v.valuation L a := by
      rw [Valuation.map_add_eq_of_lt_right _ (heau ▸ hδu), heau]
    rw [hrel, Valuation.map_neg, hu1] at hsum
    exact (lt_irrefl _ (hsum ▸ hlt))
  -- conclusion
  obtain ⟨N, hN⟩ := exists_exp_neg_mul_lt (one_ne_zero (α := ℤᵐ⁰)) (max 1 M)
  refine (v.valuation_derivation_le_max H δ hM hπ hδπ N (v.valuation_le_one y)).trans
    (max_le ?_ ?_)
  · calc exp (-1) * v.valuation L a ≤ exp (-1) * 1 := by gcongr
      _ ≤ 1 := by rw [mul_one]; exact exp_le_one_iff.mpr (by norm_num)
  · calc exp (-(N : ℤ)) * max (v.valuation L a) M ≤ exp (-(N : ℤ)) * max 1 M := by
          gcongr
      _ ≤ 1 := hN.le

end IsDedekindDomain.HeightOneSpectrum
