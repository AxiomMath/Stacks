module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.RingTheory.WittVector.CechTransfer

/-!
# Čech vanishing on a punctured spectrum cut out by a regular sequence

Let `T` be a commutative ring and `Ω` a `T`-algebra. For `s : T` let `awaySubring Ω s` be the
subring of those `ω : Ω` with `s ^ n * ω` in the image of `T` for some `n`; when `s` is a unit
in `Ω` it is the image of `T[1/s]` in `Ω` (`awaySubring_eq_range_lift`).

Let `x 0, x 1, x 2` be a weakly regular sequence of nonzerodivisors in `T` and let `y : ι → T` be
a finite family of nonzerodivisors with every `x i ∈ √(y)`, so that the opens `D(y k)` cover the
punctured spectrum `U = Spec T ∖ V(x 0, x 1, x 2)` (and possibly more). All the rings
`T[1/∏_{k ∈ K} y k]` embed in `T[1/∏ k, y k]`. This file proves that the additive Čech complex
of this covering has cohomology `T` in degree `0` and none in degree `1`, which is the vanishing
of `H⁰_I(T)`, `H¹_I(T)` and `H²_I(T)` for `I = (x 0, x 1, x 2)`, by elementary means.

## Main results

* `mem_range_of_forall_mem_awaySubring_away`: an element of `T[1/∏ k, y k]` lying in the image
  of every `T[1/y k]` lies in the image of `T`.
* `exists_cech_coboundary_away`: if `b k l ∈ T[1/(y k * y l)]` satisfy `b k l + b l m = b k m`,
  then `b k l = c k - c l` with `c k ∈ T[1/y k]`.
* `coeff_mem_range_of_forall_coeff_mem_awaySubring_away` and
  `exists_wittVector_cech_coboundary_away`: the same statements for Witt vectors whose
  coefficients lie in these subrings, by `WittVector.coeff_mem_of_forall_coeff_mem` and
  `WittVector.exists_cech_coboundary`.

## Implementation notes

Everything is first proved in an ambient `T`-algebra `Ω` into which `T` embeds and in which the
`x i` are units (`mem_range_of_forall_mem_awaySubring`,
`exists_cech_coboundary_of_forall_mem_radical`), and then transported to `T[1/∏ k, y k]` along its
embedding into `FractionRing T`, the localization at all nonzerodivisors.

* For a covering of a basic open `D(s)` by the `D(s * g k)` (that is, `s ∈ √(g)`) the Čech
  complex is exact in degrees `0` and `1` by a partition of unity
  (`mem_awaySubring_of_forall_mem_awaySubring_mul`, `exists_cech_coboundary_of_mem_radical`).
* For the covering by the `D(x i)` (`mem_range_of_mem_awaySubring_regular`,
  `exists_cech_coboundary_regular`) one clears denominators: with `a, b, c` the `N`-th powers of
  `x 0, x 1, x 2`, a cocycle gives `c * u + a * v = b * w` in `T`, and since `b` is a
  nonzerodivisor modulo `a` and `c` one modulo `(a, b)` (`mem_span_pow_of_pow_mul_mem`,
  `mem_span_pow_sup_of_pow_mul_mem`) this splits as a coboundary.
* The covering by the `D(y k)` is compared with the covering by the `D(x i)` through the common
  refinement by the `D(x i * y k)`, using the two previous points.
-/

@[expose] public section

open RingTheory.Sequence

namespace Stacks.RingTheory.PuncturedVanishing

variable {T : Type*} [CommRing T]

section AwaySubring

variable (Ω : Type*) [CommRing Ω] [Algebra T Ω]

/-- The subring of `Ω` of the elements `ω` such that `s ^ n * ω` lies in the image of `T` for
some `n`. When `s` is a unit in `Ω` this is the image of `T[1/s]` (`awaySubring_eq_range_lift`). -/
def awaySubring (s : T) : Subring Ω where
  carrier := {ω | ∃ n : ℕ, ∃ t : T, algebraMap T Ω (s ^ n) * ω = algebraMap T Ω t}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro ω ω' ⟨m, t, ht⟩ ⟨n, t', ht'⟩
    refine ⟨m + n, s ^ n * t + s ^ m * t', ?_⟩
    rw [pow_add, map_mul, map_add, map_mul, map_mul, ← ht, ← ht']
    ring
  mul_mem' := by
    rintro ω ω' ⟨m, t, ht⟩ ⟨n, t', ht'⟩
    refine ⟨m + n, t * t', ?_⟩
    rw [pow_add, map_mul, map_mul, ← ht, ← ht']
    ring
  neg_mem' := by
    rintro ω ⟨m, t, ht⟩
    exact ⟨m, -t, by rw [map_neg, ← ht, mul_neg]⟩

variable {Ω}

/-- `ω ∈ awaySubring Ω s` if and only if `s ^ n * ω` is the image of an element of `T` for some
`n`. -/
theorem mem_awaySubring_iff {s : T} {ω : Ω} :
    ω ∈ awaySubring Ω s ↔ ∃ n : ℕ, ∃ t : T, algebraMap T Ω (s ^ n) * ω = algebraMap T Ω t :=
  Iff.rfl

/-- The image of `T` lies in every `awaySubring Ω s`. -/
theorem algebraMap_mem_awaySubring (s t : T) : algebraMap T Ω t ∈ awaySubring Ω s :=
  ⟨0, t, by simp⟩

/-- The exponent in the definition of `awaySubring` may be increased. -/
theorem exists_eq_of_mem_awaySubring {s : T} {ω : Ω} {n : ℕ}
    (h : ∃ t : T, algebraMap T Ω (s ^ n) * ω = algebraMap T Ω t) {m : ℕ} (hnm : n ≤ m) :
    ∃ t : T, algebraMap T Ω (s ^ m) * ω = algebraMap T Ω t := by
  obtain ⟨t, ht⟩ := h
  refine ⟨s ^ (m - n) * t, ?_⟩
  rw [← Nat.sub_add_cancel hnm, pow_add, map_mul, mul_assoc, ht, Nat.add_sub_cancel, map_mul]

/-- For finitely many elements of the `awaySubring`s one exponent works for all of them. -/
theorem exists_uniform_exponent {ι : Type*} [Finite ι] {s : ι → T} {ω : ι → Ω}
    (h : ∀ i, ω i ∈ awaySubring Ω (s i)) :
    ∃ n : ℕ, ∀ i, ∃ t : T, algebraMap T Ω (s i ^ n) * ω i = algebraMap T Ω t := by
  have : ∀ᶠ m in Filter.atTop, ∀ i, ∃ t : T, algebraMap T Ω (s i ^ m) * ω i = algebraMap T Ω t :=
    Filter.eventually_all.2 fun i => by
      obtain ⟨n, hn⟩ := h i
      exact Filter.eventually_atTop.2 ⟨n, fun m hm => exists_eq_of_mem_awaySubring hn hm⟩
  exact this.exists

/-- Inverting more elements gives a larger subring. -/
theorem awaySubring_le_awaySubring_mul (s g : T) : awaySubring Ω s ≤ awaySubring Ω (s * g) := by
  rintro ω ⟨n, t, ht⟩
  refine ⟨n, g ^ n * t, ?_⟩
  rw [mul_pow, map_mul, map_mul, ← ht]
  ring

/-- Inverting nothing gives the image of `T`. -/
theorem awaySubring_one : awaySubring Ω (1 : T) = (algebraMap T Ω).range := by
  ext ω
  refine ⟨fun ⟨n, t, ht⟩ => ⟨t, by simpa using ht.symm⟩, ?_⟩
  rintro ⟨t, rfl⟩
  exact algebraMap_mem_awaySubring 1 t

/-- An element `u : Ω` with `algebraMap T Ω s * u = 1` lies in `awaySubring Ω s`. -/
theorem mem_awaySubring_of_mul_eq_one {s : T} {u : Ω} (hu : algebraMap T Ω s * u = 1) :
    u ∈ awaySubring Ω s :=
  ⟨1, 1, by rw [pow_one, hu, map_one]⟩

/-- When `s` is a unit in `Ω`, `awaySubring Ω s` is the image of `T[1/s]`. -/
theorem awaySubring_eq_range_lift (s : T) (hs : IsUnit (algebraMap T Ω s)) :
    awaySubring Ω s = (IsLocalization.Away.lift (S := Localization.Away s) s hs).range := by
  ext ω
  constructor
  · rintro ⟨n, t, ht⟩
    exact ⟨IsLocalization.mk' (Localization.Away s) t (⟨s ^ n, n, rfl⟩ : Submonoid.powers s),
      (IsLocalization.lift_mk'_spec _ _ _ _).2 ht.symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s z
    refine ⟨n, a, ?_⟩
    rw [← IsLocalization.Away.lift_eq (S := Localization.Away s) s hs a, ← ha, map_mul,
      map_pow (IsLocalization.Away.lift s hs), IsLocalization.Away.lift_eq, map_pow, mul_comm]

/-- If `s` divides `s'`, then inverting `s'` gives a larger subring than inverting `s`. -/
theorem awaySubring_mono_of_dvd {s s' : T} (h : s ∣ s') : awaySubring Ω s ≤ awaySubring Ω s' := by
  obtain ⟨g, rfl⟩ := h
  exact awaySubring_le_awaySubring_mul s g

/-- Membership in `awaySubring` transfers along an injective `T`-algebra map. -/
theorem mem_awaySubring_iff_of_injective {Ω' : Type*} [CommRing Ω'] [Algebra T Ω'] (φ : Ω →+* Ω')
    (hφ : ∀ t, φ (algebraMap T Ω t) = algebraMap T Ω' t) (hinj : Function.Injective φ) {s : T}
    {ω : Ω} : φ ω ∈ awaySubring Ω' s ↔ ω ∈ awaySubring Ω s := by
  refine ⟨fun ⟨n, t, ht⟩ => ⟨n, t, hinj ?_⟩, fun ⟨n, t, ht⟩ => ⟨n, t, ?_⟩⟩
  · rw [map_mul, hφ, hφ, ht]
  · rw [← hφ, ← hφ, ← map_mul, ht]

end AwaySubring

section Regular

/-- A nonzerodivisor modulo `J` is a nonzerodivisor modulo `J` in all its powers. -/
private theorem mem_of_pow_mul_mem {J : Ideal T} {z : T} (hz : ∀ t, z * t ∈ J → t ∈ J) (m : ℕ)
    {t : T} (h : z ^ m * t ∈ J) : t ∈ J := by
  induction m generalizing t with
  | zero => simpa using h
  | succ m ih => exact hz t (ih (by rwa [pow_succ, mul_assoc] at h))

/-- If `a` is a nonzerodivisor modulo `J` and `z` a nonzerodivisor modulo `(a) + J`, then `z` is a
nonzerodivisor modulo `(aⁿ) + J` for every `n`. -/
private theorem mem_span_pow_sup_of_mul_mem {J : Ideal T} {a z : T}
    (ha : ∀ t, a * t ∈ J → t ∈ J)
    (hz : ∀ t, z * t ∈ Ideal.span {a} ⊔ J → t ∈ Ideal.span {a} ⊔ J) (n : ℕ) (t : T)
    (h : z * t ∈ Ideal.span {a ^ n} ⊔ J) : t ∈ Ideal.span {a ^ n} ⊔ J := by
  induction n generalizing t with
  | zero => simp [Ideal.span_singleton_one]
  | succ n ih =>
    have h' : z * t ∈ Ideal.span {a ^ n} ⊔ J :=
      sup_le_sup_right (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a n.le_succ)) _ h
    obtain ⟨u, j, hj, rfl⟩ := Ideal.mem_span_singleton_sup.1 (ih t h')
    obtain ⟨v, j', hj', hv⟩ := Ideal.mem_span_singleton_sup.1 h
    have h1 : a ^ n * (z * u - v * a) ∈ J := by
      have : a ^ n * (z * u - v * a) = j' - z * j := by
        rw [pow_succ] at hv
        linear_combination (-1 : T) * hv
      rw [this]
      exact J.sub_mem hj' (J.mul_mem_left z hj)
    have h3 : z * u ∈ Ideal.span {a} ⊔ J :=
      Ideal.mem_span_singleton_sup.2 ⟨v, _, mem_of_pow_mul_mem ha n h1, by ring⟩
    obtain ⟨w, j'', hj'', rfl⟩ := Ideal.mem_span_singleton_sup.1 (hz u h3)
    exact Ideal.mem_span_singleton_sup.2
      ⟨w, j'' * a ^ n + j, J.add_mem (J.mul_mem_right _ hj'') hj, by ring⟩

variable {a b c : T}

/-- The `i`-th term of a weakly regular sequence is a nonzerodivisor modulo the earlier ones. -/
private theorem regular_take (hx : IsWeaklyRegular T [a, b, c]) {i : ℕ} (hi : i < 3)
    {J : Ideal T} (hJ : Ideal.ofList ([a, b, c].take i) = J) :
    ∀ t, [a, b, c][i] * t ∈ J → t ∈ J := by
  have h := hx.regular_mod_prev i (by simpa using hi)
  rwa [isSMulRegular_quotient_iff_mem_of_smul_mem, smul_eq_mul, Ideal.mul_top, hJ] at h

private theorem regular_one (hx : IsWeaklyRegular T [a, b, c]) :
    ∀ t, b * t ∈ Ideal.span {a} → t ∈ Ideal.span {a} :=
  regular_take hx (i := 1) (by simp) (by simp)

private theorem regular_two (hx : IsWeaklyRegular T [a, b, c]) :
    ∀ t, c * t ∈ Ideal.span {a} ⊔ Ideal.span {b} → t ∈ Ideal.span {a} ⊔ Ideal.span {b} :=
  regular_take hx (i := 2) (by simp) (by
      simp only [Ideal.ofList, List.take_succ_cons, List.take_zero, List.mem_cons,
        List.not_mem_nil, or_false]
      exact Ideal.span_insert a {b})

private theorem regular_zero (hx : IsWeaklyRegular T [a, b, c]) :
    ∀ t, a * t ∈ (⊥ : Ideal T) → t ∈ (⊥ : Ideal T) := by
  intro t ht
  rw [Ideal.mem_bot] at ht ⊢
  exact ((isWeaklyRegular_cons_iff T _ _).1 hx).1 (by simpa using ht)

/-- Powers of `b` are nonzerodivisors modulo the powers of `a`. -/
theorem mem_span_pow_of_pow_mul_mem (hx : IsWeaklyRegular T [a, b, c]) (N M : ℕ) {t : T}
    (h : b ^ M * t ∈ Ideal.span {a ^ N}) : t ∈ Ideal.span {a ^ N} := by
  have key : ∀ t, b * t ∈ Ideal.span {a ^ N} → t ∈ Ideal.span {a ^ N} := fun t ht => by
    simpa using mem_span_pow_sup_of_mul_mem (regular_zero hx)
      (fun t ht => by simpa using regular_one hx t (by simpa using ht)) N t (by simpa using ht)
  exact mem_of_pow_mul_mem key M h

/-- Powers of `c` are nonzerodivisors modulo the ideal generated by the powers of `a` and
`b`. -/
theorem mem_span_pow_sup_of_pow_mul_mem (hx : IsWeaklyRegular T [a, b, c]) (N : ℕ) {t : T}
    (h : c ^ N * t ∈ Ideal.span {b ^ N} ⊔ Ideal.span {a ^ N}) :
    t ∈ Ideal.span {b ^ N} ⊔ Ideal.span {a ^ N} := by
  -- `a` is a nonzerodivisor modulo `b`.
  have hab : ∀ t, a * t ∈ Ideal.span {b} → t ∈ Ideal.span {b} := by
    intro t ht
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 ht
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1
      (regular_one hx v (Ideal.mem_span_singleton'.2 ⟨t, by rw [mul_comm b, hv, mul_comm]⟩))
    refine Ideal.mem_span_singleton'.2 ⟨w, ?_⟩
    have := regular_zero hx (t - w * b) (by
      rw [Ideal.mem_bot, mul_sub, ← hv, ← hw]
      ring)
    exact (sub_eq_zero.1 (Ideal.mem_bot.1 this)).symm
  -- `c` is a nonzerodivisor modulo `(aᴺ, b)`.
  have h3 : ∀ t, c * t ∈ Ideal.span {a ^ N} ⊔ Ideal.span {b} →
      t ∈ Ideal.span {a ^ N} ⊔ Ideal.span {b} :=
    mem_span_pow_sup_of_mul_mem hab (regular_two hx) N
  -- `c` is a nonzerodivisor modulo `(bᴺ, aᴺ)`.
  have h4 : ∀ t, c * t ∈ Ideal.span {b ^ N} ⊔ Ideal.span {a ^ N} →
      t ∈ Ideal.span {b ^ N} ⊔ Ideal.span {a ^ N} :=
    mem_span_pow_sup_of_mul_mem (fun t ht => mem_span_pow_of_pow_mul_mem hx N 1 (by simpa using ht))
      (fun t ht => by rw [sup_comm] at ht ⊢; exact h3 t ht) N
  exact mem_of_pow_mul_mem h4 N h

/-- If `cᴺ * u + aᴺ * v = bᴺ * w`, then `u = q * bᴺ + p * aᴺ` and `p * cᴺ + v = r * bᴺ` for some
`q p r`: the relation splits as a coboundary. -/
theorem exists_split_of_pow_mul_add_pow_mul_eq (hx : IsWeaklyRegular T [a, b, c]) {N : ℕ}
    {u v w : T} (key : c ^ N * u + a ^ N * v = b ^ N * w) :
    ∃ q p r : T, q * b ^ N + p * a ^ N = u ∧ p * c ^ N + v = r * b ^ N := by
  obtain ⟨q, j, hj, hqj⟩ := Ideal.mem_span_singleton_sup.1
    (mem_span_pow_sup_of_pow_mul_mem hx N (t := u)
      (Ideal.mem_span_singleton_sup.2 ⟨w, -(a ^ N * v), (Ideal.neg_mem_iff _).2
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)),
          by linear_combination (-1 : T) * key⟩))
  obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton'.1 hj
  rw [← hqj] at key
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (mem_span_pow_of_pow_mul_mem hx N N
    (Ideal.mem_span_singleton'.2 ⟨p * c ^ N + v, by linear_combination key⟩ :
      b ^ N * (w - q * c ^ N) ∈ Ideal.span {a ^ N}))
  refine ⟨q, p, r, hqj,
    sub_eq_zero.1 (Ideal.mem_bot.1 (mem_of_pow_mul_mem (regular_zero hx) N ?_))⟩
  rw [Ideal.mem_bot]
  linear_combination key - b ^ N * hr

end Regular

section Ambient

variable {Ω : Type*} [CommRing Ω] [Algebra T Ω]

/-- If `s ∈ √(g)` then some power of `s` is a combination of the `n`-th powers of the `g k`. -/
private theorem exists_pow_eq_sum_mul_pow {ι : Type*} [Fintype ι] {s : T} {g : ι → T}
    (hs : s ∈ (Ideal.span (Set.range g)).radical) (n : ℕ) :
    ∃ M : ℕ, ∃ a : ι → T, ∑ k, a k * g k ^ n = s ^ M := by
  have hle : Ideal.span (Set.range g) ≤ (Ideal.span (Set.range fun k => g k ^ n)).radical :=
    Ideal.span_le.2 (Set.range_subset_iff.2 fun k => ⟨n, Ideal.subset_span ⟨k, rfl⟩⟩)
  obtain ⟨M, hM⟩ := ((Ideal.radical_mono hle).trans (Ideal.radical_idem _).le) hs
  exact ⟨M, Ideal.mem_span_range_iff_exists_fun.1 hM⟩

/-- **Čech `H⁰` of a covering of a basic open.** If `s ∈ √(g)`, so that the `D(s * g k)` cover
`D(s)`, an element of `Ω` lying in every `awaySubring Ω (s * g k)` lies in `awaySubring Ω s`. -/
theorem mem_awaySubring_of_forall_mem_awaySubring_mul {ι : Type*} [Finite ι] {s : T}
    {g : ι → T} (hs : s ∈ (Ideal.span (Set.range g)).radical) {ω : Ω}
    (h : ∀ k, ω ∈ awaySubring Ω (s * g k)) : ω ∈ awaySubring Ω s := by
  cases nonempty_fintype ι
  obtain ⟨n, hn⟩ := exists_uniform_exponent h
  choose t ht using hn
  obtain ⟨M, a, ha⟩ := exists_pow_eq_sum_mul_pow hs n
  refine ⟨M + n, ∑ k, a k * t k, ?_⟩
  rw [pow_add, ← ha, Finset.sum_mul, map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul (algebraMap T Ω) (a k) (t k), ← ht k, mul_pow, map_mul, map_mul, map_mul]
  ring

/-- **Čech `H¹` of a covering of a basic open.** If `s` is a unit in `Ω` and `s ∈ √(g)`, then
every cocycle `b k l ∈ awaySubring Ω (s * g k * g l)` is a coboundary of elements
`c k ∈ awaySubring Ω (s * g k)`. -/
theorem exists_cech_coboundary_of_mem_radical {ι : Type*} [Finite ι] {s : T} {g : ι → T}
    (hsu : IsUnit (algebraMap T Ω s)) (hs : s ∈ (Ideal.span (Set.range g)).radical)
    (b : ι → ι → Ω) (hb : ∀ k l, b k l ∈ awaySubring Ω (s * g k * g l))
    (hcoc : ∀ k l m, b k l + b l m = b k m) :
    ∃ c : ι → Ω, (∀ k, c k ∈ awaySubring Ω (s * g k)) ∧ ∀ k l, b k l = c k - c l := by
  cases nonempty_fintype ι
  obtain ⟨n, hn⟩ := exists_uniform_exponent (s := fun kl : ι × ι => s * g kl.1 * g kl.2)
    (ω := fun kl => b kl.1 kl.2) fun kl => hb kl.1 kl.2
  choose t ht using hn
  obtain ⟨M, a, ha⟩ := exists_pow_eq_sum_mul_pow hs n
  obtain ⟨w, hw⟩ : ∃ w : Ω, algebraMap T Ω s * w = 1 := ⟨_, hsu.mul_val_inv⟩
  set α : ι → Ω := fun m => algebraMap T Ω (a m) * w ^ M with hα_def
  have hα : ∑ m, α m * algebraMap T Ω (g m ^ n) = 1 := by
    have h1 := congrArg (fun z => algebraMap T Ω z * w ^ M) ha
    simp only [map_sum, Finset.sum_mul, map_pow, ← mul_pow, hw, one_pow] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hα_def, map_mul, map_pow]
    ring
  refine ⟨fun k => ∑ m, α m * (algebraMap T Ω (g m ^ n) * b k m), fun k => ?_, fun k l => ?_⟩
  · refine Subring.sum_mem _ fun m _ => Subring.mul_mem _ (Subring.mul_mem _
      (algebraMap_mem_awaySubring _ _) (Subring.pow_mem _ (awaySubring_le_awaySubring_mul s (g k)
        (mem_awaySubring_of_mul_eq_one hw)) M)) ⟨n, t (k, m), ?_⟩
    rw [← ht (k, m)]
    simp only [mul_pow, map_mul]
    ring
  · rw [← Finset.sum_sub_distrib]
    calc b k l = ∑ m, α m * algebraMap T Ω (g m ^ n) * b k l := by
          rw [← Finset.sum_mul, hα, one_mul]
      _ = _ := Finset.sum_congr rfl fun m _ => by rw [← hcoc k l m]; ring

/-- A `1`-cocycle on three indices is the coboundary of `c` as soon as it agrees with it on the
pairs `(0, 1)` and `(1, 2)`. -/
theorem eq_sub_of_cocycle_fin_three {R : Type*} [CommRing R] {b : Fin 3 → Fin 3 → R}
    (hcoc : ∀ i j k, b i j + b j k = b i k) {c : Fin 3 → R}
    (h01 : b 0 1 = c 0 - c 1) (h12 : b 1 2 = c 1 - c 2) (i j : Fin 3) :
    b i j = c i - c j := by
  have hii : ∀ i, b i i = 0 := fun i => by linear_combination hcoc i i i
  have h0 : ∀ j, b 0 j = c 0 - c j := by
    intro j
    fin_cases j
    · simp [hii]
    · exact h01
    · simp only [Fin.reduceFinMk]
      linear_combination h01 + h12 - hcoc 0 1 2
  linear_combination h0 j - h0 i - hcoc i 0 j + hcoc i 0 i + hii i

section Base

variable {x : Fin 3 → T}

/-- **Čech `H⁰` of the covering by the `D(x i)`.** If `x 0, x 1, x 2` is a weakly regular
sequence, `T` embeds into `Ω` and `x 0` is a unit in `Ω`, then an element of `Ω` lying in
`awaySubring Ω (x 0)` and in `awaySubring Ω (x 1)` lies in the image of `T`. -/
theorem mem_range_of_mem_awaySubring_regular (hinj : Function.Injective (algebraMap T Ω))
    (hxu : IsUnit (algebraMap T Ω (x 0))) (hreg : IsWeaklyRegular T [x 0, x 1, x 2]) {ω : Ω}
    (h₀ : ω ∈ awaySubring Ω (x 0)) (h₁ : ω ∈ awaySubring Ω (x 1)) :
    ω ∈ (algebraMap T Ω).range := by
  obtain ⟨N, hN⟩ := exists_uniform_exponent (s := ![x 0, x 1]) (ω := fun _ => ω)
    (by intro i; fin_cases i <;> assumption)
  choose t ht using hN
  have ht0 : algebraMap T Ω (x 0 ^ N) * ω = algebraMap T Ω (t 0) := ht 0
  have ht1 : algebraMap T Ω (x 1 ^ N) * ω = algebraMap T Ω (t 1) := ht 1
  have h01 : x 1 ^ N * t 0 ∈ Ideal.span {x 0 ^ N} := by
    refine Ideal.mem_span_singleton'.2 ⟨t 1, hinj ?_⟩
    rw [map_mul, map_mul, ← ht0, ← ht1]
    ring
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (mem_span_pow_of_pow_mul_mem hreg N N h01)
  refine ⟨r, (hxu.pow N).mul_left_cancel ?_⟩
  rw [← map_pow, ← map_mul, mul_comm, hr, ht0]

/-- The covering of `D(g)` by `D(x 0 * g)` and `D(x 1 * g)`: an element of `Ω` lying in
`awaySubring Ω (x 0 * g)` and in `awaySubring Ω (x 1 * g)` lies in `awaySubring Ω g`. -/
theorem mem_awaySubring_of_mem_awaySubring_mul_regular
    (hinj : Function.Injective (algebraMap T Ω)) (hxu : IsUnit (algebraMap T Ω (x 0)))
    (hreg : IsWeaklyRegular T [x 0, x 1, x 2]) {g : T} {ω : Ω}
    (h₀ : ω ∈ awaySubring Ω (x 0 * g)) (h₁ : ω ∈ awaySubring Ω (x 1 * g)) :
    ω ∈ awaySubring Ω g := by
  obtain ⟨N, hN⟩ := exists_uniform_exponent (s := ![x 0 * g, x 1 * g]) (ω := fun _ => ω)
    (by intro i; fin_cases i <;> assumption)
  have hmem : ∀ i : Fin 2, algebraMap T Ω (g ^ N) * ω ∈ awaySubring Ω (![x 0, x 1] i) := by
    intro i
    obtain ⟨t, ht⟩ := hN i
    refine ⟨N, t, ?_⟩
    fin_cases i <;> simpa [mul_pow, mul_assoc] using ht
  obtain ⟨r, hr⟩ := mem_range_of_mem_awaySubring_regular hinj hxu hreg (hmem 0) (hmem 1)
  exact ⟨N, r, hr.symm⟩

/-- **Čech `H¹` of the covering by the `D(x i)`.** If `x 0, x 1, x 2` is a weakly regular
sequence, `T` embeds into `Ω` and the `x i` are units in `Ω`, then every Čech `1`-cocycle
`b i j ∈ awaySubring Ω (x i * x j)` is a coboundary of elements `c i ∈ awaySubring Ω (x i)`. -/
theorem exists_cech_coboundary_regular (hinj : Function.Injective (algebraMap T Ω))
    (hxu : ∀ i, IsUnit (algebraMap T Ω (x i))) (hreg : IsWeaklyRegular T [x 0, x 1, x 2])
    (b : Fin 3 → Fin 3 → Ω) (hb : ∀ i j, b i j ∈ awaySubring Ω (x i * x j))
    (hcoc : ∀ i j k, b i j + b j k = b i k) :
    ∃ c : Fin 3 → Ω, (∀ i, c i ∈ awaySubring Ω (x i)) ∧ ∀ i j, b i j = c i - c j := by
  obtain ⟨N, hN⟩ := exists_uniform_exponent (s := fun ij : Fin 3 × Fin 3 => x ij.1 * x ij.2)
    (ω := fun ij => b ij.1 ij.2) fun ij => hb ij.1 ij.2
  choose t ht using hN
  have hu := ht (0, 1)
  have hv := ht (1, 2)
  have hw := ht (0, 2)
  simp only [mul_pow, map_mul] at hu hv hw
  set u := t (0, 1)
  set v := t (1, 2)
  set w := t (0, 2)
  -- Clearing denominators in `b 0 1 + b 1 2 = b 0 2` gives `u * c + v * a = w * b` in `T`.
  have key : x 2 ^ N * u + x 0 ^ N * v = x 1 ^ N * w := hinj <| by
    simp only [map_add, map_mul, ← hu, ← hv, ← hw, map_pow, ← hcoc 0 1 2]
    ring
  obtain ⟨q, p, r, hqj, h3⟩ := exists_split_of_pow_mul_add_pow_mul_eq hreg key
  replace h3 := congrArg (algebraMap T Ω) h3
  choose y hy using fun i => (hxu i).exists_right_inv
  have hyN : ∀ i, algebraMap T Ω (x i) ^ N * y i ^ N = 1 := fun i => by rw [← mul_pow, hy, one_pow]
  refine ⟨![algebraMap T Ω q * y 0 ^ N, -(algebraMap T Ω p * y 1 ^ N),
    -(algebraMap T Ω r * y 2 ^ N)], ?_, ?_⟩
  · have hmem : ∀ i (z : T), algebraMap T Ω z * y i ^ N ∈ awaySubring Ω (x i) := fun i z =>
      Subring.mul_mem _ (algebraMap_mem_awaySubring _ _)
        (Subring.pow_mem _ (mem_awaySubring_of_mul_eq_one (hy i)) N)
    intro i
    fin_cases i
    · exact hmem 0 q
    · exact Subring.neg_mem _ (hmem 1 p)
    · exact Subring.neg_mem _ (hmem 2 r)
  · set X : Fin 3 → Ω := fun i => algebraMap T Ω (x i) ^ N with hX
    set Y : Fin 3 → Ω := fun i => y i ^ N with hY
    have hXY : ∀ i, X i * Y i = 1 := hyN
    have hu' : X 0 * X 1 * b 0 1 = algebraMap T Ω q * X 1 + algebraMap T Ω p * X 0 := by
      simpa [← hqj, hX, map_pow] using hu
    have hv' : X 1 * X 2 * b 1 2 = algebraMap T Ω v := by simpa [hX, map_pow] using hv
    have h3' : algebraMap T Ω p * X 2 + algebraMap T Ω v = algebraMap T Ω r * X 1 := by
      simpa [hX, map_pow] using h3
    have e01 : b 0 1 = algebraMap T Ω q * Y 0 + algebraMap T Ω p * Y 1 := by
      linear_combination Y 0 * Y 1 * hu' - (b 0 1 * X 1 * Y 1) * hXY 0 - b 0 1 * hXY 1 +
        (algebraMap T Ω q * Y 0) * hXY 1 + (algebraMap T Ω p * Y 1) * hXY 0
    have e12 : b 1 2 = -(algebraMap T Ω p * Y 1) + algebraMap T Ω r * Y 2 := by
      linear_combination Y 1 * Y 2 * hv' + (Y 1 * Y 2) * h3' + (algebraMap T Ω r * Y 2) * hXY 1 -
        (algebraMap T Ω p * Y 1) * hXY 2 - (b 1 2 * X 2 * Y 2) * hXY 1 - b 1 2 * hXY 2
    simp only [hY] at e01 e12
    exact eq_sub_of_cocycle_fin_three hcoc (by simpa using e01) (by simpa using e12)

end Base

section General

variable {x : Fin 3 → T} {ι : Type*} [Finite ι] {y : ι → T}

/-- **Čech `H⁰` of a covering of the punctured spectrum.** Let `x 0, x 1, x 2` be a weakly
regular sequence and `y` a finite family with every `x i ∈ √(y)`. If `T` embeds into `Ω` and the
`x i` are units in `Ω`, then an element of `Ω` lying in every `awaySubring Ω (y k)` lies in the
image of `T`. -/
theorem mem_range_of_forall_mem_awaySubring (hinj : Function.Injective (algebraMap T Ω))
    (hxu : ∀ i, IsUnit (algebraMap T Ω (x i))) (hreg : IsWeaklyRegular T [x 0, x 1, x 2])
    (hrad : ∀ i, x i ∈ (Ideal.span (Set.range y)).radical) {ω : Ω}
    (h : ∀ k, ω ∈ awaySubring Ω (y k)) : ω ∈ (algebraMap T Ω).range :=
  mem_range_of_mem_awaySubring_regular hinj (hxu 0) hreg
    (mem_awaySubring_of_forall_mem_awaySubring_mul (hrad 0) fun k =>
      awaySubring_mono_of_dvd (dvd_mul_left _ _) (h k))
    (mem_awaySubring_of_forall_mem_awaySubring_mul (hrad 1) fun k =>
      awaySubring_mono_of_dvd (dvd_mul_left _ _) (h k))

/-- **Čech `H¹` of a covering of the punctured spectrum.** Let `x 0, x 1, x 2` be a weakly
regular sequence and `y` a finite family with every `x i ∈ √(y)`. If `T` embeds into `Ω` and the
`x i` are units in `Ω`, then every Čech `1`-cocycle `b k l ∈ awaySubring Ω (y k * y l)` is a
coboundary of elements `c k ∈ awaySubring Ω (y k)`. -/
theorem exists_cech_coboundary_of_forall_mem_radical (hinj : Function.Injective (algebraMap T Ω))
    (hxu : ∀ i, IsUnit (algebraMap T Ω (x i))) (hreg : IsWeaklyRegular T [x 0, x 1, x 2])
    (hrad : ∀ i, x i ∈ (Ideal.span (Set.range y)).radical) (b : ι → ι → Ω)
    (hb : ∀ k l, b k l ∈ awaySubring Ω (y k * y l)) (hcoc : ∀ k l m, b k l + b l m = b k m) :
    ∃ c : ι → Ω, (∀ k, c k ∈ awaySubring Ω (y k)) ∧ ∀ k l, b k l = c k - c l := by
  -- On each `D(x i)` the cocycle is a coboundary.
  have hC : ∀ i, ∃ c : ι → Ω, (∀ k, c k ∈ awaySubring Ω (x i * y k)) ∧
      ∀ k l, b k l = c k - c l := fun i =>
    exists_cech_coboundary_of_mem_radical (hxu i) (hrad i) b
      (fun k l => awaySubring_mono_of_dvd ⟨x i, by ring⟩ (hb k l)) hcoc
  choose C hCmem hCeq using hC
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
  · exact ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  -- The differences of the local primitives form a cocycle for the covering by the `D(x i)`.
  have hd : ∀ i j k, C i k₀ - C j k₀ = C i k - C j k := fun i j k => by
    linear_combination hCeq i k k₀ - hCeq j k k₀
  have hdmem : ∀ i j, C i k₀ - C j k₀ ∈ awaySubring Ω (x i * x j) := fun i j =>
    mem_awaySubring_of_forall_mem_awaySubring_mul (Ideal.mul_mem_right _ _ (hrad i)) fun k => by
      rw [hd i j k]
      exact sub_mem (awaySubring_mono_of_dvd ⟨x j, by ring⟩ (hCmem i k))
        (awaySubring_mono_of_dvd ⟨x i, by ring⟩ (hCmem j k))
  obtain ⟨e, he, hde⟩ := exists_cech_coboundary_regular hinj hxu hreg
    (fun i j => C i k₀ - C j k₀) hdmem (fun i j k => by ring)
  refine ⟨fun k => C 0 k - e 0, fun k => ?_, fun k l => by rw [hCeq 0 k l]; ring⟩
  have hmem : ∀ i, C i k - e i ∈ awaySubring Ω (x i * y k) := fun i =>
    sub_mem (hCmem i k) (awaySubring_le_awaySubring_mul _ _ (he i))
  exact mem_awaySubring_of_mem_awaySubring_mul_regular hinj (hxu 0) hreg (hmem 0)
    (by change C 0 k - e 0 ∈ _
        rw [show C 0 k - e 0 = C 1 k - e 1 by linear_combination hde 0 1 - hd 0 1 k]
        exact hmem 1)

end General

end Ambient

section Away

variable {x : Fin 3 → T} {ι : Type*} [Fintype ι] {y : ι → T}

/-- The embedding of `T[1/∏ k, y k]` into the total ring of fractions of `T`. -/
private noncomputable def awayToFractionRing (hy : ∀ k, y k ∈ nonZeroDivisors T) :
    Localization.Away (∏ k, y k) →+* FractionRing T :=
  IsLocalization.Away.lift (∏ k, y k)
    (IsLocalization.map_units (FractionRing T) ⟨∏ k, y k, prod_mem fun k _ => hy k⟩)

private theorem awayToFractionRing_algebraMap (hy : ∀ k, y k ∈ nonZeroDivisors T) (t : T) :
    awayToFractionRing hy (algebraMap T _ t) = algebraMap T (FractionRing T) t :=
  IsLocalization.Away.lift_eq _ _ t

private theorem awayToFractionRing_injective (hy : ∀ k, y k ∈ nonZeroDivisors T) :
    Function.Injective (awayToFractionRing hy) := by
  refine (injective_iff_map_eq_zero _).2 fun ω hω => ?_
  obtain ⟨n, t, ht⟩ := IsLocalization.Away.surj (∏ k, y k) ω
  have h0 : algebraMap T (FractionRing T) t = 0 := by
    rw [← awayToFractionRing_algebraMap hy, ← ht, map_mul, hω, zero_mul]
  rw [IsLocalization.injective (FractionRing T) le_rfl (h0.trans (map_zero _).symm), map_zero] at ht
  exact ((IsLocalization.Away.algebraMap_isUnit (∏ k, y k)).pow n).mul_left_eq_zero.1 ht

private theorem mem_awaySubring_awayToFractionRing_iff (hy : ∀ k, y k ∈ nonZeroDivisors T)
    {s : T} {ω : Localization.Away (∏ k, y k)} :
    awayToFractionRing hy ω ∈ awaySubring (FractionRing T) s ↔ ω ∈ awaySubring _ s :=
  mem_awaySubring_iff_of_injective _ (awayToFractionRing_algebraMap hy)
    (awayToFractionRing_injective hy)

/-- **Čech `H⁰` of a covering of the punctured spectrum.** Let `x 0, x 1, x 2` be a weakly
regular sequence of nonzerodivisors of `T` and `y` a finite family of nonzerodivisors with every
`x i ∈ √(y)`, so that the `D(y k)` cover the punctured spectrum `Spec T ∖ V(x 0, x 1, x 2)`. An
element of `T[1/∏ k, y k]` lying in the image of every `T[1/y k]` lies in the image of `T`. -/
theorem mem_range_of_forall_mem_awaySubring_away (hreg : IsWeaklyRegular T [x 0, x 1, x 2])
    (hx : ∀ i, x i ∈ nonZeroDivisors T) (hy : ∀ k, y k ∈ nonZeroDivisors T)
    (hrad : ∀ i, x i ∈ (Ideal.span (Set.range y)).radical) {ω : Localization.Away (∏ k, y k)}
    (h : ∀ k, ω ∈ awaySubring _ (y k)) : ω ∈ (algebraMap T _).range := by
  obtain ⟨t, ht⟩ := mem_range_of_forall_mem_awaySubring
    (IsLocalization.injective (FractionRing T) le_rfl)
    (fun i => IsLocalization.map_units (FractionRing T) ⟨x i, hx i⟩) hreg hrad
    (ω := awayToFractionRing hy ω) fun k => (mem_awaySubring_awayToFractionRing_iff hy).2 (h k)
  exact ⟨t, awayToFractionRing_injective hy (by rw [awayToFractionRing_algebraMap, ht])⟩

/-- **Čech `H¹` of a covering of the punctured spectrum.** Let `x 0, x 1, x 2` be a weakly
regular sequence of nonzerodivisors of `T` and `y` a finite family of nonzerodivisors with every
`x i ∈ √(y)`, so that the `D(y k)` cover the punctured spectrum `Spec T ∖ V(x 0, x 1, x 2)`. Every
Čech `1`-cocycle `b k l` of elements of `T[1/∏ k, y k]` in the image of `T[1/(y k * y l)]` is a
coboundary `b k l = c k - c l` of elements `c k` in the image of `T[1/y k]`. -/
theorem exists_cech_coboundary_away (hreg : IsWeaklyRegular T [x 0, x 1, x 2])
    (hx : ∀ i, x i ∈ nonZeroDivisors T) (hy : ∀ k, y k ∈ nonZeroDivisors T)
    (hrad : ∀ i, x i ∈ (Ideal.span (Set.range y)).radical)
    (b : ι → ι → Localization.Away (∏ k, y k)) (hb : ∀ k l, b k l ∈ awaySubring _ (y k * y l))
    (hcoc : ∀ k l m, b k l + b l m = b k m) :
    ∃ c : ι → Localization.Away (∏ k, y k), (∀ k, c k ∈ awaySubring _ (y k)) ∧
      ∀ k l, b k l = c k - c l := by
  set φ := awayToFractionRing hy
  obtain ⟨c', hc', hbc'⟩ := exists_cech_coboundary_of_forall_mem_radical
    (IsLocalization.injective (FractionRing T) le_rfl)
    (fun i => IsLocalization.map_units (FractionRing T) ⟨x i, hx i⟩) hreg hrad
    (fun k l => φ (b k l)) (fun k l => (mem_awaySubring_awayToFractionRing_iff hy).2 (hb k l))
    (fun k l m => by rw [← map_add, hcoc])
  have hlift : ∀ k, ∃ c, φ c = c' k := by
    intro k
    obtain ⟨n, t, ht⟩ := hc' k
    have hu : IsUnit (algebraMap T (Localization.Away (∏ k, y k)) (y k)) :=
      (IsLocalization.Away.algebraMap_isUnit_iff (∏ k, y k)).2
        ⟨1, by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)⟩
    obtain ⟨v, hv⟩ := (hu.pow n).exists_right_inv
    refine ⟨algebraMap T _ t * v, ?_⟩
    have hv' : algebraMap T (FractionRing T) (y k ^ n) * φ v = 1 := by
      rw [← awayToFractionRing_algebraMap hy, ← map_mul, map_pow, hv, map_one]
    rw [map_mul, awayToFractionRing_algebraMap, ← ht]
    linear_combination c' k * hv'
  choose c hc using hlift
  exact ⟨c, fun k => (mem_awaySubring_awayToFractionRing_iff hy).1 (by rw [hc]; exact hc' k),
    fun k l => awayToFractionRing_injective hy (by rw [map_sub, hc, hc, hbc' k l])⟩

/-- **Čech `H⁰` for Witt vectors on a covering of the punctured spectrum.** Under the hypotheses
of `mem_range_of_forall_mem_awaySubring_away`, a Witt vector over `T[1/∏ k, y k]` whose
coefficients lie in the image of every `T[1/y k]` has its coefficients in the image of `T`. -/
theorem coeff_mem_range_of_forall_coeff_mem_awaySubring_away {p : ℕ} [Fact p.Prime]
    (hreg : IsWeaklyRegular T [x 0, x 1, x 2]) (hx : ∀ i, x i ∈ nonZeroDivisors T)
    (hy : ∀ k, y k ∈ nonZeroDivisors T) (hrad : ∀ i, x i ∈ (Ideal.span (Set.range y)).radical)
    {w : WittVector p (Localization.Away (∏ k, y k))}
    (hw : ∀ k n, w.coeff n ∈ awaySubring _ (y k)) (n : ℕ) :
    w.coeff n ∈ (algebraMap T _).range :=
  WittVector.coeff_mem_of_forall_coeff_mem
    (fun _ h => mem_range_of_forall_mem_awaySubring_away hreg hx hy hrad h) hw n

/-- **Čech `H¹` for Witt vectors on a covering of the punctured spectrum.** Under the hypotheses
of `exists_cech_coboundary_away`, every Witt vector Čech `1`-cocycle `b k l` over
`T[1/∏ k, y k]` with coefficients in the image of `T[1/(y k * y l)]` is a coboundary
`b k l = c k - c l` of Witt vectors `c k` with coefficients in the image of `T[1/y k]`. -/
theorem exists_wittVector_cech_coboundary_away {p : ℕ} [Fact p.Prime]
    (hreg : IsWeaklyRegular T [x 0, x 1, x 2]) (hx : ∀ i, x i ∈ nonZeroDivisors T)
    (hy : ∀ k, y k ∈ nonZeroDivisors T) (hrad : ∀ i, x i ∈ (Ideal.span (Set.range y)).radical)
    (b : ι → ι → WittVector p (Localization.Away (∏ k, y k)))
    (hb : ∀ k l n, (b k l).coeff n ∈ awaySubring _ (y k * y l))
    (hcoc : ∀ k l m, b k l + b l m = b k m) :
    ∃ c : ι → WittVector p (Localization.Away (∏ k, y k)),
      (∀ k n, (c k).coeff n ∈ awaySubring _ (y k)) ∧ ∀ k l, b k l = c k - c l :=
  WittVector.exists_cech_coboundary (fun _ _ => awaySubring_le_awaySubring_mul _ _)
    (fun _ _ => awaySubring_mono_of_dvd (dvd_mul_left _ _))
    (fun b hb hcoc => exists_cech_coboundary_away hreg hx hy hrad b hb hcoc) b hb hcoc

end Away

end Stacks.RingTheory.PuncturedVanishing
