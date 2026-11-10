module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAway

/-!
# The localization at a multiple of a degree-one element is a Laurent extension

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `g = u h` with `u` homogeneous of degree one and
`h` homogeneous. In the localization `A[1/g]` the element `u` is a unit, of degree one, and the
integer powers of `u` form a basis of `A[1/g]` over its degree-zero part `A₍g₎`:

`A[1/g] = A₍g₎[u, u⁻¹]`.

This generalizes `Stacks.GradedLaurent.laurentAwayEquiv`, which is the case `h = 1`.

## Main definitions

* `Stacks.GradedLaurent.unitOfMul`: the image of `u` in `A[1/g]`, as a unit.
* `Stacks.GradedLaurent.laurentDivisorEquiv`: the ring isomorphism
  `A₍g₎[T;T⁻¹] ≃ A[1/g]` sending `T` to `u`.

## Main results

* `Stacks.GradedLaurent.exists_mk_eq_val_mul_zpow`: a fraction `x / gᵐ` with `x` homogeneous of
  degree `e` is `c · u^{e - m deg g}` for some `c ∈ A₍g₎`.
-/

@[expose] public noncomputable section

open HomogeneousLocalization

namespace Stacks.GradedLaurent

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {u h g : A} {d : ℕ}

/-- `g = u h` is homogeneous of degree `d + 1`. -/
theorem mem_of_mul_eq (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) : g ∈ 𝒜 (d + 1) := by
  rw [← hg, add_comm]
  exact SetLike.mul_mem_graded hu hh

/-- The element `gᵐ` of the powers of `g`. -/
abbrev powSub (g : A) (m : ℕ) : Submonoid.powers g := ⟨g ^ m, m, rfl⟩

/-- The fraction `a / g` with denominator the first power of `g`. -/
abbrev mkOne (g a : A) : Localization.Away g := Localization.mk a ⟨g, 1, pow_one g⟩

/-- For `g = u h`, the product of `u` and `h / g` is `1` in `A[1/g]`. -/
theorem algebraMap_mul_mkOne (hg : u * h = g) :
    algebraMap A (Localization.Away g) u * mkOne g h = 1 := by
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, hg]
  exact Localization.mk_self (⟨g, 1, pow_one g⟩ : Submonoid.powers g)

/-- **The image of `u` in `A[1/g]` is a unit**, with inverse `h / g`. -/
def unitOfMul (hg : u * h = g) : (Localization.Away g)ˣ where
  val := algebraMap A (Localization.Away g) u
  inv := mkOne g h
  val_inv := algebraMap_mul_mkOne hg
  inv_val := by rw [mul_comm]; exact algebraMap_mul_mkOne hg

/-- The underlying element of `unitOfMul hg` is the image of `u`. -/
@[simp]
theorem coe_unitOfMul (hg : u * h = g) :
    (unitOfMul hg : Localization.Away g) = algebraMap A (Localization.Away g) u := rfl

/-- `(x / gᵐ) · aᵏ = x aᵏ / gᵐ` in `A[1/g]`. -/
theorem mk_mul_algebraMap_pow_eq_mk (x a : A) (m k : ℕ) :
    Localization.mk x (powSub g m) * algebraMap A (Localization.Away g) a ^ k =
      Localization.mk (x * a ^ k) (powSub g m) := by
  rw [← map_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one]

/-- `x / gᵐ = x gᵏ / g^{m + k}` in `A[1/g]`. -/
theorem mk_eq_mk_mul_pow (x : A) (m k : ℕ) :
    Localization.mk x (powSub g m) =
      (Localization.mk (x * g ^ k) (powSub g (m + k)) : Localization.Away g) := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [pow_add]; ring⟩

/-- `x yᵏ` is homogeneous of degree `e + k i` for `x` of degree `e` and `y` of degree `i`. -/
private theorem mul_pow_mem_graded {x y : A} {e i n : ℕ} {k : ℕ} (hx : x ∈ 𝒜 e) (hy : y ∈ 𝒜 i)
    (hn : e + k • i = n) : x * y ^ k ∈ 𝒜 n :=
  hn ▸ SetLike.mul_mem_graded hx (SetLike.pow_mem_graded k hy)

/-- **A homogeneous fraction is a degree-zero fraction times a power of `u`**: for `x` homogeneous
of degree `e`, `x / gᵐ = c · u^{e - m(d + 1)}` with `c ∈ A₍g₎`. -/
theorem exists_mk_eq_val_mul_zpow (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) {e : ℕ}
    {x : A} (hx : x ∈ 𝒜 e) (m : ℕ) :
    ∃ c : Away 𝒜 g, Localization.mk x (powSub g m) =
      c.val * ((unitOfMul hg ^ ((e : ℤ) - m * (d + 1)) : (Localization.Away g)ˣ) :
        Localization.Away g) := by
  have hgd := mem_of_mul_eq 𝒜 hu hh hg
  rcases le_or_gt (m * (d + 1)) e with hle | hlt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hmem : x * h ^ k ∈ 𝒜 ((m + k) • (d + 1)) :=
      mul_pow_mem_graded 𝒜 hx hh (by simp only [smul_eq_mul]; ring)
    refine ⟨Away.mk 𝒜 hgd (m + k) (x * h ^ k) hmem, ?_⟩
    have hk : ((m * (d + 1) + k : ℕ) : ℤ) - m * (d + 1) = (k : ℤ) := by push_cast; ring
    rw [hk, zpow_natCast, Units.val_pow_eq_pow_val, coe_unitOfMul, Away.val_mk]
    change _ = Localization.mk (x * h ^ k) (powSub g (m + k)) *
      algebraMap A (Localization.Away g) u ^ k
    rw [mk_mul_algebraMap_pow_eq_mk, mk_eq_mk_mul_pow x m k, mul_assoc, ← mul_pow, mul_comm h u, hg]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have hmem : x * u ^ (k + 1) ∈ 𝒜 (m • (d + 1)) :=
      mul_pow_mem_graded 𝒜 hx hu (by simp only [smul_eq_mul]; lia)
    refine ⟨Away.mk 𝒜 hgd m (x * u ^ (k + 1)) hmem, ?_⟩
    have hk' : (e : ℤ) - m * (d + 1) = -((k + 1 : ℕ) : ℤ) := by
      have : ((m * (d + 1) : ℕ) : ℤ) = e + k + 1 := by exact_mod_cast hk
      push_cast at this ⊢
      linarith
    rw [hk', zpow_neg, zpow_natCast, Away.val_mk, eq_comm, Units.mul_inv_eq_iff_eq_mul,
      Units.val_pow_eq_pow_val, coe_unitOfMul]
    exact (mk_mul_algebraMap_pow_eq_mk x u m (k + 1)).symm

/-- The evaluation `T ↦ u` of a Laurent polynomial over the degree-zero localization. -/
def laurentDivisorHom (hg : u * h = g) : LaurentPolynomial (Away 𝒜 g) →+* Localization.Away g :=
  LaurentPolynomial.eval₂ (algebraMap (Away 𝒜 g) (Localization.Away g)) (unitOfMul hg)

/-- The evaluation sends `T k` to `u ^ k`. -/
@[simp]
theorem laurentDivisorHom_T (hg : u * h = g) (k : ℤ) :
    laurentDivisorHom 𝒜 hg (LaurentPolynomial.T k) =
      ((unitOfMul hg ^ k : (Localization.Away g)ˣ) : Localization.Away g) :=
  LaurentPolynomial.eval₂_T _ _ k

/-- The evaluation sends the constant `C c` to `c`, viewed in `A[1/g]`. -/
@[simp]
theorem laurentDivisorHom_C (hg : u * h = g) (c : Away 𝒜 g) :
    laurentDivisorHom 𝒜 hg (LaurentPolynomial.C c) = c.val :=
  LaurentPolynomial.eval₂_C _ _ c

/-- Every homogeneous fraction is in the image of the evaluation. -/
theorem exists_laurentDivisorHom_eq_mk (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) {e : ℕ}
    {x : A} (hx : x ∈ 𝒜 e) (m : ℕ) :
    ∃ c : Away 𝒜 g, laurentDivisorHom 𝒜 hg
      (LaurentPolynomial.C c * LaurentPolynomial.T ((e : ℤ) - m * (d + 1))) =
        Localization.mk x (powSub g m) := by
  obtain ⟨c, hc⟩ := exists_mk_eq_val_mul_zpow 𝒜 hu hh hg hx m
  exact ⟨c, by rw [map_mul, laurentDivisorHom_C, laurentDivisorHom_T, hc]⟩

/-- The evaluation is onto. -/
theorem surjective_laurentDivisorHom (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    Function.Surjective (laurentDivisorHom 𝒜 hg) := by
  classical
  intro z
  induction z using Localization.induction_on with
  | H y =>
    obtain ⟨x, s⟩ := y
    obtain ⟨m, hm⟩ := s.2
    have hs : s = (powSub g m) := Subtype.ext hm.symm
    subst hs
    have hsum : (Localization.mk x (powSub g m) : Localization.Away g) =
        ∑ e ∈ DFinsupp.support (DirectSum.decompose 𝒜 x),
          Localization.mk (DirectSum.decompose 𝒜 x e : A) (powSub g m) := by
      conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 x]
      exact Localization.mk_sum _ _ _
    rw [hsum]
    exact sum_mem (S := (laurentDivisorHom 𝒜 hg).range) fun e _ => by
      obtain ⟨c, hc⟩ := exists_laurentDivisorHom_eq_mk 𝒜 hu hh hg
        (DirectSum.decompose 𝒜 x e).2 m
      exact ⟨_, hc⟩

/-- `c · u^n` cleared of denominators: for `c = x / g^j`, `j ≤ J` and `n + N = a ≥ 0`,
`c · u^n · g^J · u^N = x g^{J - j} u^a`. -/
theorem val_mul_zpow_mul_eq (hg : u * h = g) (hgd : g ∈ 𝒜 (d + 1)) {j J : ℕ} (hjJ : j ≤ J)
    (x : A) (hx : x ∈ 𝒜 (j • (d + 1))) {n : ℤ} {N a : ℕ} (ha : (a : ℤ) = n + N) :
    (Away.mk 𝒜 hgd j x hx).val *
        ((unitOfMul hg ^ n : (Localization.Away g)ˣ) : Localization.Away g) *
        algebraMap A (Localization.Away g) (g ^ J) * algebraMap A (Localization.Away g) (u ^ N) =
      algebraMap A (Localization.Away g) (x * g ^ (J - j) * u ^ a) := by
  have hU : ((unitOfMul hg ^ n : (Localization.Away g)ˣ) : Localization.Away g) *
      algebraMap A (Localization.Away g) (u ^ N) = algebraMap A (Localization.Away g) (u ^ a) := by
    rw [map_pow, map_pow, ← coe_unitOfMul hg, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add,
      ← ha]
  have hJ : Localization.mk x (powSub g j) * algebraMap A (Localization.Away g) (g ^ J) =
      algebraMap A (Localization.Away g) (x * g ^ (J - j)) := by
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, one_mul, powSub, mul_one]
    rw [← Nat.add_sub_cancel' hjJ, pow_add, Nat.add_sub_cancel_left]
    ring
  rw [Away.val_mk, mul_right_comm _ _ (algebraMap A _ (g ^ J)), hJ, mul_assoc, hU, ← map_mul,
    mul_assoc]

/-- **The integer powers of `u` are linearly independent over the degree-zero localization.** -/
theorem linearIndependent_unitOfMul_zpow (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    LinearIndependent (Away 𝒜 g)
      (fun k : ℤ => ((unitOfMul hg ^ k : (Localization.Away g)ˣ) : Localization.Away g)) := by
  classical
  have hgd := mem_of_mul_eq 𝒜 hu hh hg
  rw [linearIndependent_iff']
  intro s c hsum n₀ hn₀
  choose jj num hnum hmk using fun n : ℤ => Away.mk_surjective 𝒜 hgd (c n)
  set J : ℕ := s.sup jj with hJdef
  set N : ℕ := s.sup fun n => (-n).toNat with hNdef
  have hjJ : ∀ n ∈ s, jj n ≤ J := fun n hn => Finset.le_sup hn
  have hnN : ∀ n ∈ s, (0 : ℤ) ≤ n + N := by
    intro n hn
    have h' : ((-n).toNat : ℤ) ≤ (N : ℤ) :=
      Int.ofNat_le.mpr (Finset.le_sup (f := fun n : ℤ => (-n).toNat) hn)
    lia
  set a : ℤ → ℕ := fun n => (n + N).toNat with hadef
  have ha : ∀ n ∈ s, (a n : ℤ) = n + N := fun n hn => Int.toNat_of_nonneg (hnN n hn)
  have hterm : ∀ n ∈ s, c n • ((unitOfMul hg ^ n : (Localization.Away g)ˣ) : Localization.Away g)
      * algebraMap A (Localization.Away g) (g ^ J) * algebraMap A (Localization.Away g) (u ^ N)
      = algebraMap A (Localization.Away g) (num n * g ^ (J - jj n) * u ^ a n) := by
    intro n hn
    rw [smul_eq_val_mul, ← hmk n]
    exact val_mul_zpow_mul_eq 𝒜 hg hgd (hjJ n hn) (num n) (hnum n) (ha n hn)
  have hzero : algebraMap A (Localization.Away g)
      (∑ n ∈ s, num n * g ^ (J - jj n) * u ^ a n) = 0 := by
    rw [map_sum, ← Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_mul, hsum,
      zero_mul, zero_mul]
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g)] at hzero
  obtain ⟨t, hp⟩ := hzero
  obtain ⟨q, hqt⟩ := t.2
  rw [← hqt, Finset.mul_sum] at hp
  have hdeg : ∀ n ∈ s, g ^ q * (num n * g ^ (J - jj n) * u ^ a n) ∈
      𝒜 ((q + J) * (d + 1) + a n) := by
    intro n hn
    have hmem := SetLike.mul_mem_graded (SetLike.pow_mem_graded q hgd)
      (SetLike.mul_mem_graded
        (SetLike.mul_mem_graded (hnum n) (SetLike.pow_mem_graded (J - jj n) hgd))
        (SetLike.pow_mem_graded (a n) hu))
    have hidx : q • (d + 1) + (jj n • (d + 1) + (J - jj n) • (d + 1) + a n • 1) =
        (q + J) * (d + 1) + a n := by
      simp only [smul_eq_mul, mul_one]
      zify [hjJ n hn]
      ring
    rwa [hidx] at hmem
  have hinj : Set.InjOn (fun n => (q + J) * (d + 1) + a n) s := by
    intro n hn n' hn' hEq
    simp only at hEq
    have := ha n hn
    have := ha n' hn'
    lia
  have hvanish := eq_zero_of_sum_eq_zero_of_injOn 𝒜 hinj hdeg hp hn₀
  have hnumzero : algebraMap A (Localization.Away g) (num n₀) = 0 := by
    have hunit :
        IsUnit (algebraMap A (Localization.Away g) (g ^ (q + (J - jj n₀)) * u ^ a n₀)) := by
      rw [map_mul, map_pow, map_pow, ← coe_unitOfMul hg]
      exact ((IsLocalization.map_units (Localization.Away g)
        (⟨g, 1, pow_one g⟩ : Submonoid.powers g)).pow _).mul ((unitOfMul hg).isUnit.pow _)
    refine (hunit.mul_left_eq_zero).1 ?_
    rw [← map_mul]
    calc algebraMap A (Localization.Away g) (num n₀ * (g ^ (q + (J - jj n₀)) * u ^ a n₀))
        = algebraMap A (Localization.Away g) (g ^ q * (num n₀ * g ^ (J - jj n₀) * u ^ a n₀)) := by
          rw [pow_add]; ring_nf
      _ = 0 := by rw [hvanish, map_zero]
  rw [← hmk n₀, ← HomogeneousLocalization.val_injective (Submonoid.powers g) |>.eq_iff,
    HomogeneousLocalization.val_zero, Away.val_mk, mk_eq_algebraMap_mul, hnumzero, zero_mul]

/-- The evaluation is injective. -/
theorem injective_laurentDivisorHom (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    Function.Injective (laurentDivisorHom 𝒜 hg) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hsum : ∑ n ∈ (AddMonoidAlgebra.coeff p).support, AddMonoidAlgebra.coeff p n •
      ((unitOfMul hg ^ n : (Localization.Away g)ˣ) : Localization.Away g)
      = laurentDivisorHom 𝒜 hg p := by
    conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, laurentDivisorHom_C, laurentDivisorHom_T,
      smul_eq_val_mul]
  have hli := linearIndependent_iff'.mp (linearIndependent_unitOfMul_zpow 𝒜 hu hh hg)
    (AddMonoidAlgebra.coeff p).support (AddMonoidAlgebra.coeff p) (hsum.trans hp)
  refine LaurentPolynomial.ext_iff.mpr fun k => ?_
  by_cases hk : k ∈ (AddMonoidAlgebra.coeff p).support
  · exact hli k hk
  · simpa using hk

/-- **The Laurent identification**: for `g = u h` with `u` of degree one, `A[1/g]` is the Laurent
extension `A₍g₎[u, u⁻¹]` of its degree-zero part. -/
def laurentDivisorEquiv (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g) :
    LaurentPolynomial (Away 𝒜 g) ≃+* Localization.Away g :=
  RingEquiv.ofBijective (laurentDivisorHom 𝒜 hg)
    ⟨injective_laurentDivisorHom 𝒜 hu hh hg, surjective_laurentDivisorHom 𝒜 hu hh hg⟩

/-- The Laurent identification agrees with the evaluation `T ↦ u`. -/
@[simp]
theorem laurentDivisorEquiv_apply (hu : u ∈ 𝒜 1) (hh : h ∈ 𝒜 d) (hg : u * h = g)
    (p : LaurentPolynomial (Away 𝒜 g)) :
    laurentDivisorEquiv 𝒜 hu hh hg p = laurentDivisorHom 𝒜 hg p := rfl

end Stacks.GradedLaurent

end
