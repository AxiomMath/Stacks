module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal homeomorphisms: power conditions

The field theory and the combinatorial computation behind the criteria for universal
homeomorphisms of `StacksFrontier.RingTheory.UniversalHomeomorphism.Examples`.

## Main definitions

* `Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.subringR`: the subring `ℤ[x ^ p ^ n, p ^ n
  x, y ^ p ^ m, p ^ m y]` of
  `ℤ[x, y] = MvPolynomial (Fin 2) ℤ`, where `x` and `y` are the two indeterminates `X 0`, `X 1`.

## Main results

* `Stacks.UniversalHomeomorphism.FrobeniusPowerSubring.exists_pow_mem`: `(x + y) ^ p ^ a` and `p ^
  a (x + y)` lie in
  `ℤ[x ^ p ^ n, p ^ n x, y ^ p ^ m, p ^ m y]` for some `a`.
* `satisfiesGeneratingCondition_iff_structuralCondition`: for a field `K` with a subfield `k` and
  a prime `p`, the elements admitting an `n > 0` with `x ^ p ^ n ∈ k` and `p ^ n • x ∈ k` generate
  `K` over `k` if and only if `k = K`, or `char K = p` and `K / k` is purely inseparable.
* `forall_exists_pow_mem_iff_isPurelyInseparable_or_isAlgebraic_bot`: a field extension in which
  every element has a positive power in the base is purely inseparable, or of positive
  characteristic and algebraic over its prime field.

## References

* [Stacks Project, Tag 0545](https://stacks.math.columbia.edu/tag/0545)
* [Stacks Project, Tag 0BR7](https://stacks.math.columbia.edu/tag/0BR7)
* [Stacks Project, Tag 0BR9](https://stacks.math.columbia.edu/tag/0BR9)
-/

@[expose] public section

namespace Stacks.UniversalHomeomorphism.FrobeniusPowerSubring

open MvPolynomial

/-- The `ℤ`-subalgebra `ℤ[x ^ p ^ n, p ^ n x, y ^ p ^ m, p ^ m y]` of
`ℤ[x, y] = MvPolynomial (Fin 2) ℤ`, where `x = X 0` and `y = X 1`. -/
noncomputable def subringR (p n m : ℕ) : Subalgebra ℤ (MvPolynomial (Fin 2) ℤ) :=
  Algebra.adjoin ℤ {(X 0 : MvPolynomial (Fin 2) ℤ) ^ p ^ n, (p ^ n : ℤ) • X 0, X 1 ^ p ^ m,
    (p ^ m : ℤ) • X 1}

/-- If a `ℤ`-subalgebra contains `z ^ d` and `d • z`, then it contains `d ^ (i % d) • z ^ i`:
writing `i = d * (i / d) + i % d`, that element is `(z ^ d) ^ (i / d) * (d • z) ^ (i % d)`. -/
private theorem zsmul_pow_mem {A : Type*} [CommRing A] {T : Subalgebra ℤ A} {z : A} {d : ℕ}
    (h₁ : z ^ d ∈ T) (h₂ : (d : ℤ) • z ∈ T) (i : ℕ) : (d : ℤ) ^ (i % d) • z ^ i ∈ T := by
  have key : (d : ℤ) ^ (i % d) • z ^ i = (z ^ d) ^ (i / d) * ((d : ℤ) • z) ^ (i % d) := by
    rw [smul_pow, mul_smul_comm, ← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [key]
  exact mul_mem (pow_mem h₁ _) (pow_mem h₂ _)

/-- If a `ℤ`-subalgebra contains `z ^ d`, `d • z`, `w ^ e` and `e • w`, then it contains the
monomial `(c * d ^ (i % d) * e ^ (j % e)) • (z ^ i * w ^ j)` for every integer `c`. -/
private theorem zsmul_mul_pow_mem {A : Type*} [CommRing A] {T : Subalgebra ℤ A} {z w : A}
    {d e : ℕ} (hz : z ^ d ∈ T) (hz' : (d : ℤ) • z ∈ T) (hw : w ^ e ∈ T) (hw' : (e : ℤ) • w ∈ T)
    (c : ℤ) (i j : ℕ) :
    (c * (d : ℤ) ^ (i % d) * (e : ℤ) ^ (j % e)) • (z ^ i * w ^ j) ∈ T := by
  rw [mul_assoc, ← smul_smul, ← smul_mul_smul_comm]
  exact T.smul_mem (mul_mem (zsmul_pow_mem hz hz' i) (zsmul_pow_mem hw hw' j)) c

/-- A `ℤ`-subalgebra containing `d • z` contains `e • z` for every multiple `e` of `d`. -/
private theorem zsmul_mem_of_dvd {A : Type*} [CommRing A] {T : Subalgebra ℤ A} {z : A} {d e : ℤ}
    (hde : d ∣ e) (h : d • z ∈ T) : e • z ∈ T := by
  obtain ⟨c, rfl⟩ := hde
  rw [mul_comm, mul_smul]
  exact T.smul_mem h c

/-- For `0 < k ≤ p ^ a` and `p` prime, `p ^ (a - v_p k)` divides `(p ^ a).choose k`, where `v_p` is
the `p`-adic valuation: the valuation of the binomial coefficient is exactly `a - v_p k`. -/
@[sga "3 VIIA 8.5.1" "vanishing of binomial(p"]
private theorem pow_sub_padicValNat_dvd_choose {p a k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hka : k ≤ p ^ a) : p ^ (a - padicValNat p k) ∣ (p ^ a).choose k := by
  rw [← Nat.factorization_def _ hp, ← Nat.factorization_choose_prime_pow hp hka hk]
  exact Nat.ordProj_dvd _ p

/-- As soon as `n, m ≤ a` and `n * p ^ n + m * p ^ m + n + m ≤ a`, the binomial coefficient
`(p ^ a).choose k` is divisible by the power of `p` that `zsmul_mul_pow_mem` asks of the `k`-th
term of `(x + y) ^ p ^ a`. Indeed the two residues `k % p ^ n` and `(p ^ a - k) % p ^ m` vanish
once `v_p k` is at least `n`, resp. `m`, so the exponent
`n * (k % p ^ n) + m * ((p ^ a - k) % p ^ m)` is bounded by `a - v_p k`. -/
private theorem pow_dvd_choose {p : ℕ} (hp : p.Prime) {n m a : ℕ} (hna : n ≤ a) (hma : m ≤ a)
    (ha : n * p ^ n + m * p ^ m + n + m ≤ a) {k : ℕ} (hk : k ≤ p ^ a) :
    p ^ (n * (k % p ^ n) + m * ((p ^ a - k) % p ^ m)) ∣ (p ^ a).choose k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk₀
  · simp [Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hma)]
  rcases eq_or_lt_of_le hk with rfl | hklt
  · simp [Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hna)]
  set v := padicValNat p k with hv
  have hpv : p ^ v ∣ k := pow_padicValNat_dvd
  have hva : v < a := by
    by_contra hcon
    exact absurd (Nat.le_of_dvd hk₀ ((pow_dvd_pow p (not_lt.mp hcon)).trans hpv)) (by omega)
  have hr : n ≤ v → k % p ^ n = 0 := fun h =>
    Nat.mod_eq_zero_of_dvd ((pow_dvd_pow p h).trans hpv)
  have hr' : m ≤ v → (p ^ a - k) % p ^ m = 0 := fun h =>
    Nat.mod_eq_zero_of_dvd ((pow_dvd_pow p h).trans (Nat.dvd_sub (pow_dvd_pow p hva.le) hpv))
  refine (pow_dvd_pow p ?_).trans (pow_sub_padicValNat_dvd_choose hp hk₀.ne' hk)
  have h₁ : n * (k % p ^ n) ≤ n * p ^ n :=
    Nat.mul_le_mul_left n (Nat.mod_lt _ (pow_pos hp.pos n)).le
  have h₂ : m * ((p ^ a - k) % p ^ m) ≤ m * p ^ m :=
    Nat.mul_le_mul_left m (Nat.mod_lt _ (pow_pos hp.pos m)).le
  rcases Nat.lt_or_ge v n with h | h <;> rcases Nat.lt_or_ge v m with h' | h'
  · omega
  · rw [hr' h']; omega
  · rw [hr h]; omega
  · rw [hr h, hr' h']; omega

/-- Let `p` be a prime number and `n, m > 0`. Then there is an `a` such that both
`(x + y) ^ p ^ a` and `p ^ a (x + y)` lie in `R = ℤ[x ^ p ^ n, p ^ n x, y ^ p ^ m, p ^ m y]`,
where `x = X 0` and `y = X 1`. -/
@[stacks 0545]
theorem exists_pow_mem (p : ℕ) (hp : p.Prime) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ a : ℕ, (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) ^ p ^ a ∈ subringR p n m ∧
      (p ^ a : ℤ) • (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) ∈ subringR p n m := by
  have hx : (X 0 : MvPolynomial (Fin 2) ℤ) ^ p ^ n ∈ subringR p n m :=
    Algebra.subset_adjoin (by simp)
  have hx' : ((p ^ n : ℕ) : ℤ) • (X 0 : MvPolynomial (Fin 2) ℤ) ∈ subringR p n m := by
    rw [Nat.cast_pow]
    exact Algebra.subset_adjoin (by simp)
  have hy : (X 1 : MvPolynomial (Fin 2) ℤ) ^ p ^ m ∈ subringR p n m :=
    Algebra.subset_adjoin (by simp)
  have hy' : ((p ^ m : ℕ) : ℤ) • (X 1 : MvPolynomial (Fin 2) ℤ) ∈ subringR p n m := by
    rw [Nat.cast_pow]
    exact Algebra.subset_adjoin (by simp)
  set a := n * p ^ n + m * p ^ m + n + m with ha
  refine ⟨a, ?_, ?_⟩
  · rw [add_pow]
    refine Subalgebra.sum_mem _ fun k hk => ?_
    rw [Finset.mem_range] at hk
    obtain ⟨c, hc⟩ := pow_dvd_choose hp (n := n) (m := m) (by omega) (by omega) ha.ge
      (k := k) (by omega)
    have hcast : ((p ^ a).choose k : ℤ) = (c : ℤ) * ((p ^ n : ℕ) : ℤ) ^ (k % p ^ n) *
        ((p ^ m : ℕ) : ℤ) ^ ((p ^ a - k) % p ^ m) := by
      have hc' := congrArg (Nat.cast (R := ℤ)) hc
      push_cast at hc' ⊢
      rw [hc', pow_add, pow_mul, pow_mul]
      ring
    have hterm : (X 0 : MvPolynomial (Fin 2) ℤ) ^ k * X 1 ^ (p ^ a - k) *
        ((p ^ a).choose k : MvPolynomial (Fin 2) ℤ)
        = ((c : ℤ) * ((p ^ n : ℕ) : ℤ) ^ (k % p ^ n) *
            ((p ^ m : ℕ) : ℤ) ^ ((p ^ a - k) % p ^ m)) •
          ((X 0 : MvPolynomial (Fin 2) ℤ) ^ k * X 1 ^ (p ^ a - k)) := by
      rw [← hcast, zsmul_eq_mul, Int.cast_natCast]
      exact mul_comm _ _
    rw [hterm]
    exact zsmul_mul_pow_mem hx hx' hy hy' _ k (p ^ a - k)
  · rw [smul_add]
    exact add_mem (zsmul_mem_of_dvd (by push_cast; exact pow_dvd_pow _ (by omega)) hx')
      (zsmul_mem_of_dvd (by push_cast; exact pow_dvd_pow _ (by omega)) hy')

end Stacks.UniversalHomeomorphism.FrobeniusPowerSubring

/-- The elements of `K` admitting an `n > 0` with `x ^ p ^ n ∈ k` and `p ^ n • x ∈ k`: the
"arithmetic" generating set of the source, for the extension `K / k` and the prime `p`. -/
private abbrev Subfield.powNsmulSet {K : Type*} [Field K] (k : Subfield K) (p : ℕ) : Set K :=
  {x : K | ∃ n > 0, x ^ p ^ n ∈ k ∧ (p ^ n : ℕ) • x ∈ k}

/-- The image of a subfield under its inclusion into the ambient field is the subfield itself. -/
private theorem Subfield.mem_range_algebraMap_iff {K : Type*} [Field K] {k : Subfield K} {x : K} :
    x ∈ (algebraMap k K).range ↔ x ∈ k :=
  ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- A subfield has the characteristic of the ambient field, hence also its exponential
characteristic. -/
private theorem Subfield.expChar_of_ringChar_eq {K : Type*} [Field K] (k : Subfield K) {p : ℕ}
    [Fact p.Prime] (h : ringChar K = p) : ExpChar k p :=
  have : CharP k p := ((Algebra.ringChar_eq k K).trans h) ▸ ringChar.charP k
  expChar_prime k p

/-- Let `K / k` be a field extension and `p` a prime. Then `K` is generated as a field extension
of `k` by the elements `x` admitting an `n > 0` with `x ^ p ^ n ∈ k` and `p ^ n • x ∈ k` — the
generating condition of the source — if and only if either `k = K`, or the characteristic is `p`
and `K / k` is purely inseparable, which is the source's structural condition.

The two directions are the two halves of the perfect closure: in characteristic `p` the generators
lie in the perfect closure of `k`, which is therefore all of `K`; away from `p` the multiple
`p ^ n • x` of a generator is `x` times a unit of `k`, so the generators lie in `k` already. -/
@[stacks 0BR9]
public theorem satisfiesGeneratingCondition_iff_structuralCondition
    {K : Type*} [Field K] (k : Subfield K) (p : ℕ) (hp : p.Prime) :
    Subfield.closure ((k : Set K) ∪ {x : K | ∃ n > 0, x ^ p ^ n ∈ k ∧ (p ^ n : ℕ) • x ∈ k}) = ⊤ ↔
      k = ⊤ ∨ (ringChar K = p ∧ IsPurelyInseparable k K) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  change Subfield.closure ((k : Set K) ∪ k.powNsmulSet p) = ⊤ ↔ _
  constructor
  · intro hgen
    by_cases hchar : ringChar K = p
    · have hexp : ExpChar k p := k.expChar_of_ringChar_eq hchar
      have hmem : ∀ x : K, x ∈ (perfectClosure k K).toSubfield ↔ ∃ n, x ^ p ^ n ∈ k := fun x => by
        rw [IntermediateField.mem_toSubfield, mem_perfectClosure_iff, ringExpChar.eq k p]
        exact exists_congr fun _ => Subfield.mem_range_algebraMap_iff
      have hle : Subfield.closure ((k : Set K) ∪ k.powNsmulSet p) ≤
          (perfectClosure k K).toSubfield := by
        rw [Subfield.closure_le]
        rintro x (hx | ⟨n, -, hpow, -⟩)
        · exact (hmem x).mpr ⟨0, by simpa using hx⟩
        · exact (hmem x).mpr ⟨n, hpow⟩
      have htop : (perfectClosure k K).toSubfield = ⊤ := top_le_iff.mp (hgen.ge.trans hle)
      refine Or.inr ⟨hchar, (isPurelyInseparable_iff_pow_mem k p).mpr fun x => ?_⟩
      obtain ⟨n, hn⟩ := (hmem x).mp (htop.ge (Subfield.mem_top x))
      exact ⟨n, Subfield.mem_range_algebraMap_iff.mpr hn⟩
    · refine Or.inl ?_
      have hsub : k.powNsmulSet p ⊆ (k : Set K) := by
        rintro x ⟨n, -, -, hsmul⟩
        have hne : ((p ^ n : ℕ) : K) ≠ 0 := by
          rw [Nat.cast_pow]
          exact pow_ne_zero _ (CharP.cast_ne_zero_of_ne_of_prime K hp hchar)
        rw [nsmul_eq_mul] at hsmul
        simpa only [inv_mul_cancel_left₀ hne, SetLike.mem_coe] using
          k.mul_mem (k.inv_mem (natCast_mem k (p ^ n))) hsmul
      rwa [Set.union_eq_self_of_subset_right hsub, Subfield.closure_eq] at hgen
  · rintro (hktop | ⟨hchar, hinsep⟩)
    · rw [eq_top_iff, ← hktop]
      exact fun x hx => Subfield.subset_closure (Or.inl hx)
    · have hexp : ExpChar k p := k.expChar_of_ringChar_eq hchar
      have hck : CharP K p := hchar ▸ ringChar.charP K
      refine eq_top_iff.mpr fun x _ => Subfield.subset_closure (Or.inr ?_)
      obtain ⟨m, hm⟩ := (isPurelyInseparable_iff_pow_mem k p).mp hinsep x
      refine ⟨m + 1, m.succ_pos, ?_, ?_⟩
      · rw [pow_succ, pow_mul]
        exact k.pow_mem (Subfield.mem_range_algebraMap_iff.mp hm) p
      · rw [nsmul_eq_mul, (CharP.cast_eq_zero_iff K p _).mpr (dvd_pow_self p m.succ_ne_zero),
          zero_mul]
        exact k.zero_mem

section

open Polynomial

/-! ### Roots of unity -/

/-- A root of unity is integral over any base ring: it is a root of the monic `X ^ n - 1`. -/
private lemma IsOfFinOrder.isIntegral {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {w : A}
    (hw : IsOfFinOrder w) : IsIntegral R w := by
  obtain ⟨n, hn, hwn⟩ := isOfFinOrder_iff_pow_eq_one.mp hw
  exact ⟨X ^ n - 1, by simpa using monic_X_pow_sub_C (1 : R) hn.ne', by simp [hwn]⟩

/-- A nonzero element algebraic over a finite field is a root of unity: it lies in a finite
subextension, whose nonzero elements form a finite group. -/
private lemma isOfFinOrder_of_isAlgebraic {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    {x : K} (hx : IsAlgebraic F x) (hx0 : x ≠ 0) : IsOfFinOrder x := by
  have : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set K)) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      rw [Set.mem_singleton_iff] at hy; exact hy ▸ hx.isIntegral
  have : Finite (IntermediateField.adjoin F ({x} : Set K)) := Module.finite_of_finite F
  set a : IntermediateField.adjoin F ({x} : Set K) :=
    ⟨x, IntermediateField.subset_adjoin F _ rfl⟩ with ha
  have ha0 : a ≠ 0 := by
    simp only [ne_eq, ha, ← ZeroMemClass.coe_eq_zero]
    exact hx0
  refine (Function.Injective.isOfFinOrder_iff (f := (algebraMap _ K).toMonoidHom)
    (FaithfulSMul.algebraMap_injective _ K) (x := a)).mpr ?_
  exact (isUnit_iff_ne_zero.mpr ha0).isOfFinOrder

/-- A number field contains only finitely many roots of unity. -/
private lemma finite_setOf_isOfFinOrder (L : Type*) [Field L] [NumberField L] :
    {w : L | IsOfFinOrder w}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le L ℂ 1).subset fun w hw => ?_
  obtain ⟨n, hn, hwn⟩ := isOfFinOrder_iff_pow_eq_one.mp hw
  refine ⟨IsOfFinOrder.isIntegral hw, fun φ => le_of_eq ?_⟩
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp ?_
  rw [← norm_pow, ← map_pow, hwn, map_one, norm_one]

/-- Only finitely many roots of unity of a field lie in a given number field inside it. -/
private lemma finite_setOf_isOfFinOrder_mem {A : Type*} [Field A] [Algebra ℚ A]
    (L : IntermediateField ℚ A) [NumberField L] : {w : A | w ∈ L ∧ IsOfFinOrder w}.Finite := by
  refine ((finite_setOf_isOfFinOrder L).image (fun z : L => (z : A))).subset ?_
  rintro w ⟨hwL, hw⟩
  refine ⟨⟨w, hwL⟩, ?_, rfl⟩
  exact (Function.Injective.isOfFinOrder_iff (f := (L.val : L →* A)) L.val.injective).mp hw

/-- The Möbius transformation `y ↦ (c * u + y) / (u + y)` is injective away from its pole, provided
`u ≠ 0` and `c ≠ 1`: it differs from `1` by `(c - 1) * u / (u + y)`. -/
private lemma eq_of_div_add_eq_div_add {A : Type*} [Field A] {c u a b : A} (hu : u ≠ 0) (hc : c ≠ 1)
    (ha : u + a ≠ 0) (hb : u + b ≠ 0)
    (hab : (c * u + a) / (u + a) = (c * u + b) / (u + b)) : a = b := by
  rw [div_eq_div_iff ha hb] at hab
  have h : u * (c - 1) * (a - b) = 0 := by linear_combination -hab
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hu
    · exact absurd (sub_eq_zero.mp h2) hc
  · exact sub_eq_zero.mp h1

/-! ### Roots of unity from the power condition -/

section Extension

variable {k k' Ω : Type*} [Field k] [Field k'] [Field Ω] [Algebra k k'] [Algebra k Ω]
  [Algebra k' Ω] [IsScalarTower k k' Ω]

/-- The power condition makes the extension algebraic. -/
private lemma isAlgebraic_of_forall_exists_pow_mem
    (h : ∀ z : k', ∃ n > 0, z ^ n ∈ (algebraMap k k').range) : Algebra.IsAlgebraic k k' := by
  refine ⟨fun z => ?_⟩
  obtain ⟨n, hn, a, ha⟩ := h z
  exact ⟨X ^ n - C a, (monic_X_pow_sub_C a hn.ne').ne_zero, by simp [← ha]⟩

/-- An element outside the base field is not the negative of a base-field element. -/
private lemma add_algebraMap_ne_zero {x : k'} (hx : x ∉ (algebraMap k k').range) (y : k) :
    x + algebraMap k k' y ≠ 0 :=
  fun hc => hx ⟨-y, by rw [map_neg]; linear_combination -hc⟩

/-- The same, seen in an extension of `k'`. -/
private lemma algebraMap_add_algebraMap_ne_zero {x : k'} (hx : x ∉ (algebraMap k k').range)
    (y : k) : algebraMap k' Ω x + algebraMap k Ω y ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply k k' Ω, ← map_add, ne_eq, map_eq_zero]
  exact add_algebraMap_ne_zero hx y

/-- An element outside the base field has nonzero image in any extension of `k'`. -/
private lemma algebraMap_ne_zero_of_notMem {x : k'} (hx : x ∉ (algebraMap k k').range) :
    algebraMap k' Ω x ≠ 0 := by
  simpa using algebraMap_add_algebraMap_ne_zero (Ω := Ω) hx 0

/-- If `z ^ n` lies in the base field, every root of the minimal polynomial of `z` is an `n`-th
root of unity times `z`. -/
private lemma isOfFinOrder_div {z : k'} (hz : z ≠ 0) {n : ℕ} (hn : 0 < n) {a : k}
    (hza : z ^ n = algebraMap k k' a) {s : Ω} (hs : aeval s (minpoly k z) = 0) :
    IsOfFinOrder (s / algebraMap k' Ω z) := by
  have hz' : algebraMap k' Ω z ≠ 0 := by simpa using hz
  obtain ⟨c, hc⟩ := minpoly.dvd k z (p := X ^ n - C a) (by simp [hza])
  have hsn : s ^ n = algebraMap k Ω a := by
    have h2 : (Polynomial.aeval s) (X ^ n - C a) = 0 := by rw [hc]; simp [hs]
    simp only [map_sub, map_pow, aeval_X, aeval_C] at h2
    linear_combination h2
  have hzn : (algebraMap k' Ω z) ^ n = algebraMap k Ω a := by
    rw [← map_pow, hza, ← IsScalarTower.algebraMap_apply]
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  rw [div_pow, hsn, hzn, div_self (by rw [← hzn]; exact pow_ne_zero _ hz')]

omit [Algebra k' Ω] [IsScalarTower k k' Ω] in
/-- Translating a root of the minimal polynomial of `x` by an element of the base field. -/
private lemma aeval_add_algebraMap_minpoly_add {x : k'} {r : Ω}
    (hr : aeval r (minpoly k x) = 0) (y : k) :
    aeval (r + algebraMap k Ω y) (minpoly k (x + algebraMap k k' y)) = 0 := by
  rw [minpoly.add_algebraMap, aeval_comp]
  simp [hr]

/-- For every `y` in the base field, the ratio of the conjugate `r + y` of `x + y` by `x + y`
itself is a root of unity. -/
private lemma isOfFinOrder_div_add (h : ∀ z : k', ∃ n > 0, z ^ n ∈ (algebraMap k k').range)
    {x : k'} (hx : x ∉ (algebraMap k k').range) {r : Ω} (hr : aeval r (minpoly k x) = 0) (y : k) :
    IsOfFinOrder ((r + algebraMap k Ω y) / (algebraMap k' Ω x + algebraMap k Ω y)) := by
  obtain ⟨n, hn, a, ha⟩ := h (x + algebraMap k k' y)
  have h2 := isOfFinOrder_div (Ω := Ω) (add_algebraMap_ne_zero hx y) hn ha.symm
    (aeval_add_algebraMap_minpoly_add hr y)
  rwa [map_add, ← IsScalarTower.algebraMap_apply] at h2

/-- The source's computation: an element `x` outside the base field with a conjugate `r ≠ x` is a
ratio of two roots of unity. Comparing the conjugates of `x` and of `x + 1` gives roots of unity
`ζ ≠ 1` and `ζ'` with `r = ζ · x` and `x · (ζ - ζ') = ζ' - 1`; the latter forces `ζ ≠ ζ'` and so
expresses `x` as `(ζ' - 1) / (ζ - ζ')`. -/
private lemma exists_isOfFinOrder_algebraMap_eq_div
    (h : ∀ z : k', ∃ n > 0, z ^ n ∈ (algebraMap k k').range)
    {x : k'} (hx : x ∉ (algebraMap k k').range) {r : Ω} (hr : aeval r (minpoly k x) = 0)
    (hne : r ≠ algebraMap k' Ω x) :
    ∃ ζ ζ' : Ω, IsOfFinOrder ζ ∧ IsOfFinOrder ζ' ∧ ζ ≠ 1 ∧ ζ ≠ ζ' ∧
      r = ζ * algebraMap k' Ω x ∧ algebraMap k' Ω x = (ζ' - 1) / (ζ - ζ') := by
  have hζ : IsOfFinOrder (r / algebraMap k' Ω x) := by
    simpa using isOfFinOrder_div_add h hx hr 0
  have hζ' : IsOfFinOrder ((r + 1) / (algebraMap k' Ω x + 1)) := by
    simpa using isOfFinOrder_div_add h hx hr 1
  have hu : algebraMap k' Ω x ≠ 0 := algebraMap_ne_zero_of_notMem hx
  have hv : algebraMap k' Ω x + 1 ≠ 0 := by
    simpa using algebraMap_add_algebraMap_ne_zero (Ω := Ω) hx 1
  set u := algebraMap k' Ω x
  have hkey : u * (r / u - (r + 1) / (u + 1)) = (r + 1) / (u + 1) - 1 := by
    field_simp
    ring
  have hζ1 : r / u ≠ 1 := by rw [Ne, div_eq_one_iff_eq hu]; exact hne
  have hζζ' : r / u ≠ (r + 1) / (u + 1) := fun hc => by
    rw [hc, sub_self, mul_zero] at hkey
    exact hζ1 (hc.trans (by linear_combination -hkey))
  exact ⟨r / u, (r + 1) / (u + 1), hζ, hζ', hζ1, hζζ', (div_mul_cancel₀ r hu).symm,
    by rw [eq_div_iff (sub_ne_zero.mpr hζζ')]; linear_combination hkey⟩

variable [IsAlgClosed Ω]

/-- A separable element outside the base field has a conjugate other than itself. -/
private lemma exists_ne_aeval_minpoly_eq_zero {x : k'} (hsep : IsSeparable k x)
    (hx : x ∉ (algebraMap k k').range) :
    ∃ r : Ω, aeval r (minpoly k x) = 0 ∧ r ≠ algebraMap k' Ω x := by
  classical
  have hint : IsIntegral k x := hsep.isIntegral
  set q : Polynomial Ω := (minpoly k x).map (algebraMap k Ω) with hq
  have hq0 : q ≠ 0 := by
    rw [hq, Ne, Polynomial.map_eq_zero]
    exact minpoly.ne_zero hint
  have hnodup : q.roots.Nodup := nodup_roots (Polynomial.Separable.map hsep)
  have hcard : q.roots.card = (minpoly k x).natDegree := by
    rw [splits_iff_card_roots.mp (IsAlgClosed.splits q), hq, natDegree_map]
  have h0 : (minpoly k x).natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have h1 : (minpoly k x).natDegree ≠ 1 := fun hh => hx (minpoly.natDegree_eq_one_iff.mp hh)
  have hmemx : algebraMap k' Ω x ∈ q.roots := by
    rw [mem_roots hq0, IsRoot, hq, eval_map, ← aeval_def,
      aeval_algebraMap_apply Ω, minpoly.aeval, map_zero]
  have hpos : 0 < (q.roots.erase (algebraMap k' Ω x)).card := by
    rw [Multiset.card_erase_of_mem hmemx, hcard, Nat.pred_eq_sub_one]
    omega
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  rw [hnodup.mem_erase_iff] at hr
  refine ⟨r, ?_, hr.1⟩
  have h2 := (mem_roots hq0).mp hr.2
  rwa [IsRoot, hq, eval_map, ← aeval_def] at h2

end Extension

/-! ### Positive characteristic -/

section Conclusion

variable {k k' : Type*} [Field k] [Field k'] [Algebra k k']

/-- In positive characteristic, a separable element `w` outside the base field is algebraic over
the prime field: `w` is a ratio of two roots of unity, hence algebraic over the prime field of `Ω`,
which is finite, and therefore `w` is itself a root of unity. -/
private lemma isAlgebraic_bot_of_isSeparable_notMem (Ω : Type*) [Field Ω] [Algebra k Ω]
    [Algebra k' Ω] [IsScalarTower k k' Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP k' p]
    (h : ∀ z : k', ∃ n > 0, z ^ n ∈ (algebraMap k k').range)
    {w : k'} (hsep : IsSeparable k w) (hw : w ∉ (algebraMap k k').range) :
    IsAlgebraic ↥(⊥ : Subfield k') w := by
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap k' Ω).injective p
  have : Finite ↥(⊥ : Subfield Ω) := let := Subfield.fintypeBot Ω p; inferInstance
  obtain ⟨r, hr, hrne⟩ := exists_ne_aeval_minpoly_eq_zero (Ω := Ω) hsep hw
  obtain ⟨ζ, ζ', hζ, hζ', -, -, -, hweq⟩ := exists_isOfFinOrder_algebraMap_eq_div h hw hr hrne
  have hw0 : algebraMap k' Ω w ≠ 0 := algebraMap_ne_zero_of_notMem hw
  have halg : IsAlgebraic ↥(⊥ : Subfield Ω) (algebraMap k' Ω w) := by
    rw [hweq, div_eq_mul_inv]
    exact ((IsOfFinOrder.isIntegral hζ').isAlgebraic.sub isAlgebraic_one).mul
      (((IsOfFinOrder.isIntegral hζ).isAlgebraic.sub
        (IsOfFinOrder.isIntegral hζ').isAlgebraic).inv)
  have hfin : IsOfFinOrder w :=
    (Function.Injective.isOfFinOrder_iff (f := (algebraMap k' Ω).toMonoidHom)
      (algebraMap k' Ω).injective).mp (isOfFinOrder_of_isAlgebraic halg hw0)
  exact (IsOfFinOrder.isIntegral hfin).isAlgebraic

/-- Given one separable element `x` outside the base field, every separable element of `k'` is
algebraic over the prime field: an element that does lie in `k` is moved out of `k` by adding `x`,
and the two conclusions are subtracted. -/
private lemma isAlgebraic_bot_of_isSeparable (p : ℕ) [Fact p.Prime] [CharP k' p]
    (h : ∀ z : k', ∃ n > 0, z ^ n ∈ (algebraMap k k').range)
    {x : k'} (hxsep : IsSeparable k x) (hxnot : x ∉ (algebraMap k k').range)
    {u : k'} (husep : IsSeparable k u) : IsAlgebraic ↥(⊥ : Subfield k') u := by
  have hxalg : IsAlgebraic ↥(⊥ : Subfield k') x :=
    isAlgebraic_bot_of_isSeparable_notMem (AlgebraicClosure k') p h hxsep hxnot
  by_cases hu : u ∈ (algebraMap k k').range
  · obtain ⟨a, ha⟩ := hu
    have h1 : IsSeparable k (u + x) := by
      rw [← mem_separableClosure_iff]
      exact add_mem (ha ▸ (separableClosure k k').algebraMap_mem a)
        (mem_separableClosure_iff.mpr hxsep)
    have h2 : u + x ∉ (algebraMap k k').range := by
      rintro ⟨b, hb⟩
      exact hxnot ⟨b - a, by rw [map_sub]; linear_combination hb - ha⟩
    simpa using
      (isAlgebraic_bot_of_isSeparable_notMem (AlgebraicClosure k') p h h1 h2).sub hxalg
  · exact isAlgebraic_bot_of_isSeparable_notMem (AlgebraicClosure k') p h husep hu

/-- In positive characteristic, one separable element outside the base field makes all of `k'`
algebraic over the prime field: every element of `k'` has a power in the separable closure of `k`,
and every element of that closure is separable over `k`. -/
private lemma isAlgebraic_bot (p : ℕ) [Fact p.Prime] [CharP k' p]
    (h : ∀ z : k', ∃ n > 0, z ^ n ∈ (algebraMap k k').range)
    {x : k'} (hxsep : IsSeparable k x) (hxnot : x ∉ (algebraMap k k').range) :
    Algebra.IsAlgebraic ↥(⊥ : Subfield k') k' := by
  have : Algebra.IsAlgebraic k k' := isAlgebraic_of_forall_exists_pow_mem h
  have : IsPurelyInseparable ↥(separableClosure k k') k' :=
    separableClosure.isPurelyInseparable k k'
  refine ⟨fun z => ?_⟩
  obtain ⟨e, u, hu⟩ := IsPurelyInseparable.pow_mem ↥(separableClosure k k')
    (ringExpChar ↥(separableClosure k k')) z
  have hq : 0 < ringExpChar ↥(separableClosure k k') ^ e :=
    pow_pos (expChar_pos ↥(separableClosure k k') _) e
  exact IsAlgebraic.of_pow hq
    (hu ▸ isAlgebraic_bot_of_isSeparable p h hxsep hxnot (mem_separableClosure_iff.mp u.2))

/-! ### Characteristic zero -/

/-- In characteristic zero the power condition forces the extension to be trivial: a separable
element `x` outside the base field would give infinitely many roots of unity `(r + y) / (x + y)`,
`y ∈ ℤ`, all lying in the number field generated by `ζ` and `ζ'`. -/
private lemma surjective_of_charZero [CharZero k'] (Ω : Type*) [Field Ω] [Algebra k Ω]
    [Algebra k' Ω] [IsScalarTower k k' Ω] [IsAlgClosed Ω]
    (h : ∀ z : k', ∃ n > 0, z ^ n ∈ (algebraMap k k').range) :
    Function.Surjective (algebraMap k k') := by
  have : CharZero k := (algebraMap k k').charZero
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k' Ω).injective
  have : Algebra.IsAlgebraic k k' := isAlgebraic_of_forall_exists_pow_mem h
  intro x
  by_contra hcon
  have hx : x ∉ (algebraMap k k').range := fun ⟨a, ha⟩ => hcon ⟨a, ha⟩
  have hsep : IsSeparable k x :=
    PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral)
  obtain ⟨r, hr, hrne⟩ := exists_ne_aeval_minpoly_eq_zero (Ω := Ω) hsep hx
  obtain ⟨ζ, ζ', hζ, hζ', hζ1, -, hreq, hxeq⟩ :=
    exists_isOfFinOrder_algebraMap_eq_div h hx hr hrne
  have hu : algebraMap k' Ω x ≠ 0 := algebraMap_ne_zero_of_notMem hx
  set L := IntermediateField.adjoin ℚ ({ζ, ζ'} : Set Ω)
  have : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin fun w hw => by
      rcases hw with hw | hw
      · exact hw ▸ IsOfFinOrder.isIntegral hζ
      · simp only [Set.mem_singleton_iff] at hw
        exact hw ▸ IsOfFinOrder.isIntegral hζ'
  have : NumberField L := ⟨⟩
  have hζL : ζ ∈ L := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hζ'L : ζ' ∈ L := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hxL : algebraMap k' Ω x ∈ L := by
    rw [hxeq]
    exact div_mem (sub_mem hζ'L (one_mem _)) (sub_mem hζL hζ'L)
  have hrL : r ∈ L := by rw [hreq]; exact mul_mem hζL hxL
  have hintL : ∀ y : ℤ, ((y : ℤ) : Ω) ∈ L := fun y => by
    rw [← map_intCast (algebraMap ℚ Ω) y]; exact L.algebraMap_mem _
  have hcast : ∀ y : ℤ, algebraMap k Ω ((y : ℤ) : k) = ((y : ℤ) : Ω) :=
    fun y => map_intCast (algebraMap k Ω) y
  have hden : ∀ y : ℤ, algebraMap k' Ω x + ((y : ℤ) : Ω) ≠ 0 := fun y => by
    rw [← hcast y]; exact algebraMap_add_algebraMap_ne_zero hx _
  set f : ℤ → Ω := fun y => (r + (y : Ω)) / (algebraMap k' Ω x + (y : Ω)) with hf
  have hfinj : Function.Injective f := by
    intro y y' hyy'
    simp only [hf, hreq] at hyy'
    exact Int.cast_injective (eq_of_div_add_eq_div_add hu hζ1 (hden y) (hden y') hyy')
  refine Set.infinite_range_of_injective hfinj ((finite_setOf_isOfFinOrder_mem L).subset ?_)
  rintro w ⟨y, rfl⟩
  refine ⟨div_mem (add_mem hrL (hintL y)) (add_mem hxL (hintL y)), ?_⟩
  have h2 := isOfFinOrder_div_add h hx hr ((y : ℤ) : k)
  rwa [hcast y] at h2

/-! ### The equivalence -/

/-- A surjective base-field inclusion is purely inseparable. -/
private lemma isPurelyInseparable_of_surjective_algebraMap
    (hs : Function.Surjective (algebraMap k k')) : IsPurelyInseparable k k' := by
  rw [isPurelyInseparable_iff]
  intro x
  obtain ⟨y, rfl⟩ := hs x
  exact ⟨isIntegral_algebraMap, fun _ => ⟨y, rfl⟩⟩

/-- An algebraic extension which is not purely inseparable has a separable element outside the base
field. -/
private lemma exists_isSeparable_notMem_range [Algebra.IsAlgebraic k k']
    (hPI : ¬ IsPurelyInseparable k k') :
    ∃ x : k', IsSeparable k x ∧ x ∉ (algebraMap k k').range := by
  by_contra hc
  push Not at hc
  exact hPI (isPurelyInseparable_iff.mpr fun x =>
    ⟨(Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral, hc x⟩)

end Conclusion

/-- A field of nonzero characteristic has a prime characteristic. -/
private lemma fact_prime_ringChar {K : Type*} [Field K] (h : ringChar K ≠ 0) :
    Fact (ringChar K).Prime :=
  have : NeZero (ringChar K) := ⟨h⟩
  CharP.char_is_prime_of_pos K (ringChar K)

/-- Let `k'/k` be a field extension. Then every element of `k'` has a positive power lying in `k`
if and only if either `k'/k` is purely inseparable — which in characteristic zero means `k' = k` —
or `k'` has positive characteristic and is algebraic over its prime field `𝐅_p`. -/
@[stacks 0BR7]
public theorem forall_exists_pow_mem_iff_isPurelyInseparable_or_isAlgebraic_bot
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] :
    (∀ x : k', ∃ n > 0, x ^ n ∈ (algebraMap k k').range) ↔
      IsPurelyInseparable k k' ∨
        (ringChar k' ≠ 0 ∧ Algebra.IsAlgebraic (⊥ : Subfield k') k') := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hPI : IsPurelyInseparable k k'
    · exact Or.inl hPI
    have hchar : ringChar k' ≠ 0 := fun h0 => by
      have : CharZero k' := (CharP.charP_zero_iff_charZero k').mp (h0 ▸ ringChar.charP k')
      exact hPI (isPurelyInseparable_of_surjective_algebraMap
        (surjective_of_charZero (AlgebraicClosure k') h))
    have : CharP k' (ringChar k') := ringChar.charP k'
    have := fact_prime_ringChar hchar
    have : Algebra.IsAlgebraic k k' := isAlgebraic_of_forall_exists_pow_mem h
    obtain ⟨x, hxsep, hxnot⟩ := exists_isSeparable_notMem_range hPI
    exact Or.inr ⟨hchar, isAlgebraic_bot (ringChar k') h hxsep hxnot⟩
  · rintro (hPI | ⟨hchar, halg⟩) x
    · obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem k (ringExpChar k) x
      exact ⟨_, pow_pos (expChar_pos k (ringExpChar k)) n, hn⟩
    · rcases eq_or_ne x 0 with rfl | hx0
      · exact ⟨1, one_pos, 0, by simp⟩
      have : CharP k' (ringChar k') := ringChar.charP k'
      have := fact_prime_ringChar hchar
      have : Finite ↥(⊥ : Subfield k') :=
        let := Subfield.fintypeBot k' (ringChar k'); inferInstance
      obtain ⟨N, hN, hNe⟩ :=
        isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_isAlgebraic (halg.isAlgebraic x) hx0)
      exact ⟨N, hN, 1, by rw [map_one, hNe]⟩

end
