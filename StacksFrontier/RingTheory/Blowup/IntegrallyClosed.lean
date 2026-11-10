module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.IntegralClosure.OverIdeal

/-!
# The affine blowup algebra of an ideal whose powers are integrally closed

Let `A` be an integrally closed domain, `I ⊆ A` an ideal and `a ∈ I` nonzero. The affine blowup
algebra `A[I/a]` is the subring `{x / aⁿ | n ≥ 0, x ∈ Iⁿ}` of the fraction field of `A`, which
`StacksFrontier/RingTheory/Blowup/Basic.lean` realizes as `affineBlowup I a`, a subalgebra of
`Localization.Away a`.

This file proves that `A[I/a]` is integrally closed as soon as every power `Iⁿ` is an integrally
closed *ideal*: every element of `A` satisfying a monic equation whose coefficient in degree `j`
lies in `(Iⁿ)^(k-j)` already lies in `Iⁿ`.

Together with `AlgebraicGeometry.isNormal_blowUp_ofIdealTop_iff_isIntegrallyClosed`, which turns
normality of the blowup of an affine scheme into integral closedness of the affine blowup
algebras of its charts, this reduces normality of the blowup of `Spec A` in `I` to a statement
about the ideals `Iⁿ` alone.

## Main definitions

* `Ideal.IsIntegrallyClosed`: every element integral over the ideal (in the sense of the library's
  `IsIntegralOverIdeal`, along the identity) lies in it.

## Main results

* `Ideal.isIntegralOverIdeal_id_iff`: over a nontrivial ring, integrality over `I` is a monic
  equation of positive degree `k` whose coefficient in degree `j` lies in `I ^ (k - j)`.
* `Ideal.isIntegralOverIdeal_id_of_mem`: every element of `I` is integral over `I`, so
  `Ideal.IsIntegrallyClosed` says that the integral closure of `I` is exactly `I` and not that it
  is contained in something larger.
* `IsIntegralOverIdeal.exists_pow_mem`, `Ideal.isIntegrallyClosed_of_isRadical` and
  `Ideal.IsPrime.isIntegrallyClosed`: an element integral over `I` has a positive power in `I`, so
  every radical ideal — in particular every prime ideal, and so by
  `Ideal.isIntegrallyClosed_maximalIdeal` the maximal ideal of a local ring — is integrally closed.
* `Ideal.isIntegrallyClosed_span_singleton` and `Ideal.isIntegrallyClosed_pow_span_singleton`:
  over an integrally closed domain every principal ideal, and hence every power of one, is an
  integrally closed ideal.
* `exists_pow_mul_eq_of_mem_affineBlowup`: an element of `A[I/a]` is a fraction `x / aⁿ` with
  `x ∈ Iⁿ`, written as the multiplicative equation `z · aⁿ = x`.
* `pow_mul_add_sum_eq_zero_of_monic_relation`: the algebraic identity behind the proof. A monic
  relation for `z` with coefficients `b j` becomes a monic relation for `tᴺ z` with coefficients
  `c j · t^(N(m-j))`, where `c j = b j · tᴺ`.
* `exists_algebraMap_eq_of_isIntegral_affineBlowup`: in a fraction field of `A`, an element
  integral over `A[I/a]` lies in `A[I/a]`.
* `isIntegrallyClosed_affineBlowup`: hence `A[I/a]` is an integrally closed ring.
* `add_sum_mul_pow_eq`: that identity, stated as an identity rather than an implication, so that
  it reads in both directions. With `y · tⁿ = X` and `γ j · t^(n(k-j)) = C j`, the degree-`k`
  monic expression in `y` with coefficients `γ j`, times `t^(nk)`, is the degree-`k` monic
  expression in `X` with coefficients `C j`; `mul_pow_eq_zero_of_monic_relation` is the
  consequence that a monic relation over the base divides up to one over a chart.
* `IsIntegralOverIdeal.isIntegral_affineBlowup`: an element of `A` integral over `Iⁿ` has
  `x / aⁿ` integral over `A[I/a]`, on every chart and with no hypothesis on `A`, `I` or `a`;
  `Ideal.isIntegral_affineBlowup_of_mem_pow` is the converse inclusion for elements of `Iⁿ`.
* `Ideal.isIntegrallyClosed_pow_of_isIntegral_affineBlowup`: hence a *single* chart certifies
  that `Iⁿ` is an integrally closed ideal, namely as soon as the elements of `A` whose fraction
  `x / aⁿ` is integral over `A[I/a]` are exactly the elements of `Iⁿ`.
* `affineBlowup_span_singleton_self`: the chart of a principal centre at its own generator is
  the base, `A[(t)/t] = A`, so by
  `Ideal.mem_pow_span_singleton_of_isIntegral_affineBlowup` that criterion is met
  non-degenerately at a principal centre — in particular at the maximal ideal of a discrete
  valuation ring, where it holds for every exponent.

## Implementation notes

The hypothesis on the powers of `I` is used only for the single exponent `N` produced by the
proof, but `N` depends on the element being tested, so all powers are needed.

`Ideal.isIntegralOverIdeal_id_iff` indexes the coefficients by the power of `x` they multiply, so
the condition reads `c j ∈ I ^ (k - j)`; the usual indexing by the codegree is this one reversed.
-/

@[expose] public section

universe u

/-- The polynomial `∑_{j < k} C (c j) · X ^ j` has degree less than `k`. -/
theorem Polynomial.degree_sum_range_C_mul_X_pow_lt {R : Type*} [Semiring R] (c : ℕ → R)
    (k : ℕ) :
    (∑ j ∈ Finset.range k, Polynomial.C (c j) * Polynomial.X ^ j).degree < (k : WithBot ℕ) :=
  lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j hj =>
      lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j (c j))
        (by exact_mod_cast Finset.mem_range.mp hj))

/-- Evaluating a monic polynomial given as `X ^ k + ∑_{j < k} C (c j) * X ^ j` at `z`. -/
private theorem eval₂_X_pow_add_sum_C_mul {R S : Type*} [Semiring R] [CommSemiring S] (f : R →+* S)
    (c : ℕ → R) (k : ℕ) (z : S) :
    (Polynomial.X ^ k + ∑ j ∈ Finset.range k, Polynomial.C (c j) * Polynomial.X ^ j).eval₂ f z
      = z ^ k + ∑ j ∈ Finset.range k, f (c j) * z ^ j := by
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C]

/-- A ring homomorphism carries a monic relation `x ^ k + ∑_{j < k} c j * x ^ j = 0` to one. -/
private theorem map_pow_add_sum_eq_zero {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {k : ℕ} {c : ℕ → R} {x : R} (h : x ^ k + ∑ j ∈ Finset.range k, c j * x ^ j = 0) :
    f x ^ k + ∑ j ∈ Finset.range k, f (c j) * f x ^ j = 0 := by
  simpa only [map_add, map_pow, map_sum, map_mul, map_zero] using congrArg f h

/-- An element satisfying a monic relation `z ^ k + ∑_{j < k} c j · z ^ j = 0` is integral. -/
theorem IsIntegral.of_pow_add_sum_eq_zero {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {k : ℕ} {c : ℕ → R} {z : S}
    (h : z ^ k + ∑ j ∈ Finset.range k, algebraMap R S (c j) * z ^ j = 0) : IsIntegral R z :=
  ⟨Polynomial.X ^ k + ∑ j ∈ Finset.range k, Polynomial.C (c j) * Polynomial.X ^ j,
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_range_C_mul_X_pow_lt c k),
    by rw [eval₂_X_pow_add_sum_C_mul]; exact h⟩

/-- An integral element of a nontrivial algebra satisfies a monic relation
`z ^ k + ∑_{j < k} c j · z ^ j = 0` of positive degree `k`. -/
theorem IsIntegral.exists_pow_add_sum_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Nontrivial S] {z : S} (hz : IsIntegral R z) :
    ∃ (k : ℕ) (c : ℕ → R), 0 < k ∧
      z ^ k + ∑ j ∈ Finset.range k, algebraMap R S (c j) * z ^ j = 0 := by
  obtain ⟨p, hmon, hpz⟩ := hz
  rw [hmon.as_sum] at hpz
  rw [eval₂_X_pow_add_sum_C_mul] at hpz
  refine ⟨p.natDegree, p.coeff, Nat.pos_of_ne_zero fun h0 => ?_, hpz⟩
  simp [h0] at hpz

namespace Ideal

variable {R : Type*} [CommRing R]

/-- **An element integral over an ideal satisfies an explicit monic relation**
`x ^ k + ∑_{j < k} c j · x ^ j = 0` of positive degree `k` whose coefficient in degree `j` lies in
`I ^ (k - j)`: the coefficients of the monic polynomial witnessing `IsIntegralOverIdeal`. -/
theorem _root_.IsIntegralOverIdeal.exists_sum_eq_zero {I : Ideal R} {x : R}
    (hx : IsIntegralOverIdeal (RingHom.id R) I x) :
    ∃ (k : ℕ) (c : ℕ → R), 0 < k ∧ (∀ j < k, c j ∈ I ^ (k - j)) ∧
      x ^ k + ∑ j ∈ Finset.range k, c j * x ^ j = 0 := by
  obtain ⟨p, hmon, hdeg, hcoeff, heval⟩ := hx
  refine ⟨p.natDegree, p.coeff, hdeg, hcoeff, ?_⟩
  rw [hmon.as_sum] at heval
  simpa only [eval₂_X_pow_add_sum_C_mul, RingHom.id_apply] using heval

/-- **Integrality over an ideal, as an explicit monic relation.** Over a nontrivial ring, an
element `x` of `R` is integral over `I` in the sense of `IsIntegralOverIdeal` (along the identity
of `R`) exactly when it satisfies a monic equation `x ^ k + ∑_{j < k} c j · x ^ j = 0` of positive
degree `k` whose coefficient in degree `j` lies in `I ^ (k - j)`. (Over the zero ring every
polynomial has degree `0`, so no element is integral over an ideal in the sense of
`IsIntegralOverIdeal`, while `x - x = 0` is such a relation.) -/
theorem isIntegralOverIdeal_id_iff [Nontrivial R] {I : Ideal R} {x : R} :
    IsIntegralOverIdeal (RingHom.id R) I x ↔
      ∃ (k : ℕ) (c : ℕ → R), 0 < k ∧ (∀ j < k, c j ∈ I ^ (k - j)) ∧
        x ^ k + ∑ j ∈ Finset.range k, c j * x ^ j = 0 := by
  classical
  refine ⟨IsIntegralOverIdeal.exists_sum_eq_zero, ?_⟩
  · rintro ⟨k, c, hk, hc, hrel⟩
    have hlt := Polynomial.degree_sum_range_C_mul_X_pow_lt c k
    have hnat : (Polynomial.X ^ k
        + ∑ j ∈ Finset.range k, Polynomial.C (c j) * Polynomial.X ^ j).natDegree = k := by
      rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
        Polynomial.natDegree_X_pow]
    refine ⟨_, Polynomial.monic_X_pow_add hlt, by rwa [hnat], fun i hi => ?_, ?_⟩
    · rw [hnat] at hi ⊢
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_right hi.ne,
        Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, zero_add,
        Finset.sum_ite_eq, Finset.mem_range, ite_eq_left hi]
      exact hc i hi
    · simpa only [eval₂_X_pow_add_sum_C_mul, RingHom.id_apply] using hrel

/-- **An integrally closed ideal:** every element of `R` integral over `I` (in the sense of
`IsIntegralOverIdeal`, along the identity of `R`) lies in `I`. -/
def IsIntegrallyClosed (I : Ideal R) : Prop :=
  ∀ x : R, IsIntegralOverIdeal (RingHom.id R) I x → x ∈ I

/-- Every element of an ideal is integral over it, by the equation `x - x = 0`. So
`Ideal.IsIntegrallyClosed` says that the set of elements integral over `I` is exactly `I`. -/
theorem isIntegralOverIdeal_id_of_mem [Nontrivial R] {I : Ideal R} {x : R} (hx : x ∈ I) :
    IsIntegralOverIdeal (RingHom.id R) I x := by
  refine isIntegralOverIdeal_id_iff.2 ⟨1, fun _ => -x, Nat.one_pos, fun j hj => ?_, by simp⟩
  obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
  simpa using neg_mem hx

/-- The unit ideal is integrally closed, vacuously. -/
theorem isIntegrallyClosed_top : (⊤ : Ideal R).IsIntegrallyClosed := fun _ _ => Submodule.mem_top

/-- **An element integral over `I` has a positive power in `I`.** The monic relation exhibits
`x ^ k` as minus a combination of the coefficients, and each coefficient lies in `I ^ (k - j)`
with `k - j ≥ 1`, hence in `I`. -/
theorem _root_.IsIntegralOverIdeal.exists_pow_mem {I : Ideal R} {x : R}
    (hx : IsIntegralOverIdeal (RingHom.id R) I x) : ∃ k, 0 < k ∧ x ^ k ∈ I := by
  obtain ⟨k, c, hk, hc, hrel⟩ := hx.exists_sum_eq_zero
  refine ⟨k, hk, ?_⟩
  rw [eq_neg_of_add_eq_zero_left hrel]
  refine neg_mem (Submodule.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_)
  have hjk : j < k := Finset.mem_range.mp hj
  exact Ideal.pow_le_self (by omega) (hc j hjk)

/-- **A radical ideal is integrally closed:** an element integral over it has a power in it. -/
theorem isIntegrallyClosed_of_isRadical {I : Ideal R} (hI : I.IsRadical) :
    I.IsIntegrallyClosed := fun _ hx =>
  let ⟨k, _, hmem⟩ := hx.exists_pow_mem
  hI ⟨k, hmem⟩

/-- **A prime ideal is integrally closed**, being radical. -/
theorem IsPrime.isIntegrallyClosed {I : Ideal R} (hI : I.IsPrime) : I.IsIntegrallyClosed :=
  isIntegrallyClosed_of_isRadical hI.isRadical

/-- **The maximal ideal of a local ring is an integrally closed ideal**, being prime. So the
hypothesis `∀ n, (𝔪 ^ n).IsIntegrallyClosed` is automatic at `n = 0` and `n = 1`, and its content
lies in the exponents `n ≥ 2`. -/
theorem isIntegrallyClosed_maximalIdeal (A : Type*) [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A).IsIntegrallyClosed :=
  (IsLocalRing.maximalIdeal.isMaximal A).isPrime.isIntegrallyClosed

/-- **Integral closedness of an ideal transports along a ring isomorphism**, presented by a pair
of mutually inverse ring homomorphisms. -/
theorem isIntegrallyClosed_map_of_inverse {S : Type*} [CommRing S] (f : R →+* S) (g : S →+* R)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) {I : Ideal R}
    (hI : I.IsIntegrallyClosed) : (I.map f).IsIntegrallyClosed := by
  intro y hy
  obtain ⟨k, c, hk, hc, hrel⟩ := hy.exists_sum_eq_zero
  have hmem : g y ∈ I := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim 0 (g y) ▸ I.zero_mem
    refine hI _ (isIntegralOverIdeal_id_iff.2 ⟨k, fun j => g (c j), hk, fun j hj => ?_, ?_⟩)
    · have h1 : c j ∈ Ideal.map f (I ^ (k - j)) := by rw [Ideal.map_pow]; exact hc j hj
      have h2 : Ideal.map f (I ^ (k - j)) ≤ Ideal.comap g (I ^ (k - j)) :=
        Ideal.map_le_iff_le_comap.2 fun x hx => by
          simpa only [Ideal.mem_comap, hgf] using hx
      exact Ideal.mem_comap.1 (h2 h1)
    · exact map_pow_add_sum_eq_zero g hrel
  simpa only [hfg] using Ideal.mem_map_of_mem f hmem

/-- **A principal ideal of an integrally closed domain is an integrally closed ideal.** Writing
the coefficient of `x ^ j` as `d j · t ^ (k - j)`, the monic relation for `x` over `(t)` becomes,
after division by `t ^ k`, a monic relation over `A` for `y = x / t`; so `y` lies in `A` and `t`
divides `x`. -/
theorem isIntegrallyClosed_span_singleton {A : Type*} [CommRing A] [IsDomain A]
    [_root_.IsIntegrallyClosed A] (t : A) : (Ideal.span {t} : Ideal A).IsIntegrallyClosed := by
  classical
  rcases eq_or_ne t 0 with rfl | ht
  · rw [Ideal.span_singleton_eq_bot.2 rfl]
    exact (inferInstance : (⊥ : Ideal A).IsPrime).isIntegrallyClosed
  intro x hx
  obtain ⟨k, c, hk, hc, hrel⟩ := hx.exists_sum_eq_zero
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  -- write each coefficient as a multiple of the corresponding power of `t`
  have hdex : ∀ j : ℕ, ∃ d : A, j < m + 1 → c j = d * t ^ (m + 1 - j) := by
    intro j
    by_cases hj : j < m + 1
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1
        (by simpa only [Ideal.span_singleton_pow] using hc j hj)
      exact ⟨d, fun _ => hd.symm⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose d hd using hdex
  set K := FractionRing A
  set T : K := algebraMap A K t with hT
  have hTne : T ≠ 0 := fun h =>
    ht (IsFractionRing.injective A K (by simpa only [hT, map_zero] using h))
  set y : K := algebraMap A K x * T⁻¹ with hy
  have hxT : algebraMap A K x = y * T := by
    rw [hy, mul_assoc, inv_mul_cancel₀ hTne, mul_one]
  -- the relation, read in `K` and divided by `T ^ (m + 1)`
  have hmap : (algebraMap A K x) ^ (m + 1)
      + ∑ j ∈ Finset.range (m + 1), algebraMap A K (c j) * (algebraMap A K x) ^ j = 0 :=
    map_pow_add_sum_eq_zero (algebraMap A K) hrel
  have hfac : T ^ (m + 1) * (y ^ (m + 1)
      + ∑ j ∈ Finset.range (m + 1), algebraMap A K (d j) * y ^ j) = 0 := by
    rw [mul_add, Finset.mul_sum, ← hmap]
    congr 1
    · rw [hxT, mul_pow]; ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j < m + 1 := Finset.mem_range.mp hj
      have hsplit : T ^ (m + 1) = T ^ (m + 1 - j) * T ^ j := by
        rw [← pow_add]; congr 1; omega
      rw [hd j hjk, map_mul, map_pow, hxT, mul_pow, hsplit]
      ring
  have hrelK : y ^ (m + 1)
      + ∑ j ∈ Finset.range (m + 1), algebraMap A K (d j) * y ^ j = 0 :=
    (mul_eq_zero.1 hfac).resolve_left (pow_ne_zero _ hTne)
  -- so `y` is integral over `A`, hence lies in `A`
  have hint : IsIntegral A y := .of_pow_add_sum_eq_zero hrelK
  obtain ⟨w, hw⟩ := _root_.IsIntegrallyClosed.isIntegral_iff.mp hint
  refine Ideal.mem_span_singleton'.2 ⟨w, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hw, ← hxT]

/-- **Every power of a principal ideal of an integrally closed domain is an integrally closed
ideal**, a power of a principal ideal being principal. -/
theorem isIntegrallyClosed_pow_span_singleton {A : Type*} [CommRing A] [IsDomain A]
    [_root_.IsIntegrallyClosed A] (t : A) (n : ℕ) :
    ((Ideal.span {t} : Ideal A) ^ n).IsIntegrallyClosed := by
  rw [Ideal.span_singleton_pow]
  exact Ideal.isIntegrallyClosed_span_singleton _

end Ideal

/-- The chart element `x / aⁿ`, presented by its denominator equation in `Localization.Away a`. -/
theorem mk_pow_mul_algebraMap_pow_eq {R : Type*} [CommRing R] (a : R) (n : ℕ) (x : R) :
    (Localization.mk x ⟨a ^ n, n, rfl⟩ : Localization.Away a)
        * (algebraMap R (Localization.Away a) a) ^ n
      = algebraMap R (Localization.Away a) x := by
  rw [Localization.mk_eq_mk', ← map_pow]
  exact IsLocalization.mk'_spec _ _ _

/-- **An element of `R[I/a]` is a fraction `x / aⁿ` with `x ∈ Iⁿ`**, written as the
multiplicative equation `z · aⁿ = x` in the localization. -/
theorem exists_pow_mul_eq_of_mem_affineBlowup {R : Type*} [CommRing R] (I : Ideal R) (a : R)
    (haI : a ∈ I) {z : Localization.Away a} (hz : z ∈ affineBlowup I a) :
    ∃ n : ℕ, ∃ x ∈ I ^ n,
      z * (algebraMap R (Localization.Away a) a) ^ n
        = algebraMap R (Localization.Away a) x := by
  obtain ⟨n, x, hx, rfl⟩ := (affineBlowup_mem_iff I a haI z).1 hz
  exact ⟨n, x, hx, mk_pow_mul_algebraMap_pow_eq a n x⟩

/-- **Finitely many elements of `R[I/a]` have a common denominator:** they are fractions
`d i / aᴺ` with `d i ∈ Iᴺ`, for one exponent `N`. -/
theorem exists_pow_mul_eq_of_forall_mem_affineBlowup {R : Type*} [CommRing R] (I : Ideal R)
    (a : R) (haI : a ∈ I) {ι : Type*} (s : Finset ι) (f : ι → affineBlowup I a) :
    ∃ (N : ℕ) (d : ι → R), (∀ i ∈ s, d i ∈ I ^ N) ∧
      ∀ i ∈ s, (f i : Localization.Away a) * (algebraMap R (Localization.Away a) a) ^ N
        = algebraMap R (Localization.Away a) (d i) := by
  choose n x hx heq using fun i : ι => exists_pow_mul_eq_of_mem_affineBlowup I a haI (f i).2
  refine ⟨s.sup n, fun i => x i * a ^ (s.sup n - n i), fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := Ideal.mul_mem_mul (hx i) (Ideal.pow_mem_pow haI (s.sup n - n i))
    rwa [← pow_add, Nat.add_sub_of_le (Finset.le_sup (f := n) hi)] at h1
  · rw [map_mul, map_pow, ← heq i, mul_assoc, ← pow_add,
      Nat.add_sub_of_le (Finset.le_sup (f := n) hi)]

/-- **Clearing denominators in a monic relation.** If `z` satisfies a monic relation of degree
`m + 1` with coefficients `b j`, and `c j = b j · tᴺ`, then `tᴺ z` satisfies the monic relation
of the same degree with coefficients `c j · t ^ (N (m - j))`. -/
theorem pow_mul_add_sum_eq_zero_of_monic_relation {K : Type*} [CommRing K] {m N : ℕ} {t z : K}
    {b c : ℕ → K} (hbc : ∀ j ∈ Finset.range (m + 1), b j * t ^ N = c j)
    (hz : z ^ (m + 1) + ∑ j ∈ Finset.range (m + 1), b j * z ^ j = 0) :
    (t ^ N * z) ^ (m + 1)
      + ∑ j ∈ Finset.range (m + 1), c j * t ^ (N * (m - j)) * (t ^ N * z) ^ j = 0 := by
  have hterm : ∀ j ∈ Finset.range (m + 1),
      c j * t ^ (N * (m - j)) * (t ^ N * z) ^ j = t ^ (N * (m + 1)) * (b j * z ^ j) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hexp : N + (N * (m - j) + N * j) = N * (m + 1) := by
      have h3 : N * (m - j) + N * j = N * m := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hjm]
      rw [h3]; ring
    rw [← hbc j hj, mul_pow, ← pow_mul, ← hexp]
    ring
  rw [Finset.sum_congr rfl hterm, mul_pow, ← pow_mul, ← Finset.mul_sum, ← mul_add, hz, mul_zero]

section Main

variable {A : Type u} [CommRing A] [IsDomain A] {I : Ideal A} {a : A}

/-- **Every element of a fraction field of `A` integral over `A[I/a]` lies in `A[I/a]`**, when
`A` is an integrally closed domain, `a ∈ I` is nonzero, and every power of `I` is an integrally
closed ideal.

Clearing denominators turns a monic relation for `z` over `A[I/a]` into a monic relation for
`u = aᴺ z` over `A`, whose coefficient in degree `j` lies in `(Iᴺ) ^ (m + 1 - j)`. So `u` lies in
`A` because `A` is integrally closed, and then in `Iᴺ` because `Iᴺ` is an integrally closed
ideal; hence `z = u / aᴺ` lies in `A[I/a]`. -/
theorem exists_algebraMap_eq_of_isIntegral_affineBlowup [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra (Localization.Away a) K] [IsScalarTower A (Localization.Away a) K]
    (haI : a ∈ I) (ha0 : a ≠ 0) (hclosed : ∀ n : ℕ, (I ^ n).IsIntegrallyClosed) {z : K}
    (hz : IsIntegral ↥(affineBlowup I a) z) :
    ∃ w : affineBlowup I a, algebraMap ↥(affineBlowup I a) K w = z := by
  classical
  have ha0' : algebraMap A K a ≠ 0 := fun h =>
    ha0 (IsFractionRing.injective A K (by simpa using h))
  obtain ⟨k, c, hk, hpz⟩ := hz.exists_pow_add_sum_eq_zero
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  -- representatives for the coefficients, over a common denominator `aᴺ`
  obtain ⟨N, dd, hddmem, hddeq⟩ :=
    exists_pow_mul_eq_of_forall_mem_affineBlowup I a haI (Finset.range (m + 1)) c
  -- the same equations in `K`
  have hbc : ∀ j ∈ Finset.range (m + 1),
      algebraMap ↥(affineBlowup I a) K (c j) * (algebraMap A K a) ^ N
        = algebraMap A K (dd j) := by
    intro j hj
    have h := congrArg (algebraMap (Localization.Away a) K) (hddeq j hj)
    rw [map_mul, map_pow] at h
    rw [IsScalarTower.algebraMap_apply A (Localization.Away a) K a,
      IsScalarTower.algebraMap_apply A (Localization.Away a) K (dd j)]
    exact h
  have hrel := pow_mul_add_sum_eq_zero_of_monic_relation hbc hpz
  -- the cleared relation has coefficients in `A`
  have hcoeff : ∀ j ∈ Finset.range (m + 1),
      algebraMap A K (dd j) * (algebraMap A K a) ^ (N * (m - j))
          * ((algebraMap A K a) ^ N * z) ^ j
        = algebraMap A K (dd j * a ^ (N * (m - j))) * ((algebraMap A K a) ^ N * z) ^ j := by
    intro _ _
    rw [map_mul, map_pow]
  rw [Finset.sum_congr rfl hcoeff] at hrel
  -- `u` is integral over `A`, hence lies in `A`
  have hint : IsIntegral A ((algebraMap A K a) ^ N * z) := .of_pow_add_sum_eq_zero hrel
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  -- the relation descends to `A`
  have hwrel : w ^ (m + 1)
      + ∑ j ∈ Finset.range (m + 1), (dd j * a ^ (N * (m - j))) * w ^ j = 0 :=
    IsFractionRing.injective A K (by
      simpa only [map_zero, map_add, map_pow, map_sum, map_mul, hw] using hrel)
  -- so `w` lies in `Iᴺ`
  have hwmem : w ∈ I ^ N := by
    refine hclosed N w (Ideal.isIntegralOverIdeal_id_iff.2
      ⟨m + 1, fun j => dd j * a ^ (N * (m - j)), Nat.succ_pos m, fun j hj => ?_, hwrel⟩)
    rw [show m + 1 - j = 1 + (m - j) by omega, pow_add, pow_one, ← pow_mul]
    exact Ideal.mul_mem_mul (hddmem j (Finset.mem_range.2 hj)) (Ideal.pow_mem_pow haI _)
  -- and `z = w / aᴺ` lies in `A[I/a]`
  refine ⟨⟨Localization.mk w ⟨a ^ N, N, rfl⟩, mk_mem_affineBlowup_of_mem_pow I a hwmem⟩, ?_⟩
  have hK := congrArg (algebraMap (Localization.Away a) K) (mk_pow_mul_algebraMap_pow_eq a N w)
  rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply A (Localization.Away a) K a,
    ← IsScalarTower.algebraMap_apply A (Localization.Away a) K w, hw] at hK
  exact mul_right_cancel₀ (pow_ne_zero N ha0') (hK.trans (mul_comm _ _))

/-- **The affine blowup algebra of an ideal all of whose powers are integrally closed ideals is
an integrally closed ring.** Here `A` is an integrally closed domain and `a ∈ I` is nonzero. -/
theorem isIntegrallyClosed_affineBlowup [IsIntegrallyClosed A] (haI : a ∈ I) (ha0 : a ≠ 0)
    (hclosed : ∀ n : ℕ, (I ^ n).IsIntegrallyClosed) :
    IsIntegrallyClosed ↥(affineBlowup I a) := by
  classical
  have hpow : Submonoid.powers a ≤ nonZeroDivisors A :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero ha0)
  have hunit : ∀ y : Submonoid.powers a,
      IsUnit (algebraMap A (FractionRing A) (y : A)) := fun y =>
    isUnit_iff_ne_zero.2 fun h => (mem_nonZeroDivisors_iff_ne_zero.mp (hpow y.2))
      (IsFractionRing.injective A (FractionRing A) (by simpa using h))
  let : Algebra (Localization.Away a) (FractionRing A) :=
    (IsLocalization.lift (M := Submonoid.powers a)
      (g := algebraMap A (FractionRing A)) hunit).toAlgebra
  have : IsScalarTower A (Localization.Away a) (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  have : IsDomain ↥(affineBlowup I a) := affineBlowup_isDomain I a ha0
  have : IsFractionRing (Localization.Away a) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers a) _ _
  have hfaith : FaithfulSMul ↥(affineBlowup I a) (FractionRing A) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y hxy => ?_
    exact Subtype.ext
      (IsFractionRing.injective (Localization.Away a) (FractionRing A) hxy)
  have : IsFractionRing ↥(affineBlowup I a) (FractionRing A) := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := A) z
    refine ⟨algebraMap A _ x, algebraMap A _ y, ?_⟩
    rw [← IsScalarTower.algebraMap_apply A ↥(affineBlowup I a) (FractionRing A),
      ← IsScalarTower.algebraMap_apply A ↥(affineBlowup I a) (FractionRing A), hxy]
  refine (isIntegrallyClosed_iff (FractionRing A)).2 fun {x} hx => ?_
  exact exists_algebraMap_eq_of_isIntegral_affineBlowup (FractionRing A) haI ha0 hclosed hx

end Main

/-! ### Integral closedness of `Iⁿ` tested on one affine blowup chart

The results above run from the ideals `Iⁿ` to the charts `R[I/a]`. This section runs the other
way. An element `x` of `R` integral over `Iⁿ` has `x / aⁿ` integral over `R[I/a]`, on every
chart and with no hypothesis whatever on `R`, `I` or `a`: the monic relation for `x` over `Iⁿ`
becomes, after division by `a^(nk)`, a monic relation for `x / aⁿ` whose coefficient in degree
`j` is `c j / a^(n(k-j))`, and that fraction lies in `R[I/a]` because `c j` lies in `I^(n(k-j))`.

Consequently `Iⁿ` is integrally closed as soon as a *single* chart separates it: if every `x`
with `x / aⁿ` integral over `R[I/a]` already lies in `Iⁿ`, then `Iⁿ` is an integrally closed
ideal. The hypothesis is sharp, not merely sufficient — by
`Ideal.isIntegral_affineBlowup_of_mem_pow` every element of `Iⁿ` does satisfy it — so it says
exactly that the elements of `R` integral over `R[I/a]` after division by `aⁿ` are the elements
of `Iⁿ`.

Over the normalization of the blowup of `Spec R` in `I` the chart over `Spec R[I/a]` is the
spectrum of the integral closure of `R[I/a]`, so the elements tested by that hypothesis are the
global sections of `𝓘ⁿ` lying in `R`. This is the point at which the identification
`H⁰(X, 𝓘ⁿ) = 𝔪ⁿ` of [Stacks, Tag 0B4Y] bears on [Stacks, Tag 0B4Z]; that identification is
`RationalSingularitySituation.idealSheafGlobalSections_exceptionalIdealPow_unconditional` in the
namespace `AlgebraicGeometry`, and nothing here depends on cohomology.
-/

section Chart

variable {R : Type*} [CommRing R] (I : Ideal R) (a : R)

/-- **The two readings of one monic relation, over a chart and over the base.** If `y · tⁿ = X`
and `γ j · t^(n(k-j)) = C j` for every `j < k`, then the degree-`k` monic expression in `y` with
coefficients `γ j`, multiplied by `t^(nk)`, *is* the degree-`k` monic expression in `X` with
coefficients `C j`.

So either expression vanishes exactly when the other does, up to the factor `t^(nk)`: this is
the identity behind both `pow_mul_add_sum_eq_zero_of_monic_relation`, which clears denominators
from a chart down to the base, and `mul_pow_eq_zero_of_monic_relation`, which divides a relation
over the base up to a chart. -/
theorem add_sum_mul_pow_eq {k n : ℕ} {t y X : R} {γ C : ℕ → R} (hy : y * t ^ n = X)
    (hγ : ∀ j ∈ Finset.range k, γ j * t ^ (n * (k - j)) = C j) :
    (y ^ k + ∑ j ∈ Finset.range k, γ j * y ^ j) * t ^ (n * k)
      = X ^ k + ∑ j ∈ Finset.range k, C j * X ^ j := by
  have hterm : ∀ j ∈ Finset.range k, γ j * y ^ j * t ^ (n * k) = C j * X ^ j := by
    intro j hj
    have hjk : j ≤ k := le_of_lt (Finset.mem_range.mp hj)
    calc γ j * y ^ j * t ^ (n * k)
        = γ j * t ^ (n * (k - j)) * (y ^ j * (t ^ n) ^ j) := by
          rw [show t ^ (n * k) = t ^ (n * (k - j)) * t ^ (n * j) by
            rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hjk], ← pow_mul]
          ring
      _ = C j * X ^ j := by rw [hγ j hj, ← mul_pow, hy]
  have hlead : y ^ k * t ^ (n * k) = X ^ k := by rw [← hy, mul_pow, ← pow_mul]
  rw [add_mul, Finset.sum_mul, Finset.sum_congr rfl hterm, hlead]

/-- **Dividing a monic relation over the base up to a chart.** With `y · tⁿ = X` and
`γ j · t^(n(k-j)) = C j`, a monic relation of degree `k` for `X` with coefficients `C j` makes
the corresponding expression in `y`, with coefficients `γ j`, vanish after multiplication by
`t^(nk)`. -/
theorem mul_pow_eq_zero_of_monic_relation {k n : ℕ} {t y X : R} {γ C : ℕ → R}
    (hy : y * t ^ n = X) (hγ : ∀ j ∈ Finset.range k, γ j * t ^ (n * (k - j)) = C j)
    (hX : X ^ k + ∑ j ∈ Finset.range k, C j * X ^ j = 0) :
    (y ^ k + ∑ j ∈ Finset.range k, γ j * y ^ j) * t ^ (n * k) = 0 :=
  (add_sum_mul_pow_eq hy hγ).trans hX

/-- **An element of `Iⁿ` has `x / aⁿ` in the chart `R[I/a]`**, hence integral over it. Together
with `IsIntegralOverIdeal.isIntegral_affineBlowup` this makes the hypothesis of
`Ideal.isIntegrallyClosed_pow_of_isIntegral_affineBlowup` an exact description of `Iⁿ`. -/
theorem Ideal.isIntegral_affineBlowup_of_mem_pow {n : ℕ} {x : R} (hx : x ∈ I ^ n) :
    IsIntegral ↥(affineBlowup I a)
      (Localization.mk x ⟨a ^ n, n, rfl⟩ : Localization.Away a) :=
  isIntegral_algebraMap (x := (⟨_, mk_mem_affineBlowup_of_mem_pow I a hx⟩ :
    affineBlowup I a))

/-- **An element integral over `Iⁿ` is integral over the chart `R[I/a]` after division by `aⁿ`.**

No hypothesis is placed on `R`, on `I` or on `a`. The monic relation
`x ^ k + ∑ c j · x ^ j = 0` with `c j ∈ (Iⁿ)^(k-j) = I^(n(k-j))` divides by `a^(nk)` to the monic
relation for `x / aⁿ` whose coefficient in degree `j` is `c j / a^(n(k-j))`, and that fraction is
an element of `R[I/a]` by `mk_mem_affineBlowup_of_mem_pow`. The division is legitimate because
`a` is invertible in `Localization.Away a`. -/
theorem IsIntegralOverIdeal.isIntegral_affineBlowup {n : ℕ} {x : R}
    (hx : IsIntegralOverIdeal (RingHom.id R) (I ^ n) x) :
    IsIntegral ↥(affineBlowup I a)
      (Localization.mk x ⟨a ^ n, n, rfl⟩ : Localization.Away a) := by
  classical
  obtain ⟨k, c, hk, hc, hrel⟩ := hx.exists_sum_eq_zero
  set S := Localization.Away a
  set t : S := algebraMap R S a
  set y : S := Localization.mk x ⟨a ^ n, n, rfl⟩
  -- the coefficients of the divided relation, as elements of the chart
  have hcmem : ∀ j : ℕ, j < k →
      (Localization.mk (c j) ⟨a ^ (n * (k - j)), n * (k - j), rfl⟩ : S)
        ∈ affineBlowup I a := by
    refine fun j hj => mk_mem_affineBlowup_of_mem_pow I a ?_
    rw [pow_mul]
    exact hc j hj
  set γ : ℕ → ↥(affineBlowup I a) := fun j =>
    if hj : j < k then ⟨_, hcmem j hj⟩ else 0 with hγdef
  have hγcoe : ∀ j ∈ Finset.range k,
      (γ j : S) * t ^ (n * (k - j)) = algebraMap R S (c j) := by
    intro j hj
    rw [hγdef]
    simp only [dite_eq_left (Finset.mem_range.mp hj)]
    exact mk_pow_mul_algebraMap_pow_eq a (n * (k - j)) (c j)
  -- the relation of `hx`, read in `S`
  have hX : (algebraMap R S x) ^ k
      + ∑ j ∈ Finset.range k, algebraMap R S (c j) * (algebraMap R S x) ^ j = 0 :=
    map_pow_add_sum_eq_zero (algebraMap R S) hrel
  have hzero := mul_pow_eq_zero_of_monic_relation
    (mk_pow_mul_algebraMap_pow_eq a n x) hγcoe hX
  -- `t` is a unit, so the divided relation itself vanishes
  have hunit : IsUnit (t ^ (n * k)) :=
    (IsLocalization.map_units S (⟨a, 1, pow_one a⟩ : Submonoid.powers a)).pow _
  have hrelS : y ^ k + ∑ j ∈ Finset.range k, (γ j : S) * y ^ j = 0 :=
    (hunit.mul_left_eq_zero).mp hzero
  exact IsIntegral.of_pow_add_sum_eq_zero (c := γ) hrelS

/-- **A single affine blowup chart certifies that `Iⁿ` is an integrally closed ideal.** If every
`x` in `R` whose fraction `x / aⁿ` is integral over `R[I/a]` already lies in `Iⁿ`, then `Iⁿ` is
integrally closed.

This is the content of [Stacks, Tag 0B4Z] beyond the two criteria of
`StacksFrontier/AlgebraicGeometry/Surfaces/BlowUpNormality.lean`, transported from the ideals of `R`
to the blowup charts, with no cohomology and no hypothesis on `R`: by
`Ideal.isIntegral_affineBlowup_of_mem_pow` the elements described by the hypothesis always
contain `Iⁿ`, so the hypothesis asks exactly that they do not exceed it. -/
theorem Ideal.isIntegrallyClosed_pow_of_isIntegral_affineBlowup (n : ℕ)
    (hchart : ∀ x : R, IsIntegral ↥(affineBlowup I a)
        (Localization.mk x ⟨a ^ n, n, rfl⟩ : Localization.Away a) → x ∈ I ^ n) :
    (I ^ n).IsIntegrallyClosed :=
  fun _ hx => hchart _ (hx.isIntegral_affineBlowup I a)

/-- **The chart of a principal centre at its own generator is the base:** `R[(t)/t] = R`. Every
element of `(t)ⁿ` is `r · tⁿ`, so every fraction `r · tⁿ / tⁿ` is the image of `r`. -/
theorem affineBlowup_span_singleton_self (t : R) :
    affineBlowup (Ideal.span {t}) t = ⊥ := by
  refine le_antisymm (fun z hz => ?_) bot_le
  obtain ⟨m, y, hy, rfl⟩ :=
    (affineBlowup_mem_iff _ t (Ideal.mem_span_singleton_self t) z).1 hz
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨r, rfl⟩ := hy
  have hu : IsUnit ((algebraMap R (Localization.Away t) t) ^ m) :=
    (IsLocalization.map_units _ (⟨t, 1, pow_one t⟩ : Submonoid.powers t)).pow m
  refine Algebra.mem_bot.2 ⟨r, (hu.mul_right_cancel ?_).symm⟩
  rw [mk_pow_mul_algebraMap_pow_eq, map_mul, map_pow]

/-- **The chart criterion is met, non-degenerately, at a principal centre.** Over an integrally
closed domain and for `t ≠ 0`, an element `x` whose fraction `x / tⁿ` is integral over
`R[(t)/t]` lies in `(t)ⁿ`.

By `affineBlowup_span_singleton_self` the chart is `R` itself, so the hypothesis says that
`x / tⁿ` is integral over `R`; clearing the denominator by `add_sum_mul_pow_eq` turns that into a
monic relation for `x` whose coefficient in degree `j` lies in `((t)ⁿ)^(k-j)`, and
`Ideal.isIntegrallyClosed_pow_span_singleton` concludes. So the hypothesis of
`Ideal.isIntegrallyClosed_pow_of_isIntegral_affineBlowup` is satisfiable at a centre which is
neither the unit ideal nor zero — in particular at the maximal ideal of a discrete valuation
ring, where it holds for every `n`. -/
theorem Ideal.mem_pow_span_singleton_of_isIntegral_affineBlowup {A : Type u} [CommRing A]
    [IsDomain A] [_root_.IsIntegrallyClosed A] {t : A} (ht : t ≠ 0) (n : ℕ) (x : A)
    (hx : IsIntegral ↥(affineBlowup (Ideal.span {t}) t)
      (Localization.mk x ⟨t ^ n, n, rfl⟩ : Localization.Away t)) :
    x ∈ (Ideal.span {t} : Ideal A) ^ n := by
  classical
  have hinj : Function.Injective (algebraMap A (Localization.Away t)) :=
    IsLocalization.injective _ (Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero ht))
  have : Nontrivial (Localization.Away t) := hinj.nontrivial
  obtain ⟨k, c, hk, hpz⟩ := hx.exists_pow_add_sum_eq_zero
  -- the coefficients of the relation lie in the image of `A`, the chart being `A` itself
  have hbot : ∀ j : ℕ, ∃ r : A,
      algebraMap A (Localization.Away t) r
        = algebraMap ↥(affineBlowup (Ideal.span {t}) t) (Localization.Away t) (c j) := by
    refine fun j => Algebra.mem_bot.1 ?_
    rw [← affineBlowup_span_singleton_self t]
    exact (c j).2
  choose r hr using hbot
  -- clearing the denominator `tⁿ` turns the relation for `x / tⁿ` into one for `x`
  have hγ : ∀ j ∈ Finset.range k,
      algebraMap A (Localization.Away t) (r j)
            * (algebraMap A (Localization.Away t) t) ^ (n * (k - j))
        = algebraMap A (Localization.Away t) (r j * t ^ (n * (k - j))) := by
    intro _ _
    rw [map_mul, map_pow]
  have hvanish : (Localization.mk x ⟨t ^ n, n, rfl⟩ : Localization.Away t) ^ k
      + ∑ j ∈ Finset.range k, algebraMap A (Localization.Away t) (r j)
          * (Localization.mk x ⟨t ^ n, n, rfl⟩ : Localization.Away t) ^ j = 0 := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hr j]]
    exact hpz
  have hsum : ∀ j ∈ Finset.range k,
      algebraMap A (Localization.Away t) (r j * t ^ (n * (k - j)) * x ^ j)
        = algebraMap A (Localization.Away t) (r j * t ^ (n * (k - j)))
          * (algebraMap A (Localization.Away t) x) ^ j := by
    intro _ _
    rw [map_mul, map_pow]
  have hrelA : x ^ k + ∑ j ∈ Finset.range k, r j * t ^ (n * (k - j)) * x ^ j = 0 := by
    refine hinj ?_
    rw [map_zero, map_add, map_pow, map_sum, Finset.sum_congr rfl hsum,
      ← add_sum_mul_pow_eq (mk_pow_mul_algebraMap_pow_eq t n x) hγ, hvanish, zero_mul]
  -- so `x` is integral over `(t)ⁿ`, which is an integrally closed ideal
  refine Ideal.isIntegrallyClosed_pow_span_singleton t n x
    (Ideal.isIntegralOverIdeal_id_iff.2
      ⟨k, fun j => r j * t ^ (n * (k - j)), hk, fun j _ => ?_, hrelA⟩)
  rw [← pow_mul, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton'.2 ⟨r j, rfl⟩

end Chart

end
