module

public import Mathlib.RingTheory.PowerSeries.Expand
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionEulerProduct
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.HeckeRecursion
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.WhittakerRecursion
public import StacksFrontier.NumberTheory.Drinfeld.UnitEigenform

/-!
# The Whittaker coefficients and the Euler product of an eigenform

Let `f` be an eigenform on `GL₂(A)` (Stacks, the notation before Tag 03VT) with `T_v f = t_v f`
and `U_v f = u_v f`, let `ψ` be a nontrivial adelic character, `A(W₀)` the greatest lattice on
which `ψ` is trivial, and `c(D)` the Whittaker coefficients of `f`
(`Stacks.Adeles.GlobalFunctionField.whittakerDiv`). The Hecke recursion
`t_v c(D) = q_v c(D - v) + u_v c(D + v)` (for `D ≤ W₀`) has the explicit solution

`c(W₀ - E) = N(E)⁻¹ ∏_v c_v(E(v)) · c(W₀)` for every effective divisor `E`,

where `c_v = heckeSeq t_v (q_v u_v)` is the sequence with generating series
`(1 - t_v X + q_v u_v X²)⁻¹`. Consequently the Dirichlet series of `f`,
`∑_{E ≥ 0} N(E) c(W₀ - E) X^{deg E}`, is `c(W₀)` times the Euler product

`L(f, X) = ∏_v (1 - t_v X^{deg v} + q_v u_v X^{2 deg v})⁻¹`,

built with `Stacks.EtaleCohomology.EulerSystem`. Its local factor at `v` is the local factor
`det(1 - A X^{deg v})⁻¹` of any `2 × 2` matrix `A` with trace `t_v` and determinant `q_v u_v`
(`Stacks.Adeles.GlobalFunctionField.localEulerFactor_eq_heckeFactor`), as for the geometric
Frobenius `ρ(F_v)` of a representation as in Tags 03VT and 03VU.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.heckeCoeff t u E` — `∏_v q_v^{-E(v)} c_v(E(v))`.
* `Stacks.Adeles.GlobalFunctionField.heckeFactor d t e` — `∑ₙ heckeSeq t e n X^{d n}`.
* `Stacks.Adeles.GlobalFunctionField.heckeEulerSystem k K t e` — the Euler system of the
  factors `heckeFactor (deg v) (t v) (e v)` over the places of `K`.
* `Stacks.Adeles.GlobalFunctionField.eigenLFunction k K t u` — the Euler product
  `∏_v (1 - t_v X^{deg v} + q_v u_v X^{2 deg v})⁻¹`.
* `Stacks.Adeles.GlobalFunctionField.effDivisors k K n` — the effective divisors of degree `n`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.IsEigenform.whittakerDiv_sub_eq` — the closed form
  `c(W₀ - E) = heckeCoeff t u E · c(W₀)`, and `heckeCoeff_eq` —
  `heckeCoeff t u E = N(E)⁻¹ ∏_v c_v(E(v))`.
* `Stacks.Adeles.GlobalFunctionField.heckeFactor_mul` — the local factor identity
  `(1 - t X^d + e X^{2d}) · heckeFactor d t e = 1`.
* `Stacks.Adeles.GlobalFunctionField.coeff_eulerProduct_heckeEulerSystem` — the Euler product
  is the Dirichlet series `∑_{deg E = n} ∏_v c_v(E(v))`.
* `Stacks.Adeles.GlobalFunctionField.coeff_eulerProduct_heckeEulerSystem_twist` — twisting the
  eigenvalues by an unramified character twists the Dirichlet series.
* `Stacks.Adeles.GlobalFunctionField.IsEigenform.mul_coeff_eigenLFunction` —
  `c(W₀) · [Xⁿ] L(f, X) = ∑_{E ≥ 0, deg E = n} N(E) c(W₀ - E)`.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, §6.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open PowerSeries

universe u w

namespace Stacks.Adeles.GlobalFunctionField

/-! ### The normalised local coefficients -/

section Local

variable {Λ : Type*} [Field Λ] {q t u : Λ}

/-- `h(n) = q⁻ⁿ c_n` for the sequence `c = heckeSeq t (q u)`: the normalised coefficient
`c(W₀ - n v) / c(W₀)` of an eigenform along the powers of a place `v`, for `q = q_v`. -/
public def normHeckeSeq (q t u : Λ) (n : ℕ) : Λ := q⁻¹ ^ n * heckeSeq t (q * u) n

/-- The normalised coefficient at `0` is `1`. -/
@[simp]
public theorem normHeckeSeq_zero (q t u : Λ) : normHeckeSeq q t u 0 = 1 := by
  simp [normHeckeSeq]

/-- The initial step `t h(0) = q h(1)` of the recursion of the normalised coefficients. -/
public theorem normHeckeSeq_rec_zero (hq : q ≠ 0) :
    t * normHeckeSeq q t u 0 = q * normHeckeSeq q t u 1 := by
  simp [normHeckeSeq, hq]

/-- The recursion `t h(n+1) = q h(n+2) + u h(n)` of the normalised coefficients. -/
public theorem normHeckeSeq_rec (hq : q ≠ 0) (n : ℕ) :
    t * normHeckeSeq q t u (n + 1) = q * normHeckeSeq q t u (n + 2) + u * normHeckeSeq q t u n := by
  simp only [normHeckeSeq, heckeSeq_add_two, inv_pow]
  field_simp
  ring

end Local

/-! ### The closed form of the Whittaker coefficients -/

section Divisor

variable {K : Type u} [Field K] {Λ : Type w} [Field Λ]

/-- `heckeCoeff t u E = ∏_v q_v^{-E(v)} c_v(E(v))` with `c_v = heckeSeq t_v (q_v u_v)`: the
normalised Whittaker coefficient `c(W₀ - E) / c(W₀)` of an eigenform with eigenvalues `t`, `u`. -/
public def heckeCoeff (t u : Place K → Λ) (E : Place K →₀ ℤ) : Λ :=
  E.prod fun v m => normHeckeSeq (v.residueCard : Λ) (t v) (u v) m.toNat

/-- The normalised Whittaker coefficient of the zero divisor is `1`. -/
@[simp]
public theorem heckeCoeff_zero (t u : Place K → Λ) : heckeCoeff t u 0 = 1 :=
  Finsupp.prod_zero_index

/-- `heckeCoeff t u E` splits off the factor at a place `v` from the product over the other
places. -/
public theorem heckeCoeff_eq_mul (t u : Place K → Λ) (E : Place K →₀ ℤ) (v : Place K) :
    heckeCoeff t u E =
      normHeckeSeq (v.residueCard : Λ) (t v) (u v) (E v).toNat * heckeCoeff t u (E.erase v) :=
  (Finsupp.mul_prod_erase' E v _ fun _ => by simp).symm

/-- `heckeCoeff t u E = N(E)⁻¹ ∏_v c_v(E(v))`, `N(E) = ∏_v q_v^{E(v)}`. -/
public theorem heckeCoeff_eq (t u : Place K → Λ) (E : Place K →₀ ℤ) :
    heckeCoeff t u E = (E.prod fun v m => (v.residueCard : Λ) ^ m.toNat)⁻¹ *
      E.prod fun v m => heckeSeq (t v) (v.residueCard * u v) m.toNat := by
  simp only [heckeCoeff, normHeckeSeq, Finsupp.prod, Finset.prod_mul_distrib, inv_pow,
    Finset.prod_inv_distrib]

/-- The closed form solves the Hecke recursion:
`t_v λ(E) = q_v λ(E + v) + u_v λ(E - v)`, the last term absent if `E(v) = 0`. -/
public theorem heckeCoeff_rec {t u : Place K → Λ} (hq : ∀ v : Place K, (v.residueCard : Λ) ≠ 0)
    {E : Place K →₀ ℤ} (hE : 0 ≤ E) (v : Place K) :
    t v * heckeCoeff t u E = (v.residueCard : Λ) * heckeCoeff t u (E + Finsupp.single v 1) +
      u v * (if 1 ≤ E v then heckeCoeff t u (E - Finsupp.single v 1) else 0) := by
  classical
  have h : ∀ F : Place K →₀ ℤ, (∀ w, w ≠ v → F w = E w) → F.erase v = E.erase v := fun F hF => by
    ext w
    rcases eq_or_ne w v with rfl | hw
    · simp
    · simp [hw, hF w hw]
  have h₁ := h (E + Finsupp.single v 1) fun w hw => by simp [hw]
  have h₂ := h (E - Finsupp.single v 1) fun w hw => by simp [hw]
  rw [heckeCoeff_eq_mul t u E v, heckeCoeff_eq_mul t u (E + Finsupp.single v 1) v, h₁,
    heckeCoeff_eq_mul t u (E - Finsupp.single v 1) v, h₂]
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_eq_same]
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hE v)
  rw [hm]
  rcases m with _ | m
  · rw [ite_eq_right (by omega)]
    have h := normHeckeSeq_rec_zero (t := t v) (u := u v) (hq v)
    simp only [Nat.cast_zero, zero_add, Int.toNat_zero, Int.toNat_one] at h ⊢
    linear_combination heckeCoeff t u (E.erase v) * h
  · rw [ite_eq_left (by omega)]
    have h := normHeckeSeq_rec (t := t v) (u := u v) (hq v) m
    have e1 : ((m + 1 : ℕ) : ℤ).toNat = m + 1 := Int.toNat_natCast _
    have e2 : (((m + 1 : ℕ) : ℤ) + 1).toNat = m + 2 := by omega
    have e3 : (((m + 1 : ℕ) : ℤ) - 1).toNat = m := by omega
    rw [e1, e2, e3]
    linear_combination heckeCoeff t u (E.erase v) * h

end Divisor

section ClosedForm

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [Field Λ]
variable {f : GL (Fin 2) (AdeleRing K) → Λ} {ψ : AddChar (AdeleRing K) Λ} {t u : Place K → Λ}

/-- The residue cardinality of a place is nonzero in a field where `ringChar k` is nonzero. -/
private theorem residueCard_ne_zero [NeZero (ringChar k : Λ)] (v : Place K) :
    (v.residueCard : Λ) ≠ 0 :=
  (isUnit_residueCard k (Ne.isUnit (NeZero.ne (ringChar k : Λ))) v).ne_zero

/-- **The closed form of the Whittaker coefficients of an eigenform.** For every effective
divisor `E`, `c(W₀ - E) = λ(E) · c(W₀)` with `λ(E) = N(E)⁻¹ ∏_v c_v(E(v))`
(`heckeCoeff_eq`), `A(W₀)` the greatest lattice on which `ψ` is trivial. -/
public theorem IsEigenform.whittakerDiv_sub_eq [NeZero (ringChar k : Λ)] (hf : IsEigenform f t u)
    (hψ : IsAdelicChar k K ψ) {W₀ : Place K →₀ ℤ}
    (hW₀ : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀) {E : Place K →₀ ℤ} (hE : 0 ≤ E) :
    whittakerDiv k K ψ f (W₀ - E) = heckeCoeff t u E * whittakerDiv k K ψ f W₀ := by
  classical
  set c₀ := whittakerDiv k K ψ f W₀
  have key := eq_zero_of_hecke_recursion k (W₀ := W₀) (t := t) (u := u)
    (c := fun D => whittakerDiv k K ψ f D - if D ≤ W₀ then heckeCoeff t u (W₀ - D) * c₀ else 0)
    (fun D hD => by
      rw [ite_eq_right hD, sub_zero]
      exact IsUnramifiedCuspForm.whittakerDiv_eq_zero_of_not_le k hf.isUnramifiedCuspForm hψ
        hW₀ hD)
    (fun D hD v => by
      have hr := IsEigenform.whittakerDiv_recursion k hf hψ ((hW₀ D).2 hD) v
      have hc := heckeCoeff_rec (t := t) (u := u) (residueCard_ne_zero k) (sub_nonneg.2 hD) v
      have h1 : D - Finsupp.single v 1 ≤ W₀ :=
        (sub_le_self _ (Finsupp.single_nonneg.2 zero_le_one)).trans hD
      have h2 : W₀ - (D - Finsupp.single v 1) = W₀ - D + Finsupp.single v 1 := by abel
      have h3 : W₀ - (D + Finsupp.single v 1) = W₀ - D - Finsupp.single v 1 := by abel
      have h4 : D + Finsupp.single v 1 ≤ W₀ ↔ 1 ≤ (W₀ - D) v := by
        refine ⟨fun h => ?_, fun h w => ?_⟩
        · have := h v
          simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same] at this ⊢
          omega
        · have := hD w
          by_cases hw : w = v
          · subst hw
            simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same] at h ⊢
            omega
          · simp [Ne.symm hw, this]
      rw [ite_eq_left hD, ite_eq_left h1, h2]
      by_cases h5 : 1 ≤ (W₀ - D) v
      · rw [ite_eq_left (h4.2 h5), h3]
        rw [ite_eq_left h5] at hc
        linear_combination hr - c₀ * hc
      · rw [ite_eq_right (h4.not.2 h5)]
        rw [ite_eq_right h5] at hc
        linear_combination hr - c₀ * hc)
    (by rw [ite_eq_left le_rfl, sub_self, heckeCoeff_zero, one_mul, sub_self])
    (W₀ - E)
  rw [ite_eq_left (sub_le_self _ hE), sub_sub_cancel] at key
  exact sub_eq_zero.1 key

end ClosedForm

/-! ### The local factor -/

section LocalFactor

variable {R : Type*} [CommRing R]

/-- The series `∑ₙ heckeSeq t e n X^{d n}`, the inverse of `1 - t X^d + e X^{2d}`. -/
public def heckeFactor (d : ℕ) (hd : d ≠ 0) (t e : R) : PowerSeries R :=
  expand d hd (mk (heckeSeq t e))

/-- The `j`-th coefficient of `heckeFactor d t e` is `heckeSeq t e (j / d)` if `d ∣ j`, and `0`
otherwise. -/
public theorem coeff_heckeFactor {d : ℕ} (hd : d ≠ 0) (t e : R) (j : ℕ) :
    coeff j (heckeFactor d hd t e) = if d ∣ j then heckeSeq t e (j / d) else 0 := by
  rw [heckeFactor, coeff_expand, coeff_mk]

/-- **The local factor**: `(1 - t X^d + e X^{2d}) · heckeFactor d t e = 1`. -/
public theorem heckeFactor_mul {d : ℕ} (hd : d ≠ 0) (t e : R) :
    (1 - C t * X ^ d + C e * X ^ (2 * d)) * heckeFactor d hd t e = 1 := by
  have h := congrArg (expand d hd) (heckeSeq_mul_eq_one t e)
  rw [map_mul, map_one, map_add, map_sub, map_one, map_mul, map_mul, expand_C, expand_C,
    expand_X, map_pow, expand_X, ← pow_mul, mul_comm d 2] at h
  exact h

/-- `heckeFactor d t e` is congruent to `1` modulo `X^d`. -/
public theorem X_pow_dvd_heckeFactor_sub_one {d : ℕ} (hd : d ≠ 0) (t e : R) :
    (X : PowerSeries R) ^ d ∣ heckeFactor d hd t e - 1 := by
  refine X_pow_dvd_iff.2 fun m hm => ?_
  rw [map_sub, coeff_heckeFactor, coeff_one]
  split_ifs with h1 h2 h2
  · subst h2; simp
  · exact absurd (Nat.eq_zero_of_dvd_of_lt h1 hm) h2
  · subst h2; exact absurd (dvd_zero d) h1
  · simp

/-- The local factor `det(1 - A X^d)` of a `2 × 2` matrix is `1 - tr(A) X^d + det(A) X^{2d}`. -/
public theorem localCharSeries_fin_two (A : Matrix (Fin 2) (Fin 2) R) (d : ℕ) :
    Stacks.EtaleCohomology.localCharSeries A d =
      1 - C A.trace * X ^ d + C A.det * X ^ (2 * d) := by
  simp only [Stacks.EtaleCohomology.localCharSeries, Stacks.EtaleCohomology.localCharMatrix,
    Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, Matrix.one_apply_eq]
  simp only [Matrix.one_apply, Fin.isValue, zero_ne_one, one_ne_zero, ite_false, map_sub, map_mul,
    map_add]
  ring

/-- The local Euler factor `det(1 - A X^d)⁻¹` of a `2 × 2` matrix `A` is
`heckeFactor d (tr A) (det A)`. -/
public theorem localEulerFactor_eq_heckeFactor (A : Matrix (Fin 2) (Fin 2) R) {d : ℕ}
    (hd : d ≠ 0) :
    Stacks.EtaleCohomology.localEulerFactor A d = heckeFactor d hd A.trace A.det := by
  have h1 := Stacks.EtaleCohomology.localCharSeries_mul_localEulerFactor A hd
  have h2 := heckeFactor_mul hd A.trace A.det
  rw [← localCharSeries_fin_two] at h2
  exact left_inv_eq_right_inv (by rw [mul_comm, h1]) h2

end LocalFactor

/-! ### The Euler product -/

section EulerProduct

open Stacks.Drinfeld

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The degree of a place is nonzero. -/
public theorem placeDegree_ne_zero (v : Place K) : placeDegree k K v ≠ 0 := by
  intro h
  have h1 := resCard_eq_pow_placeDegree k v
  rw [h, pow_zero] at h1
  exact (one_lt_resCard k v).ne' h1

/-- There are only finitely many places of degree at most `n`. -/
public theorem finite_setOf_placeDegree_le (n : ℕ) :
    {v : Place K | placeDegree k K v ≤ n}.Finite :=
  (finite_setOf_resCard_le k (Nat.card k ^ n)).subset fun v hv => by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [resCard_eq_pow_placeDegree k v]
    exact Nat.pow_le_pow_right Nat.card_pos hv

variable (K) in
/-- The divisor `v ↦ E(v) deg v` (a divisor on `K` viewed as a multi-index of powers of `X`). -/
public def mulDegree (E : Place K →₀ ℕ) : Place K →₀ ℕ :=
  Finsupp.onFinset E.support (fun v => E v * placeDegree k K v) fun v hv => by
    simp only [ne_eq, mul_eq_zero, not_or] at hv
    exact Finsupp.mem_support_iff.2 hv.1

/-- The value of `mulDegree E` at `v` is `E(v) deg v`. -/
@[simp]
public theorem mulDegree_apply (E : Place K →₀ ℕ) (v : Place K) :
    mulDegree k K E v = E v * placeDegree k K v :=
  Finsupp.onFinset_apply

/-- `E ↦ (v ↦ E(v) deg v)` is injective. -/
public theorem mulDegree_injective : Function.Injective (mulDegree k K) := fun E E' h =>
  Finsupp.ext fun v => Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (placeDegree_ne_zero k v))
    (by simpa using DFunLike.congr_fun h v)

/-- Summed over a set of places containing the support of `E`, `mulDegree E` is the degree
`∑_v E(v) deg v` of `E`. -/
public theorem sum_mulDegree {E : Place K →₀ ℕ} {S : Finset (Place K)} (hS : E.support ⊆ S) :
    ∑ v ∈ S, mulDegree k K E v = Finsupp.weight (placeDegree k K) E := by
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset E hS (fun i c => c • placeDegree k K i)
    (fun _ _ => zero_smul ℕ _)]
  simp

/-- A place in the support of an effective divisor of degree `n` has degree at most `n`. -/
private theorem placeDegree_le_of_weight_eq {E : Place K →₀ ℕ} {n : ℕ}
    (hE : Finsupp.weight (placeDegree k K) E = n) {v : Place K} (hv : v ∈ E.support) :
    placeDegree k K v ≤ n := by
  rw [← hE]
  exact Finsupp.le_weight_of_ne_zero' _ (Finsupp.mem_support_iff.1 hv)

/-- `mulDegree E` of an effective divisor of degree `n` supported in `S` lies in the
antidiagonal of `n` over `S`. -/
private theorem mulDegree_mem_finsuppAntidiag [DecidableEq (Place K)] {E : Place K →₀ ℕ} {n : ℕ}
    {S : Finset (Place K)} (hS : E.support ⊆ S) (hE : Finsupp.weight (placeDegree k K) E = n) :
    mulDegree k K E ∈ Finset.finsuppAntidiag S n :=
  Finset.mem_finsuppAntidiag.2
    ⟨by rw [sum_mulDegree k hS, hE], (Finsupp.support_onFinset_subset).trans hS⟩

/-- There are only finitely many effective divisors of degree `n`. -/
public theorem finite_setOf_weight_eq (n : ℕ) :
    {E : Place K →₀ ℕ | Finsupp.weight (placeDegree k K) E = n}.Finite := by
  classical
  set S := (finite_setOf_placeDegree_le k (K := K) n).toFinset
  refine ((Finset.finsuppAntidiag S n).finite_toSet.preimage
    (mulDegree_injective k).injOn).subset fun E hE => ?_
  exact mulDegree_mem_finsuppAntidiag k (fun v hv => by
    simpa [S] using placeDegree_le_of_weight_eq k hE hv) hE

variable (K) in
/-- The effective divisors of degree `n`, `∑_v E(v) deg v = n`. -/
public def effDivisors (n : ℕ) : Finset (Place K →₀ ℕ) :=
  (finite_setOf_weight_eq k (K := K) n).toFinset

/-- An effective divisor lies in `effDivisors k K n` exactly when its degree is `n`. -/
public theorem mem_effDivisors {n : ℕ} {E : Place K →₀ ℕ} :
    E ∈ effDivisors k K n ↔ Finsupp.weight (placeDegree k K) E = n := by
  simp [effDivisors]

variable {Λ : Type w} [CommRing Λ]

variable (K) in
/-- The Euler system of the local factors `(1 - t_v X^{deg v} + e_v X^{2 deg v})⁻¹` over the
places of `K`. -/
public def heckeEulerSystem (t e : Place K → Λ) :
    Stacks.EtaleCohomology.EulerSystem Λ (Place K) where
  factor v := heckeFactor (placeDegree k K v) (placeDegree_ne_zero k v) (t v) (e v)
  deg v := placeDegree k K v
  dvd_factor_sub_one _ := X_pow_dvd_heckeFactor_sub_one _ _ _
  finite_degLE n := finite_setOf_placeDegree_le k n

/-- **The Euler product is a Dirichlet series over effective divisors**:
`[Xⁿ] ∏_v (1 - t_v X^{deg v} + e_v X^{2 deg v})⁻¹ = ∑_{deg E = n} ∏_v c_v(E(v))`,
`c_v = heckeSeq t_v e_v`. -/
public theorem coeff_eulerProduct_heckeEulerSystem (t e : Place K → Λ) (n : ℕ) :
    coeff n (heckeEulerSystem k K t e).eulerProduct =
      ∑ E ∈ effDivisors k K n, E.prod fun v m => heckeSeq (t v) (e v) m := by
  classical
  set 𝓔 := heckeEulerSystem k K t e
  set S := 𝓔.support n
  have hS : ∀ v, v ∈ S ↔ placeDegree k K v ≤ n := fun v => 𝓔.mem_support
  rw [𝓔.coeff_eulerProduct, Stacks.EtaleCohomology.EulerSystem.partialProduct, coeff_prod]
  set F : (Place K →₀ ℕ) → Λ := fun l => ∏ i ∈ S, coeff (l i) (𝓔.factor i)
  have hsuppE : ∀ E ∈ effDivisors k K n, E.support ⊆ S := fun E hE v hv =>
    (hS v).2 (placeDegree_le_of_weight_eq k ((mem_effDivisors k).1 hE) hv)
  have hmem : ∀ E ∈ effDivisors k K n, mulDegree k K E ∈ Finset.finsuppAntidiag S n :=
    fun E hE => mulDegree_mem_finsuppAntidiag k (hsuppE E hE) ((mem_effDivisors k).1 hE)
  have himage : (effDivisors k K n).image (mulDegree k K) ⊆ Finset.finsuppAntidiag S n :=
    Finset.image_subset_iff.2 hmem
  rw [← Finset.sum_subset himage ?_, Finset.sum_image fun E _ E' _ h => mulDegree_injective k h]
  · refine Finset.sum_congr rfl fun E hE => ?_
    rw [Finsupp.prod_of_support_subset E (hsuppE E hE) _ (fun _ _ => heckeSeq_zero _ _)]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hd := Nat.pos_of_ne_zero (placeDegree_ne_zero k v)
    simp only [𝓔, heckeEulerSystem, coeff_heckeFactor, mulDegree_apply, dvd_mul_left,
      ite_true, Nat.mul_div_cancel _ hd]
  · intro l hl hnot
    by_contra hF
    have hdvd : ∀ v, placeDegree k K v ∣ l v := by
      intro v
      by_cases hv : v ∈ S
      · by_contra hnd
        apply hF
        refine Finset.prod_eq_zero hv ?_
        simp only [𝓔, heckeEulerSystem, coeff_heckeFactor, ite_eq_right hnd]
      · rw [Finsupp.notMem_support_iff.1 fun h => hv ((Finset.mem_finsuppAntidiag.1 hl).2 h)]
        exact dvd_zero _
    set E : Place K →₀ ℕ := Finsupp.onFinset l.support (fun v => l v / placeDegree k K v)
      fun v hv => by
        refine Finsupp.mem_support_iff.2 fun h => hv ?_
        rw [h, Nat.zero_div]
    have hEl : mulDegree k K E = l := Finsupp.ext fun v => by
      simp only [mulDegree_apply, E, Finsupp.onFinset_apply]
      exact Nat.div_mul_cancel (hdvd v)
    apply hnot
    refine Finset.mem_image.2 ⟨E, (mem_effDivisors k).2 ?_, hEl⟩
    have hES : E.support ⊆ S :=
      (Finsupp.support_onFinset_subset).trans (Finset.mem_finsuppAntidiag.1 hl).2
    rw [← sum_mulDegree k hES, hEl, (Finset.mem_finsuppAntidiag.1 hl).1]

/-- **The twisted Euler product**: twisting the eigenvalues by `t_v ↦ χ_v t_v`,
`e_v ↦ χ_v² e_v` (an unramified character with `χ_v = χ(v)`) twists the Dirichlet series by
`χ(E) = ∏_v χ_v^{E(v)}`. -/
public theorem coeff_eulerProduct_heckeEulerSystem_twist (χ t e : Place K → Λ) (n : ℕ) :
    coeff n (heckeEulerSystem k K (fun v => χ v * t v) fun v => χ v ^ 2 * e v).eulerProduct =
      ∑ E ∈ effDivisors k K n,
        (E.prod fun v m => χ v ^ m) * E.prod fun v m => heckeSeq (t v) (e v) m := by
  rw [coeff_eulerProduct_heckeEulerSystem]
  refine Finset.sum_congr rfl fun E _ => ?_
  simp only [heckeSeq_mul_mul, Finsupp.prod_mul]

variable (K) in
/-- **The `L`-function of an eigenform** with eigenvalues `T_v f = t_v f`, `U_v f = u_v f`: the
Euler product `L(f, X) = ∏_v (1 - t_v X^{deg v} + q_v u_v X^{2 deg v})⁻¹`. -/
public def eigenLFunction (t u : Place K → Λ) : PowerSeries Λ :=
  (heckeEulerSystem k K t fun v => v.residueCard * u v).eulerProduct

variable {Λ : Type w} [Field Λ]
variable {f : GL (Fin 2) (AdeleRing K) → Λ} {ψ : AddChar (AdeleRing K) Λ} {t u : Place K → Λ}

/-- **The Dirichlet series of an eigenform is its Euler product**:
`c(W₀) · [Xⁿ] L(f, X) = ∑_{E ≥ 0, deg E = n} N(E) c(W₀ - E)` for the Whittaker coefficients `c`
of `f` with respect to an adelic character `ψ`, `A(W₀)` the greatest lattice on which `ψ` is
trivial and `N(E) = ∏_v q_v^{E(v)}`. -/
public theorem IsEigenform.mul_coeff_eigenLFunction [NeZero (ringChar k : Λ)]
    (hf : IsEigenform f t u) (hψ : IsAdelicChar k K ψ) {W₀ : Place K →₀ ℤ}
    (hW₀ : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W₀) (n : ℕ) :
    whittakerDiv k K ψ f W₀ * coeff n (eigenLFunction k K t u) =
      ∑ E ∈ effDivisors k K n, (E.prod fun v m => (v.residueCard : Λ) ^ m) *
        whittakerDiv k K ψ f (W₀ - Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero E) := by
  classical
  rw [eigenLFunction, coeff_eulerProduct_heckeEulerSystem, Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  set E' := Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero E
  have hE' : 0 ≤ E' := fun v => by simp [E']
  rw [IsEigenform.whittakerDiv_sub_eq k hf hψ hW₀ hE', heckeCoeff_eq,
    Finsupp.prod_mapRange_index (fun _ => by simp),
    Finsupp.prod_mapRange_index (fun _ => by simp)]
  simp only [Int.toNat_natCast]
  have hN : (E.prod fun v m => (v.residueCard : Λ) ^ m) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (residueCard_ne_zero k v)
  field_simp

end EulerProduct

end Stacks.Adeles.GlobalFunctionField

end
