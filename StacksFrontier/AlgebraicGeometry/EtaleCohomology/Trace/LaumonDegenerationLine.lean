module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# A line through the origin of the plane not contained in a curve

For a nonzero polynomial `D(a, c)` over a finite field `k`, the line `s ↦ (s, λ s)` is not
contained in `D = 0` for some `λ` in a finite extension of `k`: the substitution
`a ↦ s, c ↦ λ s` into `k[λ][s]` is injective (it sends the monomial `aⁱ cʲ` to `λʲ s^{i+j}`), so
some coefficient of `D(s, λ s)` is a nonzero polynomial in `λ`, which does not vanish at some
point of a large enough finite extension.

## Main results

* `Stacks.EtaleCohomology.coeff_coeff_aeval_line`: the coefficient of `λʲ sᵗ` in `D(s, λ s)`.
* `Stacks.EtaleCohomology.exists_aeval_line_ne_zero`: for a nonzero `D` over a finite field there
  is `c` in a finite extension with `D(s, c s) ≠ 0`.

## References

* K. Kedlaya, *Fourier transforms and p-adic Weil II*, §6.4.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.EtaleCohomology

variable {k : Type*} [CommRing k]

/-- **The coefficient of `λʲ sᵗ` in `D(s, λ s)`** (in `k[λ][s]`) is the coefficient of
`a^{t - j} cʲ` in `D`, for `j ≤ t`. -/
public theorem coeff_coeff_aeval_line (D : MvPolynomial (Fin 2) k) {t j : ℕ} (hjt : j ≤ t) :
    ((MvPolynomial.aeval ![(X : (Polynomial k)[X]), C X * X] D).coeff t).coeff j =
      D.coeff (Finsupp.single 0 (t - j) + Finsupp.single 1 j) := by
  induction D using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [MvPolynomial.aeval_monomial, MvPolynomial.coeff_monomial, Finsupp.prod_fintype _ _
      (fun i => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, mul_pow,
      ← C_pow]
    rw [show C (C a) * (X ^ m 0 * (C (X ^ m 1) * X ^ m 1)) =
        C (C a * X ^ m 1) * X ^ (m 0 + m 1) by
      rw [C_mul, pow_add]; ring, coeff_C_mul_X_pow]
    by_cases hm : m = Finsupp.single 0 (t - j) + Finsupp.single 1 j
    · subst hm
      simp [hjt]
    · rw [if_neg hm]
      split_ifs with ht
      · rw [coeff_C_mul_X_pow, if_neg]
        intro hj
        apply hm
        ext i
        fin_cases i <;> simp <;> omega
      · exact coeff_zero j
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, MvPolynomial.coeff_add]

/-- **`D(s, λ s)` is a nonzero polynomial in `λ` and `s`** for `D ≠ 0`. -/
public theorem aeval_line_ne_zero {D : MvPolynomial (Fin 2) k} (hD : D ≠ 0) :
    MvPolynomial.aeval ![(X : (Polynomial k)[X]), C X * X] D ≠ 0 := by
  intro h0
  apply hD
  ext m
  have := coeff_coeff_aeval_line D (Nat.le_add_left (m 1) (m 0))
  rw [h0, coeff_zero, coeff_zero, Nat.add_sub_cancel] at this
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, this]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Evaluating the inner variable `λ` of `D(s, λ s)` at `c` gives `D(s, c s)`. -/
public theorem map_aeval_line {k' : Type*} [CommRing k'] [Algebra k k'] (D : MvPolynomial (Fin 2) k)
    (c : k') :
    (MvPolynomial.aeval ![(X : (Polynomial k)[X]), C X * X] D).map
        (Polynomial.eval₂RingHom (algebraMap k k') c) =
      MvPolynomial.aeval ![(X : Polynomial k'), C c * X] D := by
  induction D using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, Polynomial.map_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.map_mul, hp, map_mul]
    congr 1
    fin_cases i <;> simp

/-- **A line through the origin not contained in `D = 0`**: for a nonzero polynomial `D(a, c)` over
a finite field `k` there are a finite extension `k'` of `k` and `c ∈ k'` with `D(s, c s) ≠ 0` in
`k'[s]`. -/
public theorem exists_aeval_line_ne_zero (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime]
    [CharP k p] {D : MvPolynomial (Fin 2) k} (hD : D ≠ 0) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Finite k') (c : k'),
      MvPolynomial.aeval ![(X : Polynomial k'), C c * X] D ≠ 0 := by
  classical
  set P := MvPolynomial.aeval ![(X : (Polynomial k)[X]), C X * X] D with hP
  have hP0 : P ≠ 0 := aeval_line_ne_zero hD
  set g := P.leadingCoeff
  have hg : g ≠ 0 := leadingCoeff_ne_zero.2 hP0
  set N := g.natDegree + 1
  have : NeZero N := ⟨Nat.succ_ne_zero _⟩
  let φ : FiniteField.Extension k p N →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let k' := φ.fieldRange
  let e : FiniteField.Extension k p N ≃ₐ[k] k'.toSubalgebra :=
    (AlgEquiv.ofInjectiveField φ).trans
      (Subalgebra.equivOfEq _ _ (AlgHom.fieldRange_toSubalgebra φ).symm)
  have hrank : Module.finrank k k' = N :=
    e.toLinearEquiv.finrank_eq.symm.trans (FiniteField.finrank_extension k p N)
  have : Module.Finite k k' := Module.finite_of_finrank_pos (by rw [hrank]; exact Nat.succ_pos _)
  have : Finite k' := Module.finite_of_finite k
  have := Fintype.ofFinite k
  have := Fintype.ofFinite k'
  have hcard : Fintype.card k' = Fintype.card k ^ N := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), hrank]
  have hlt : (g.map (algebraMap k k')).natDegree < Cardinal.mk k' := by
    rw [Cardinal.mk_fintype, natDegree_map, hcard, Nat.cast_lt]
    calc g.natDegree < N := Nat.lt_succ_self _
      _ < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ Fintype.card k ^ N := Nat.pow_le_pow_left Fintype.one_lt_card N
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_of_natDegree_lt_card _
    ((Polynomial.map_ne_zero_iff (algebraMap k k').injective).2 hg) hlt
  refine ⟨k', inferInstance, inferInstance, inferInstance, c, ?_⟩
  rw [← map_aeval_line D c]
  intro h0
  apply hc
  have := congrArg (fun F : Polynomial k' => F.coeff P.natDegree) h0
  simp only [coeff_map, coeff_zero] at this
  rw [eval_map, ← this]
  rfl

end Stacks.EtaleCohomology

end
