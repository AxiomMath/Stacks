module

public import StacksFrontier.RingTheory.FormsTrace.AdjoinRootTrace
import StacksCore.Tactic.StacksAttribute

/-!
# The trace on the one-forms `t^i dt` of a monogenic algebra: Stacks, Example 0FLD

Let `A` be a ring, `f = x^d + ∑_{0 ≤ i < d} a_{d - i} x^i ∈ A[x]` and `B = A[x]/(f)`, with `t ∈ B`
the image of `x`. Proposition 0FLC gives the map of de Rham complexes
`Θ_{B/A} : Ω^•_B → Ω^•_A` (`Stacks.FormsTrace.frameTrace`), and Example 0FLD computes its values
on the one-forms `t^i dt`:

* `Θ(dt) = -da₁`,
* `Θ(t dt) = a₁ da₁ - da₂`,
* `Θ(t² dt) = -a₁² da₁ + a₁ da₂ + a₂ da₁ - da₃`,
* if `f = x^d - a`, then `Θ(t^i dt) = 0` for `i = 0, …, d - 2` and `Θ(t^{d-1} dt) = da`.

The computation is the one of the source: it is enough to compute in the universal case, here
the polynomial ring `ℤ[x_c : c ∈ A]` (`Stacks.FormsTrace.UniversalCoefficients`), whose
differentials have no torsion. There `Θ` commutes with `d` and is the trace in degree zero, so
`(i + 1) Θ(t^i dt) = Θ(d(t^{i+1})) = d Trace(t^{i+1})`, and `Trace(t^{i+1})` is the power sum
`∑ αⱼ^{i+1}` of the roots, computed from the coefficients (`Stacks.FormsTrace.trace_root`,
`trace_root_sq`, `trace_root_cube`, `trace_root_pow_X_pow_sub_C`). The general value is then the
pull-back from the universal case (`Stacks.FormsTrace.frameTrace_root_pow_smul_oneForm_D_eq`).

The algebra `B` is any `A`-algebra isomorphic to `A[x]/(f)`, through `e : A[x]/(f) ≃ₐ[A] B`, and
`t = e(x)`; one-forms are read in the first exterior power through
`Stacks.FormsTrace.oneForm`.

## Main results

* `Stacks.FormsTrace.frameTrace_oneForm_D_root`: `Θ(dt) = -da₁`.
* `Stacks.FormsTrace.frameTrace_root_smul_oneForm_D_root`: `Θ(t dt) = a₁ da₁ - da₂`.
* `Stacks.FormsTrace.frameTrace_root_sq_smul_oneForm_D_root`:
  `Θ(t² dt) = -a₁² da₁ + a₁ da₂ + a₂ da₁ - da₃`.
* `Stacks.FormsTrace.frameTrace_root_pow_smul_oneForm_D_root_X_pow_sub_C`: for `f = x^d - a`,
  `Θ(t^i dt) = 0` for `i ≤ d - 2`, and
  `Stacks.FormsTrace.frameTrace_root_pow_pred_smul_oneForm_D_root_X_pow_sub_C`:
  `Θ(t^{d-1} dt) = da`.

## References

* [Stacks Project, Tag 0FLD](https://stacks.math.columbia.edu/tag/0FLD)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open Polynomial KaehlerDifferential

universe u

namespace Stacks.FormsTrace

section Polynomial

variable {A : Type u} [CommRing A]

/-- The polynomial `x^d + ∑_{0 ≤ i < d} a_{d - i} x^i` of Example 0FLD. -/
abbrev monicOfCoefficients (d : ℕ) (a : ℕ → A) : A[X] :=
  Polynomial.X ^ d + ∑ i ∈ Finset.range d, C (a (d - i)) * Polynomial.X ^ i

/-- The polynomial `∑_{0 ≤ i < d} a_{d - i} x^i` has degree less than `d`. -/
theorem degree_sum_coefficients_lt (d : ℕ) (a : ℕ → A) :
    degree (∑ i ∈ Finset.range d, C (a (d - i)) * Polynomial.X ^ i) < d := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => C (a (d - i)) * Polynomial.X ^ i)]
  exact degree_sum_fin_lt _

/-- The polynomial `x^d + ∑_{0 ≤ i < d} a_{d - i} x^i` is monic. -/
theorem monicOfCoefficients_monic (d : ℕ) (a : ℕ → A) : (monicOfCoefficients d a).Monic :=
  monic_X_pow_add (degree_sum_coefficients_lt d a)

/-- Over a nontrivial ring, `x^d + ∑_{0 ≤ i < d} a_{d - i} x^i` has degree `d`. -/
theorem monicOfCoefficients_natDegree [Nontrivial A] (d : ℕ) (a : ℕ → A) :
    (monicOfCoefficients d a).natDegree = d :=
  (natDegree_add_eq_left_of_degree_lt (by
    rw [degree_X_pow]; exact degree_sum_coefficients_lt d a)).trans (natDegree_X_pow _)

/-- The coefficient of `x^m`, `m < d`, of `x^d + ∑ a_{d - i} x^i` is `a_{d - m}`. -/
theorem monicOfCoefficients_coeff (d : ℕ) (a : ℕ → A) {m : ℕ} (hm : m < d) :
    (monicOfCoefficients d a).coeff m = a (d - m) := by
  classical
  simp only [monicOfCoefficients, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [ite_eq_right hm.ne, zero_add, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hm)]

end Polynomial

section Derivation

variable {R : Type u} [CommRing R]

/-- `d` of a numeral vanishes. -/
theorem D_ofNat (n : ℕ) [Nat.AtLeastTwo n] : D ℤ R (OfNat.ofNat n : R) = 0 := by
  rw [← Nat.cast_ofNat]
  exact Derivation.map_natCast _ _

/-- `d(n x) = n dx` for a numeral `n`. -/
theorem D_ofNat_mul (n : ℕ) [Nat.AtLeastTwo n] (x : R) :
    D ℤ R ((OfNat.ofNat n : R) * x) = (OfNat.ofNat n : ℕ) • D ℤ R x := by
  rw [Derivation.leibniz, D_ofNat, smul_zero, add_zero, ← Nat.cast_ofNat, Nat.cast_smul_eq_nsmul]

variable {R₀ : Type u} [CommRing R₀] (φ : R₀ →+* R)

/-- The pull-back of `dx` along `φ : R₀ → R` is `d(φ x)`. -/
theorem map_D_of_ringHom (x : R₀) :
    letI := φ.toAlgebra
    KaehlerDifferential.map ℤ ℤ R₀ R (D ℤ R₀ x) = D ℤ R (φ x) := by
  let := φ.toAlgebra
  exact KaehlerDifferential.map_D ℤ ℤ R₀ R x

/-- The pull-back of `c dx` along `φ : R₀ → R` is `φ(c) d(φ x)`. -/
theorem map_smul_D_of_ringHom (c x : R₀) :
    letI := φ.toAlgebra
    KaehlerDifferential.map ℤ ℤ R₀ R (c • D ℤ R₀ x) = φ c • D ℤ R (φ x) := by
  let := φ.toAlgebra
  rw [map_smul, KaehlerDifferential.map_D, ← algebraMap_smul R c]
  rfl

end Derivation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The universal data of `f`: the evaluation `ℤ[x_c : c ∈ A] → A` carries the universal
polynomial to `f`, and the differentials of `ℤ[x_c]` have no torsion. -/
theorem frameTrace_root_pow_smul_oneForm_D_eq_universal {f : A[X]} (hf : f.Monic)
    (e : AdjoinRoot f ≃ₐ[A] B) (i : ℕ) (w₀ : Ω[UniversalCoefficients A⁄ℤ])
    (hw : (i + 1) • w₀ = D ℤ (UniversalCoefficients A)
      (Algebra.trace (UniversalCoefficients A) (AdjoinRoot (universalPolynomial f))
        (AdjoinRoot.root (universalPolynomial f) ^ (i + 1)))) :
    frameTrace A B 1
        (e (AdjoinRoot.root f) ^ i • oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root f)))) =
      oneForm A Ω[A⁄ℤ] (letI := (UniversalCoefficients.eval A).toAlgebra;
        KaehlerDifferential.map ℤ ℤ (UniversalCoefficients A) A w₀) :=
  frameTrace_root_pow_smul_oneForm_D_eq (UniversalCoefficients.eval A)
    (fun _ hn ω h => UniversalCoefficients.eq_zero_of_natCast_smul hn ω h)
    (universalPolynomial_monic f) (universalPolynomial_map hf) e i w₀ hw

/-- The image of a coefficient of the universal polynomial is the coefficient of `f`. -/
theorem eval_coeff_universalPolynomial {f : A[X]} (hf : f.Monic) (m : ℕ) :
    UniversalCoefficients.eval A ((universalPolynomial f).coeff m) = f.coeff m := by
  rw [← coeff_map, universalPolynomial_map hf]

section Example

variable {d : ℕ} (a : ℕ → A)

/-- The image of the `m`-th coefficient of the universal polynomial of `x^d + ∑ a_{d - i} x^i`
is `a_{d - m}`. -/
private theorem eval_coeff_universalPolynomial_monicOfCoefficients {m : ℕ} (hm : m < d) :
    UniversalCoefficients.eval A ((universalPolynomial (monicOfCoefficients d a)).coeff m) =
      a (d - m) := by
  rw [eval_coeff_universalPolynomial (monicOfCoefficients_monic d a),
    monicOfCoefficients_coeff _ _ hm]

/-- `Θ(t^i dt)` for `x^d + ∑ a_{d - i} x^i` from the universal case; the trivial ring is
handled here, and `hw` may assume that the universal polynomial has degree `d`. -/
private theorem frameTrace_root_pow_smul_oneForm_D_eq_monicOfCoefficients
    (e : AdjoinRoot (monicOfCoefficients d a) ≃ₐ[A] B) (i : ℕ) (w₀ : Ω[UniversalCoefficients A⁄ℤ])
    (hw : (universalPolynomial (monicOfCoefficients d a)).natDegree = d →
      (i + 1) • w₀ = D ℤ (UniversalCoefficients A)
        (Algebra.trace (UniversalCoefficients A)
          (AdjoinRoot (universalPolynomial (monicOfCoefficients d a)))
          (AdjoinRoot.root (universalPolynomial (monicOfCoefficients d a)) ^ (i + 1)))) :
    frameTrace A B 1 (e (AdjoinRoot.root (monicOfCoefficients d a)) ^ i •
        oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root (monicOfCoefficients d a))))) =
      oneForm A Ω[A⁄ℤ] (letI := (UniversalCoefficients.eval A).toAlgebra;
        KaehlerDifferential.map ℤ ℤ (UniversalCoefficients A) A w₀) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := subsingleton_forms A 1
    exact Subsingleton.elim _ _
  exact frameTrace_root_pow_smul_oneForm_D_eq_universal (monicOfCoefficients_monic d a) e i w₀
    (hw (by rw [universalPolynomial_natDegree, monicOfCoefficients_natDegree]))

/-- **Stacks, Example 0FLD: `Θ(dt) = -da₁`.** Let `f = x^d + ∑_{0 ≤ i < d} a_{d - i} x^i` with
`d ≥ 1`, let `B ≅ A[x]/(f)` and let `t ∈ B` be the image of `x`. Then the trace map
`Θ_{B/A} : Ω^•_B → Ω^•_A` of Proposition 0FLC sends `dt` to `-da₁`. -/
@[stacks 0FLD "`Θ(dt) = -da₁`"]
theorem frameTrace_oneForm_D_root (hd : 1 ≤ d)
    (e : AdjoinRoot (monicOfCoefficients d a) ≃ₐ[A] B) :
    frameTrace A B 1
        (oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root (monicOfCoefficients d a))))) =
      oneForm A Ω[A⁄ℤ] (-D ℤ A (a 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have h := frameTrace_root_pow_smul_oneForm_D_eq_monicOfCoefficients a e 0
    (-D ℤ (UniversalCoefficients A)
      ((universalPolynomial (monicOfCoefficients (n + 1) a)).coeff n)) (fun hdeg => by
      rw [zero_add, one_smul, pow_one, trace_root (universalPolynomial_monic _) hdeg, map_neg])
  rw [pow_zero, one_smul] at h
  rw [h, map_neg, map_D]
  change oneForm A Ω[A⁄ℤ] (-D ℤ A (UniversalCoefficients.eval A _)) = _
  rw [eval_coeff_universalPolynomial_monicOfCoefficients a (by omega),
    show n + 1 - n = 1 by omega]

/-- **Stacks, Example 0FLD: `Θ(t dt) = a₁ da₁ - da₂`.** Let `f = x^d + ∑_{0 ≤ i < d} a_{d - i} x^i`
with `d ≥ 2`, let `B ≅ A[x]/(f)` and let `t ∈ B` be the image of `x`. Then the trace map
`Θ_{B/A}` of Proposition 0FLC sends `t dt` to `a₁ da₁ - da₂`. -/
@[stacks 0FLD "`Θ(t dt) = a₁ da₁ - da₂`"]
theorem frameTrace_root_smul_oneForm_D_root (hd : 2 ≤ d)
    (e : AdjoinRoot (monicOfCoefficients d a) ≃ₐ[A] B) :
    frameTrace A B 1 (e (AdjoinRoot.root (monicOfCoefficients d a)) •
        oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root (monicOfCoefficients d a))))) =
      oneForm A Ω[A⁄ℤ] (a 1 • D ℤ A (a 1) - D ℤ A (a 2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  set c₁ := (universalPolynomial (monicOfCoefficients (n + 2) a)).coeff (n + 1)
  set c₂ := (universalPolynomial (monicOfCoefficients (n + 2) a)).coeff n
  have h := frameTrace_root_pow_smul_oneForm_D_eq_monicOfCoefficients a e 1
    (c₁ • D ℤ (UniversalCoefficients A) c₁ - D ℤ (UniversalCoefficients A) c₂) (fun hdeg => by
      rw [show 1 + 1 = 2 from rfl, trace_root_sq (universalPolynomial_monic _) hdeg, map_sub,
        Derivation.leibniz_pow, D_ofNat_mul]
      module)
  rw [pow_one] at h
  rw [h, map_sub, map_smul_D_of_ringHom, map_D_of_ringHom,
    eval_coeff_universalPolynomial_monicOfCoefficients a (by omega),
    eval_coeff_universalPolynomial_monicOfCoefficients a (by omega),
    show n + 2 - (n + 1) = 1 by omega, show n + 2 - n = 2 by omega]

/-- **Stacks, Example 0FLD: `Θ(t² dt) = -a₁² da₁ + a₁ da₂ + a₂ da₁ - da₃`.** Let
`f = x^d + ∑_{0 ≤ i < d} a_{d - i} x^i` with `d ≥ 3`, let `B ≅ A[x]/(f)` and let `t ∈ B` be the
image of `x`. Then the trace map `Θ_{B/A}` of Proposition 0FLC sends `t² dt` to
`-a₁² da₁ + a₁ da₂ + a₂ da₁ - da₃` (and the source's "modulo calculation error" is not needed). -/
@[stacks 0FLD "`Θ(t² dt) = -a₁² da₁ + a₁ da₂ + a₂ da₁ - da₃`"]
theorem frameTrace_root_sq_smul_oneForm_D_root (hd : 3 ≤ d)
    (e : AdjoinRoot (monicOfCoefficients d a) ≃ₐ[A] B) :
    frameTrace A B 1 (e (AdjoinRoot.root (monicOfCoefficients d a)) ^ 2 •
        oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root (monicOfCoefficients d a))))) =
      oneForm A Ω[A⁄ℤ] (-(a 1 ^ 2 • D ℤ A (a 1)) + a 1 • D ℤ A (a 2) + a 2 • D ℤ A (a 1) -
        D ℤ A (a 3)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  set c₁ := (universalPolynomial (monicOfCoefficients (n + 3) a)).coeff (n + 2)
  set c₂ := (universalPolynomial (monicOfCoefficients (n + 3) a)).coeff (n + 1)
  set c₃ := (universalPolynomial (monicOfCoefficients (n + 3) a)).coeff n
  have h := frameTrace_root_pow_smul_oneForm_D_eq_monicOfCoefficients a e 2
    (-(c₁ ^ 2 • D ℤ (UniversalCoefficients A) c₁) + c₁ • D ℤ (UniversalCoefficients A) c₂ +
      c₂ • D ℤ (UniversalCoefficients A) c₁ - D ℤ (UniversalCoefficients A) c₃) (fun hdeg => by
      rw [show 2 + 1 = 3 from rfl, trace_root_cube (universalPolynomial_monic _) hdeg, map_sub,
        map_add, map_neg, Derivation.leibniz_pow, mul_assoc, D_ofNat_mul, D_ofNat_mul,
        Derivation.leibniz]
      module)
  rw [h, map_sub, map_add, map_add, map_neg, map_smul_D_of_ringHom, map_smul_D_of_ringHom,
    map_smul_D_of_ringHom, map_D_of_ringHom, map_pow]
  rw [eval_coeff_universalPolynomial_monicOfCoefficients a (by omega),
    eval_coeff_universalPolynomial_monicOfCoefficients a (by omega),
    eval_coeff_universalPolynomial_monicOfCoefficients a (by omega),
    show n + 3 - (n + 2) = 1 by omega, show n + 3 - (n + 1) = 2 by omega,
    show n + 3 - n = 3 by omega]

end Example

section PurePower

variable {d : ℕ} (hd : 0 < d) (a : A)

/-- The universal pure power `x^d - x_a` over `ℤ[x_c : c ∈ A]`. -/
abbrev universalPurePower (d : ℕ) (a : A) : (UniversalCoefficients A)[X] :=
  Polynomial.X ^ d - C (UniversalCoefficients.var a)

/-- The evaluation `ℤ[x_c : c ∈ A] → A` carries `x^d - x_a` to `x^d - a`. -/
theorem universalPurePower_map :
    (universalPurePower d a).map (UniversalCoefficients.eval A) = Polynomial.X ^ d - C a := by
  simp [universalPurePower]

include hd in
/-- **`Θ(t^i dt)` for `x^d - a` from the universal case**: if `w₀` satisfies
`(i + 1) w₀ = d Trace(t₀^{i+1})` for `ℤ[x_c][x]/(x^d - x_a)`, then `Θ(t^i dt)` is its image. -/
theorem frameTrace_root_pow_smul_oneForm_D_X_pow_sub_C_eq
    (e : AdjoinRoot (Polynomial.X ^ d - C a) ≃ₐ[A] B)
    (i : ℕ) (w₀ : Ω[UniversalCoefficients A⁄ℤ])
    (hw : (i + 1) • w₀ = D ℤ (UniversalCoefficients A)
      (Algebra.trace (UniversalCoefficients A) (AdjoinRoot (universalPurePower d a))
        (AdjoinRoot.root (universalPurePower d a) ^ (i + 1)))) :
    frameTrace A B 1 (e (AdjoinRoot.root (Polynomial.X ^ d - C a)) ^ i •
        oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root (Polynomial.X ^ d - C a))))) =
      oneForm A Ω[A⁄ℤ] (letI := (UniversalCoefficients.eval A).toAlgebra;
        KaehlerDifferential.map ℤ ℤ (UniversalCoefficients A) A w₀) :=
  frameTrace_root_pow_smul_oneForm_D_eq (UniversalCoefficients.eval A)
    (fun _ hn ω h => UniversalCoefficients.eq_zero_of_natCast_smul hn ω h)
    (monic_X_pow_sub_C_of_pos hd _) (universalPurePower_map a) e i w₀ hw

include hd in
/-- **Stacks, Example 0FLD: for `f = x^d - a`, `Θ(t^i dt) = 0` for `i = 0, …, d - 2`.** Let
`B ≅ A[x]/(x^d - a)` with `d ≥ 1` and let `t ∈ B` be the image of `x`. Then the trace map
`Θ_{B/A}` of Proposition 0FLC kills `t^i dt` for `i + 1 < d`. -/
@[stacks 0FLD "for `f = x^d - a`: `Θ(t^i dt) = 0` for `i = 0, …, d - 2`"]
theorem frameTrace_root_pow_smul_oneForm_D_root_X_pow_sub_C
    (e : AdjoinRoot (Polynomial.X ^ d - C a) ≃ₐ[A] B) {i : ℕ} (hi : i + 1 < d) :
    frameTrace A B 1 (e (AdjoinRoot.root (Polynomial.X ^ d - C a)) ^ i •
        oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root (Polynomial.X ^ d - C a))))) = 0 := by
  rw [frameTrace_root_pow_smul_oneForm_D_X_pow_sub_C_eq hd a e i 0 (by
    rw [trace_root_pow_X_pow_sub_C hd _ (Nat.succ_pos i) hi.le, ite_eq_right hi.ne, map_zero,
      smul_zero]), map_zero, map_zero]

include hd in
/-- **Stacks, Example 0FLD: for `f = x^d - a`, `Θ(t^{d-1} dt) = da`.** Let `B ≅ A[x]/(x^d - a)`
with `d ≥ 1` and let `t ∈ B` be the image of `x`. Then the trace map `Θ_{B/A}` of
Proposition 0FLC sends `t^{d-1} dt` to `da`. -/
@[stacks 0FLD "for `f = x^d - a`: `Θ(t^{d-1} dt) = da`"]
theorem frameTrace_root_pow_pred_smul_oneForm_D_root_X_pow_sub_C
    (e : AdjoinRoot (Polynomial.X ^ d - C a) ≃ₐ[A] B) :
    frameTrace A B 1 (e (AdjoinRoot.root (Polynomial.X ^ d - C a)) ^ (d - 1) •
        oneForm B Ω[B⁄ℤ] (D ℤ B (e (AdjoinRoot.root (Polynomial.X ^ d - C a))))) =
      oneForm A Ω[A⁄ℤ] (D ℤ A a) := by
  rw [frameTrace_root_pow_smul_oneForm_D_X_pow_sub_C_eq hd a e (d - 1)
    (D ℤ (UniversalCoefficients A) (UniversalCoefficients.var a)) (by
      rw [Nat.sub_add_cancel hd, trace_root_pow_X_pow_sub_C hd _ hd le_rfl, ite_eq_left rfl,
        Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, Nat.cast_smul_eq_nsmul]),
    map_D]
  change oneForm A Ω[A⁄ℤ] (D ℤ A (UniversalCoefficients.eval A (UniversalCoefficients.var a))) = _
  rw [UniversalCoefficients.eval_var]

end PurePower

end Stacks.FormsTrace

end
