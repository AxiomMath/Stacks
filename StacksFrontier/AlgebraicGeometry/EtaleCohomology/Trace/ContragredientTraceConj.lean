module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions

/-!
# Traces of the contragredient of a pure matrix

Let `A` be an invertible square matrix over a field `E` and `ι : E →+* ℂ`. The complex roots of
the characteristic polynomial of `A⁻¹` are the inverses of those of `A`
(`Stacks.EtaleCohomology.roots_map_charpoly_inv`), so
`ι Tr(A⁻ʳ) = ∑ α⁻ʳ` over the roots `α` of `A`. If every such root has `|α|² = Q`, then
`α⁻¹ = ᾱ / Q`, and the traces of the powers of the contragredient `(A⁻¹)ᵀ` are
`Q⁻ʳ · conj(ι Tr(Aʳ))` (`Stacks.EtaleCohomology.map_trace_inv_transpose_pow_of_norm_sq`). This is
the pointwise input of the comparison of a lisse sheaf `ι`-pure of weight `β` with its dual in the
trace formula ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier
transforms and p-adic Weil II*, proof of Theorem 6.4).

## Main results

* `Stacks.EtaleCohomology.roots_reverse_of_coeff_zero_ne_zero`.
* `Stacks.EtaleCohomology.roots_map_charpoly_inv`.
* `Stacks.EtaleCohomology.map_trace_inv_pow`.
* `Stacks.EtaleCohomology.map_trace_inv_transpose_pow_of_norm_sq`.
-/

@[expose] public noncomputable section

open Polynomial
open scoped Matrix

namespace Stacks.EtaleCohomology

/-- The reverse of `X - α` is `-α · (X - α⁻¹)` for `α ≠ 0`. -/
theorem reverse_X_sub_C_eq {α : ℂ} (hα : α ≠ 0) :
    (Polynomial.X - C α).reverse = C (-α) * (Polynomial.X - C α⁻¹) := by
  have h1 : reflect 1 (Polynomial.X : Polynomial ℂ) = 1 := by
    simp
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_C, h1, mul_sub, ← C_mul, neg_mul,
    mul_inv_cancel₀ hα, C_neg, C_neg, C_1, pow_one]
  ring

/-- **The roots of the reverse of a complex polynomial with nonzero constant term are the inverses
of its roots**, with multiplicity. -/
public theorem roots_reverse_of_coeff_zero_ne_zero {p : Polynomial ℂ} (h : p.coeff 0 ≠ 0) :
    p.reverse.roots = p.roots.map (·⁻¹) := by
  have hp := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := p))
  have h0 : ∀ α ∈ p.roots, α ≠ 0 := fun α hα hα0 => by
    subst hα0
    rw [mem_roots', IsRoot.def, ← coeff_zero_eq_eval_zero] at hα
    exact h hα.2
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 fun h' => by simp [h'] at h
  have key : ∀ s : Multiset ℂ, (∀ α ∈ s, α ≠ 0) →
      ((s.map fun a => Polynomial.X - C a).prod).reverse =
        C (s.map fun a => -a).prod * (s.map fun a => Polynomial.X - C a⁻¹).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simpa using reverse_C (1 : ℂ)
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain,
        reverse_X_sub_C_eq (hs a (Multiset.mem_cons_self a s)),
        ih fun b hb => hs b (Multiset.mem_cons_of_mem hb), Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_cons, Multiset.prod_cons, C_mul]
      ring
  conv_lhs => rw [← hp]
  rw [reverse_mul_of_domain, reverse_C, key _ h0, ← mul_assoc, ← C_mul,
    roots_C_mul _ (mul_ne_zero hlc (Multiset.prod_ne_zero fun h' => by
      obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 h'
      exact h0 a ha (neg_eq_zero.1 ha0)))]
  have hm : (p.roots.map fun a => Polynomial.X - C a⁻¹) =
      ((p.roots.map (·⁻¹)).map fun a => Polynomial.X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [hm, roots_multiset_prod_X_sub_C]

variable {E : Type*} [Field E] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The complex roots of the characteristic polynomial of `A⁻¹` are the inverses of those of
`A`**, with multiplicity, along any `ι : E →+* ℂ`. -/
public theorem roots_map_charpoly_inv (ι : E →+* ℂ) {A : Matrix n n E} (hA : IsUnit A) :
    (A⁻¹.charpoly.map ι).roots = (A.charpoly.map ι).roots.map (·⁻¹) := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h0 : (A.charpoly.map ι).coeff 0 ≠ 0 := by
    rw [coeff_map]
    refine (map_ne_zero ι).2 fun h => hdet.ne_zero ?_
    rw [Matrix.det_eq_sign_charpoly_coeff, h, mul_zero]
  have hdeg : (A.charpoly.map ι).natDegree = A.charpoly.natDegree :=
    natDegree_map ι
  have hrev : Polynomial.map ι A.charpoly.reverse = (A.charpoly.map ι).reverse := by
    rw [reverse, reverse, hdeg, reflect_map]
  have hc : ((-1) ^ Fintype.card n * ι (Ring.inverse A.det)) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ((map_ne_zero ι).2 ?_)
    rw [Ring.inverse_of_isUnit hdet]
    exact (hdet.unit⁻¹).ne_zero
  rw [Matrix.charpoly_inv A hA, ← Matrix.reverse_charpoly, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_C, hrev,
    show ((-1 : Polynomial ℂ)) ^ Fintype.card n * C (ι (Ring.inverse A.det)) =
      C ((-1) ^ Fintype.card n * ι (Ring.inverse A.det)) by rw [C_mul, C_pow, C_neg, C_1],
    roots_C_mul _ hc, roots_reverse_of_coeff_zero_ne_zero h0]

/-- **Traces of the powers of `A⁻¹` along `ι`**: `ι Tr(A⁻ʳ) = ∑ α⁻ʳ` over the complex roots `α` of
the characteristic polynomial of `A`. -/
public theorem map_trace_inv_pow (ι : E →+* ℂ) {m : ℕ} {A : Matrix (Fin m) (Fin m) E}
    (hA : IsUnit A) (r : ℕ) :
    ι ((A⁻¹ ^ r).trace) = ((A.charpoly.map ι).roots.map fun α => α⁻¹ ^ r).sum := by
  rw [map_trace_pow_eq_sum_roots ι A⁻¹ r, roots_map_charpoly_inv ι hA, Multiset.map_map]
  rfl

/-- **Traces of the contragredient of a pure matrix**: if every complex root `α` of the
characteristic polynomial of `A` along `ι` has `|α|² = Q`, then
`ι Tr(((A⁻¹)ᵀ)ʳ) = Q⁻ʳ · conj(ι Tr(Aʳ))`. -/
public theorem map_trace_inv_transpose_pow_of_norm_sq (ι : E →+* ℂ) {m : ℕ}
    {A : Matrix (Fin m) (Fin m) E} (hA : IsUnit A) {Q : ℝ}
    (hQ : ∀ α : ℂ, (A.charpoly.map ι).IsRoot α → ‖α‖ ^ 2 = Q) (r : ℕ) :
    ι (((A⁻¹)ᵀ ^ r).trace) = ((Q : ℂ) ^ r)⁻¹ * starRingEnd ℂ (ι ((A ^ r).trace)) := by
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, map_trace_inv_pow ι hA,
    map_trace_pow_eq_sum_roots ι A r, map_multiset_sum, Multiset.map_map,
    ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun α hα => ?_
  have hroot : (A.charpoly.map ι).IsRoot α :=
    (mem_roots ((Matrix.charpoly_monic A).map ι).ne_zero).1 hα
  have hn : Complex.normSq α = Q := by
    rw [Complex.normSq_eq_norm_sq]
    exact hQ α hroot
  simp only [Function.comp_apply, map_pow]
  rw [Complex.inv_def, hn, mul_pow, Complex.ofReal_inv, inv_pow, mul_comm]

end Stacks.EtaleCohomology

end
