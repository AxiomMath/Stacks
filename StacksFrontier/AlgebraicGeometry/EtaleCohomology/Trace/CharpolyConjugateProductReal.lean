module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A polynomial times its complex conjugate has real coefficients

If the roots along `ι : E →+* ℂ` of a monic `Q` are the complex conjugates of those of a monic `P`
(with multiplicity), then `P * Q` has real coefficients along `ι`: over `ℂ`, `ι Q` is the
coefficientwise conjugate of `ι P`, and `R · R̄` is fixed by conjugation. This is the reality
of `τ ⊕ τ'` for the real partner `τ'` of the Fourier family in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.map_eq_map_conj_of_roots_eq_map_conj`.
* `Stacks.EtaleCohomology.coeff_mul_mem_range_ofReal_of_roots_eq_map_conj`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.EtaleCohomology

/-- **Monic polynomials with conjugate roots are conjugate**: if the roots of `ι Q` are the
conjugates of those of `ι P`, then `ι Q` is the coefficientwise conjugate of `ι P`. -/
public theorem map_eq_map_conj_of_roots_eq_map_conj {E : Type*} [Field E] (ι : E →+* ℂ)
    {P Q : E[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : (Q.map ι).roots = (P.map ι).roots.map (starRingEnd ℂ)) :
    Q.map ι = (P.map ι).map (starRingEnd ℂ) := by
  set R := P.map ι
  calc Q.map ι = ((Q.map ι).roots.map fun a => X - C a).prod :=
        (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hQ.map ι)
          IsAlgClosed.card_roots_eq_natDegree).symm
    _ = ((R.roots.map (starRingEnd ℂ)).map fun a => X - C a).prod := by rw [h]
    _ = (R.roots.map fun a => X - C a).prod.map (starRingEnd ℂ) := by
        rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
        congr 1
        exact Multiset.map_congr rfl fun a _ => by simp
    _ = R.map (starRingEnd ℂ) := by
        rw [prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map ι)
          IsAlgClosed.card_roots_eq_natDegree]

/-- **A polynomial times one with conjugate roots is real**: if `P`, `Q` are monic and the roots
of `ι Q` are the conjugates of those of `ι P` (with multiplicity), every coefficient of `P * Q` is
real along `ι`. -/
public theorem coeff_mul_mem_range_ofReal_of_roots_eq_map_conj {E : Type*} [Field E]
    (ι : E →+* ℂ) {P Q : E[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : (Q.map ι).roots = (P.map ι).roots.map (starRingEnd ℂ)) (m : ℕ) :
    ι ((P * Q).coeff m) ∈ Set.range ((↑) : ℝ → ℂ) := by
  set R := P.map ι
  have hQc := map_eq_map_conj_of_roots_eq_map_conj ι hP hQ h
  have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z
    simp
  have hfix : ∀ S : ℂ[X], (S * S.map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      S * S.map (starRingEnd ℂ) := fun S => by
    rw [Polynomial.map_mul, Polynomial.map_map, hcc, Polynomial.map_id, mul_comm]
  rw [← Polynomial.coeff_map, Polynomial.map_mul, hQc]
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 (by
    rw [← Polynomial.coeff_map, hfix R] : starRingEnd ℂ ((R * R.map (starRingEnd ℂ)).coeff m) =
      (R * R.map (starRingEnd ℂ)).coeff m)
  exact ⟨r, hr.symm⟩

end Stacks.EtaleCohomology

end
