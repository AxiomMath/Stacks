module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The tensor-power trick

Deligne's argument for the local weight bound (Weil II, 1.8; Kedlaya, *Fourier transforms and
`p`-adic Weil II*, Proposition 6.3.2) bounds the eigenvalues of Frobenius on the local
invariants `H⁰_loc(ℱ)` of an `ι`-pure sheaf of weight `w` first only by `w + 2`, through the
weight-drop lemma on `H¹_c`.  Applied to `ℱ^{⊗n}`, which is pure of weight `n w`, the same
argument bounds the eigenvalues on `H⁰_loc(ℱ^{⊗n}) ⊇ H⁰_loc(ℱ)^{⊗n}` by `n w + 2`; as an
eigenvalue `α` on `H⁰_loc(ℱ)` gives the eigenvalue `α ^ n` on the tensor power, `|α| ≤
q ^ ((w + 2 / n) / 2)` for every `n`, that is `|α| ≤ q ^ (w / 2)`.

This module proves that step in linear-algebraic form: a fixed eigenvector `v` of `F` gives the
fixed eigenvector `v ⊗ ⋯ ⊗ v` of `F^{⊗n}` with eigenvalue `α ^ n`, and a bound `C R ^ n` on all
such eigenvalues, for every `n`, bounds `|α|` by `R`.

## Main results

* `Stacks.EtaleCohomology.tprod_const_ne_zero`: `v ⊗ ⋯ ⊗ v ≠ 0` for `v ≠ 0` over a field.
* `Stacks.EtaleCohomology.le_of_forall_pow_le`: `a ^ n ≤ C R ^ n` for all `n > 0` implies
  `a ≤ R`.
* `Stacks.EtaleCohomology.norm_le_of_forall_tensorPower`: the tensor-power trick.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.8.
* K. Kedlaya, *Fourier transforms and `p`-adic Weil II*, Compos. Math. 142 (2006), Prop. 6.3.2.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Filter Topology

namespace Stacks.EtaleCohomology

/-- If `a ^ n ≤ C R ^ n` for every `n > 0`, with `0 ≤ R`, then `a ≤ R`. -/
public theorem le_of_forall_pow_le {a R C : ℝ} (hR : 0 ≤ R)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ C * R ^ n) : a ≤ R := by
  by_contra hlt
  push Not at hlt
  rcases hR.eq_or_lt with rfl | hRpos
  · have := h 1 one_pos
    simp only [pow_one, mul_zero] at this
    linarith
  · have ht := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hRpos).2 hlt)
    obtain ⟨n, hn, hn0⟩ := ((ht.eventually_gt_atTop C).and (eventually_gt_atTop 0)).exists
    rw [div_pow, lt_div_iff₀ (pow_pos hRpos n)] at hn
    linarith [h n hn0]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Over a field, `v ⊗ ⋯ ⊗ v ≠ 0` for `v ≠ 0`. -/
public theorem tprod_const_ne_zero (n : ℕ) {v : V} (hv : v ≠ 0) :
    PiTensorProduct.tprod K (fun _ : Fin n => v) ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv
  intro h0
  have := congrArg (PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra K (Fin n) K).compLinearMap fun _ => φ)) h0
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at this
  simp [hφ] at this

/-- **The tensor-power trick.**  Let `F` and `T` be endomorphisms of `V` (a Frobenius and a
local monodromy), `0 ≤ R`, and suppose that for every `n > 0` every eigenvalue `c` of `F^{⊗n}`
on the vectors of `V^{⊗n}` fixed by `T^{⊗n}` has `|ι c| ≤ C R ^ n`.  Then every eigenvalue `α`
of `F` on the vectors fixed by `T` has `|ι α| ≤ R`. -/
public theorem norm_le_of_forall_tensorPower (ι : K →+* ℂ) {F T : Module.End K V} {C R : ℝ}
    (hR : 0 ≤ R)
    (H : ∀ n : ℕ, 0 < n → ∀ (X : PiTensorProduct K fun _ : Fin n => V) (c : K), X ≠ 0 →
      PiTensorProduct.map (fun _ => T) X = X → PiTensorProduct.map (fun _ => F) X = c • X →
        ‖ι c‖ ≤ C * R ^ n)
    {v : V} {α : K} (hv : v ≠ 0) (hTv : T v = v) (hFv : F v = α • v) : ‖ι α‖ ≤ R := by
  have hX : ∀ (G : Module.End K V) (β : K), G v = β • v → ∀ n : ℕ,
      PiTensorProduct.map (fun _ => G) (PiTensorProduct.tprod K fun _ : Fin n => v) =
        β ^ n • PiTensorProduct.tprod K fun _ : Fin n => v := fun G β hG n => by
    rw [PiTensorProduct.map_tprod]
    simp only [hG]
    rw [MultilinearMap.map_smul_univ (PiTensorProduct.tprod K) (fun _ => β) (fun _ => v),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine le_of_forall_pow_le (C := C) hR fun n hn => ?_
  have := H n hn _ _ (tprod_const_ne_zero n hv)
    (by simpa using hX T 1 (by rw [hTv, one_smul]) n) (hX F α hFv n)
  rwa [map_pow, norm_pow] at this

end Stacks.EtaleCohomology

end
