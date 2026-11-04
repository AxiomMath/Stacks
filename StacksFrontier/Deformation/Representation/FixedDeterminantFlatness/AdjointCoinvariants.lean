module

public import StacksFrontier.Deformation.Representation.FixedDeterminantFlatness.AdjointRepresentation

/-!
# The coinvariants of `ad⁰ ρ₀` vanish

Let `ρ₀ : G → GLₙ(𝐅_ℓ)` be a representation which is absolutely irreducible on a subgroup `N`,
with `ℓ ∤ n`. Then the differences `g • X - X` (`g ∈ N`, `X ∈ ad⁰ ρ₀`) span `ad⁰ ρ₀`, i.e. the
`N`-coinvariants of `ad⁰ ρ₀` vanish. This is the dual of
`Deformation.AdZero.eq_zero_of_forall_smul_eq` (the invariants vanish) under the trace pairing
`(X, Y) ↦ tr(XY)`, which is perfect on trace-zero matrices since `n` is invertible in `𝐅_ℓ`.

## Main results

* `Deformation.AdZero.exists_trace_mul_eq`: every linear functional on `ad⁰` is `tr(Y ·)` for a
  trace-zero `Y`, when `ℓ ∤ n`.
* `Deformation.AdZero.span_smul_sub_eq_top`: the `N`-coinvariants of `ad⁰ ρ₀` vanish.
-/

@[expose] public noncomputable section

universe u

namespace Deformation.AdZero

open Matrix

variable {G : Type u} [Group G] {n ℓ : ℕ} [Fact ℓ.Prime]
  {ρ : G →* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)}

/-- The trace-zero part `A - (tr A / n) • 1` of a matrix, `n` being invertible. -/
def traceZeroPart (hn : ¬ ℓ ∣ n) (A : Matrix (Fin n) (Fin n) (ZMod ℓ)) : AdZero ρ :=
  mk (A - (A.trace / n) • 1) (by
    have hn' : (n : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul,
      div_mul_cancel₀ _ hn', sub_self])

/-- The underlying matrix of `traceZeroPart hn A` is `A - (tr A / n) • 1`. -/
lemma val_traceZeroPart (hn : ¬ ℓ ∣ n) (A : Matrix (Fin n) (Fin n) (ZMod ℓ)) :
    (traceZeroPart (ρ := ρ) hn A).val = A - (A.trace / n) • 1 := rfl

/-- The trace-zero part of a trace-zero matrix is the matrix itself. -/
lemma traceZeroPart_val (hn : ¬ ℓ ∣ n) (X : AdZero ρ) : traceZeroPart hn X.val = X := by
  ext1
  rw [val_traceZeroPart, trace_val, zero_div, zero_smul, sub_zero]

/-- The trace-zero part, as a linear map. -/
def traceZeroPartₗ (hn : ¬ ℓ ∣ n) : Matrix (Fin n) (Fin n) (ZMod ℓ) →ₗ[ZMod ℓ] AdZero ρ where
  toFun := traceZeroPart hn
  map_add' A B := by
    ext1
    simp only [val_traceZeroPart, val_add, trace_add, add_div, add_smul]
    abel
  map_smul' c A := by
    ext1
    simp only [val_traceZeroPart, val_smul, trace_smul, smul_eq_mul, RingHom.id_apply,
      mul_div_assoc, smul_sub, smul_smul]

/-- A trace-zero matrix pairing to zero with every trace-zero matrix is zero, `ℓ ∤ n`. -/
theorem eq_zero_of_forall_trace_mul_eq_zero (hn : ¬ ℓ ∣ n) (Z : AdZero ρ)
    (hZ : ∀ X : AdZero ρ, (Z.val * X.val).trace = 0) : Z = 0 := by
  ext1
  rw [val_zero, ext_iff_trace_mul_right]
  intro A
  have h := hZ (traceZeroPart hn A)
  rw [val_traceZeroPart, Matrix.mul_sub, trace_sub, Matrix.mul_smul, trace_smul, Matrix.mul_one,
    trace_val, smul_zero, sub_zero] at h
  rw [h, Matrix.zero_mul, trace_zero]

/-- **Every linear functional on `ad⁰` is a trace pairing**: for `ℓ ∤ n`, a linear functional `φ`
on the trace-zero matrices is `X ↦ tr(Y X)` for a trace-zero matrix `Y`. -/
theorem exists_trace_mul_eq (hn : ¬ ℓ ∣ n) (φ : AdZero ρ →ₗ[ZMod ℓ] ZMod ℓ) :
    ∃ Y : AdZero ρ, ∀ X : AdZero ρ, φ X = (Y.val * X.val).trace := by
  classical
  let ψ := φ ∘ₗ traceZeroPartₗ (ρ := ρ) hn
  let Y' : Matrix (Fin n) (Fin n) (ZMod ℓ) := Matrix.of fun j i => ψ (single i j 1)
  have hY' : ∀ A, ψ A = (Y' * A).trace := by
    intro A
    conv_lhs => rw [matrix_eq_sum_single A]
    simp only [map_sum, trace, mul_apply, diag_apply, Y', of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show single j i (A j i) = A j i • single j i (1 : ZMod ℓ) by
      rw [smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
  refine ⟨traceZeroPart hn Y', fun X => ?_⟩
  rw [show φ X = ψ X.val from congrArg φ (traceZeroPart_val hn X).symm, hY', val_traceZeroPart,
    Matrix.sub_mul, trace_sub, Matrix.smul_mul, trace_smul, Matrix.one_mul, trace_val, smul_zero,
    sub_zero]

/-- **The coinvariants of `ad⁰ ρ₀` vanish.** If `ρ₀ : G → GLₙ(𝐅_ℓ)` is absolutely irreducible on
the subgroup `N` and `ℓ ∤ n`, the elements `g • X - X` with `g ∈ N` and `X ∈ ad⁰ ρ₀` span
`ad⁰ ρ₀`. -/
theorem span_smul_sub_eq_top (N : Subgroup G) (hirr : IsAbsolutelyIrreducible fun g : N => ρ g)
    (hn : ¬ ℓ ∣ n) :
    Submodule.span (ZMod ℓ)
      (Set.range fun p : N × AdZero ρ => (p.1 : G) • p.2 - p.2) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨Y, hY⟩ := exists_trace_mul_eq hn φ
  have hinv : ∀ g ∈ N, g • Y = Y := by
    intro g hg
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_trace_mul_eq_zero hn _ fun X => ?_
    have h0 : φ ((g⁻¹ : G) • X - X) = 0 :=
      hle (Submodule.subset_span ⟨(⟨g⁻¹, N.inv_mem hg⟩, X), rfl⟩)
    rw [map_sub, hY, hY, sub_eq_zero, val_smul_group] at h0
    rw [val_sub, val_smul_group, Matrix.sub_mul, trace_sub, sub_eq_zero, ← h0]
    have hinvg : (ρ g⁻¹ : Matrix (Fin n) (Fin n) (ZMod ℓ)) =
        ((ρ g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) := by rw [map_inv]
    have hinvg' : (((ρ g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) :
        Matrix (Fin n) (Fin n) (ZMod ℓ)) = ρ g := by rw [map_inv, inv_inv]
    rw [hinvg, hinvg', Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  apply hφ
  ext X
  rw [hY, eq_zero_of_forall_smul_eq N hirr hn Y hinv, val_zero, Matrix.zero_mul, trace_zero,
    LinearMap.zero_apply]

end Deformation.AdZero

end
