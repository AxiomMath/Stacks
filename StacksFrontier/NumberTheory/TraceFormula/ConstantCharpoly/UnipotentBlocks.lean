module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.SpanLatticeBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AlgebraicBlockForm

/-!
# Unipotent elements and absolutely irreducible graded blocks

Two algebraic inputs to the finiteness of the image of a representation over `F_ℓ[[t]]` whose
characteristic polynomials have constant coefficients.

First, a matrix `A` over a power series ring `k[[t]]` whose characteristic polynomial has
constant coefficients and whose reduction modulo `t` is the identity is unipotent:
its characteristic polynomial is that of its reduction, `(X - 1)ⁿ`, so `(A - 1)ⁿ = 0` by
Cayley–Hamilton.

Second, a family of graded upper triangular matrices over a field `E`, closed under products and
containing `1`, whose diagonal blocks are irreducible over an algebraically closed field
`K ⊇ E`, and all of whose members are unipotent, has identity diagonal blocks. Indeed each block
family spans all block matrices over `E` (Burnside's theorem), the blocks of unipotent matrices
have trace the block size, so `tr (Y (B - 1)) = 0` for every block `B` and every matrix `Y` in
the span, and the trace form is nondegenerate.

## Main results

* `Stacks.TraceFormula.pow_sub_one_eq_zero_of_charpoly_coeff_mem_range_C`.
* `Stacks.EtaleCohomology.toSquareBlock_mul_of_isGradedUpper`: on graded upper triangular matrices,
  taking a diagonal block is multiplicative.
* `Stacks.TraceFormula.eq_one_of_isNilpotent_sub_one`: an absolutely irreducible family of
  unipotent matrices closed under products is trivial.
* `Stacks.TraceFormula.apply_eq_one_apply_of_isNilpotent_sub_one`: the diagonal blocks of a
  family of unipotent graded upper triangular matrices with absolutely irreducible blocks are
  identity blocks.
-/

@[expose] public noncomputable section

open Matrix Stacks.EtaleCohomology

namespace Stacks.TraceFormula

section Unipotent

variable {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]

/-- **A matrix over `k[[t]]` with constant characteristic polynomial and identity reduction is
unipotent.** If every coefficient of the characteristic polynomial of `A` is a constant power
series and `A` reduces to the identity modulo `t`, then `(A - 1)ⁿ = 0`, `n` the size of `A`. -/
theorem pow_sub_one_eq_zero_of_charpoly_coeff_mem_range_C {A : Matrix ι ι (PowerSeries k)}
    (hchar : ∀ i, A.charpoly.coeff i ∈ Set.range (PowerSeries.C (R := k)))
    (hA : A.map PowerSeries.constantCoeff = 1) :
    (A - 1) ^ Fintype.card ι = 0 := by
  have hmap : A.charpoly.map PowerSeries.constantCoeff = (Polynomial.X - 1) ^ Fintype.card ι := by
    rw [← Matrix.charpoly_map, hA, Matrix.charpoly_one]
  have hconst : A.charpoly = (A.charpoly.map PowerSeries.constantCoeff).map PowerSeries.C := by
    ext i
    obtain ⟨c, hc⟩ := hchar i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, ← hc, PowerSeries.constantCoeff_C]
  have hcp : A.charpoly = (Polynomial.X - 1) ^ Fintype.card ι := by
    rw [hconst, hmap, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one]
  have := Matrix.aeval_self_charpoly A
  rwa [hcp, map_pow, map_sub, Polynomial.aeval_X, map_one] at this

end Unipotent

end Stacks.TraceFormula

namespace Stacks.EtaleCohomology

section Blocks

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {d : ι → ℤ}

omit [Fintype ι] in
/-- The diagonal block of the identity matrix is the identity matrix. -/
theorem toSquareBlock_one (t : ℤ) : (1 : Matrix ι ι R).toSquareBlock d t = 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp [Matrix.toSquareBlock_def, Matrix.one_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- Taking a diagonal block commutes with subtraction. -/
theorem toSquareBlock_sub (S U : Matrix ι ι R) (t : ℤ) :
    (S - U).toSquareBlock d t = S.toSquareBlock d t - U.toSquareBlock d t := by
  ext i j
  simp [Matrix.toSquareBlock_def]

omit [DecidableEq ι] in
/-- **Diagonal blocks of graded upper triangular matrices multiply.** For graded upper
triangular `S` and `U`, the diagonal block of `S * U` is the product of the diagonal blocks: an
index `k` contributing to an entry of the block `t` has `t ≤ d k ≤ t`. -/
theorem toSquareBlock_mul_of_isGradedUpper {S U : Matrix ι ι R} (hS : IsGradedUpper d S)
    (hU : IsGradedUpper d U) (t : ℤ) :
    (S * U).toSquareBlock d t = S.toSquareBlock d t * U.toSquareBlock d t := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => d k = t)]
  have h0 : ∑ k : {k // ¬ d k = t}, S i k * U k j = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_gt_of_ne k.2 with h | h
    · rw [hS i k (hi ▸ h), zero_mul]
    · rw [hU k j (hj ▸ h), mul_zero]
  rw [h0, add_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- A difference of graded upper triangular matrices is graded upper triangular. -/
theorem IsGradedUpper.sub {S U : Matrix ι ι R} (hS : IsGradedUpper d S)
    (hU : IsGradedUpper d U) : IsGradedUpper d (S - U) := fun i j h => by
  rw [Matrix.sub_apply, hS i j h, hU i j h, sub_zero]

/-- A power of a graded upper triangular matrix is graded upper triangular. -/
theorem IsGradedUpper.pow {S : Matrix ι ι R} (hS : IsGradedUpper d S) (m : ℕ) :
    IsGradedUpper d (S ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact isGradedUpper_one
  | succ m ih => rw [pow_succ]; exact ih.mul hS

/-- The diagonal block of a power of a graded upper triangular matrix is the power of its
diagonal block. -/
theorem toSquareBlock_pow_of_isGradedUpper {S : Matrix ι ι R} (hS : IsGradedUpper d S)
    (t : ℤ) (m : ℕ) : (S ^ m).toSquareBlock d t = S.toSquareBlock d t ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, toSquareBlock_one]
  | succ m ih => rw [pow_succ, pow_succ, toSquareBlock_mul_of_isGradedUpper (hS.pow m) hS, ih]

end Blocks

end Stacks.EtaleCohomology

namespace Stacks.TraceFormula

section Burnside

variable {E K ι A : Type*} [Field E] [Field K] [IsAlgClosed K] [Algebra E K] [Fintype ι]
  [DecidableEq ι]

/-- **An absolutely irreducible family of unipotent matrices is trivial.** If `M : A → M_ι(E)`
is closed under products, contains `1`, stabilizes no subspace of `K^ι` other than `0` and
`K^ι` over an algebraically closed `K ⊇ E`, and every `M a - 1` is nilpotent, then every `M a`
is `1`. By Burnside's theorem the `M b` span `M_ι(E)`; since `M b * M a` is again in the family
and unipotent matrices have trace `|ι|`, the trace of `M b * (M a - 1)` vanishes, so `M a - 1`
is orthogonal to all matrices under the trace form. -/
theorem eq_one_of_isNilpotent_sub_one (M : A → Matrix ι ι E)
    (hmul : ∀ a b, ∃ c, M a * M b = M c) (hone : ∃ a, M a = 1)
    (hirr : ∀ W : Submodule K (ι → K), (∀ a, ∀ v ∈ W, (M a).map (algebraMap E K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (hnil : ∀ a, IsNilpotent (M a - 1)) (a : A) : M a = 1 := by
  have hspan := span_range_eq_top_of_forall_mulVec_map_mem (K := K) M hmul hone hirr
  have htr : ∀ b, (M b).trace = Fintype.card ι := fun b => by
    have h0 : (M b - 1).trace = 0 := (Matrix.isNilpotent_trace_of_isNilpotent (hnil b)).eq_zero
    rwa [Matrix.trace_sub, Matrix.trace_one, sub_eq_zero] at h0
  set φ : Matrix ι ι E →ₗ[E] E :=
    (Matrix.traceLinearMap ι E E).comp (LinearMap.mulRight E (M a - 1)) with hφ_def
  have hle : Submodule.span E (Set.range M) ≤ LinearMap.ker φ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    obtain ⟨c, hc⟩ := hmul b a
    simp [φ, mul_sub, hc, Matrix.trace_sub, htr]
  rw [← sub_eq_zero]
  ext i j
  have := hle (hspan ▸ Submodule.mem_top : Matrix.single j i (1 : E) ∈ _)
  simpa [φ, Matrix.trace_single_mul] using this

/-- **Unipotent graded families with absolutely irreducible blocks have identity diagonal
blocks.** Let `T : A → M_r(E)` be graded upper triangular for `d`, closed under products,
containing `1`, with every `T a - 1` nilpotent, and such that over an algebraically closed
`K ⊇ E` the graded diagonal parts stabilize no nonzero proper subspace of any coordinate block.
Then `T a i j = δ i j` whenever `d i = d j`. -/
theorem apply_eq_one_apply_of_isNilpotent_sub_one {r : ℕ} (T : A → Matrix (Fin r) (Fin r) E)
    (d : Fin r → ℤ) (hup : ∀ a, IsGradedUpper d (T a)) (hmul : ∀ a b, ∃ c, T a * T b = T c)
    (hone : ∃ a, T a = 1) (hnil : ∀ a, IsNilpotent (T a - 1))
    (hirr : ∀ (t : ℤ) (W' : Submodule K (Fin r → K)),
      W' ≤ coordSubspace (K := K) (fun i => d i = t) → W' ≠ ⊥ →
      (∀ a, ∀ v ∈ W', (gradedDiag d (T a)).map (algebraMap E K) *ᵥ v ∈ W') →
      W' = coordSubspace (K := K) (fun i => d i = t))
    (a : A) {i j : Fin r} (hij : d i = d j) : T a i j = (1 : Matrix (Fin r) (Fin r) E) i j := by
  set t := d i with ht
  set M : A → Matrix {k // d k = t} {k // d k = t} E := fun b => (T b).toSquareBlock d t
    with hM_def
  have hmul' : ∀ b c, ∃ e, M b * M c = M e := fun b c => by
    obtain ⟨e, he⟩ := hmul b c
    exact ⟨e, by simp only [hM_def]; rw [← toSquareBlock_mul_of_isGradedUpper (hup b) (hup c), he]⟩
  have hone' : ∃ b, M b = 1 := by
    obtain ⟨b, hb⟩ := hone
    exact ⟨b, by simp only [hM_def]; rw [hb, toSquareBlock_one]⟩
  have hnil' : ∀ b, IsNilpotent (M b - 1) := fun b => by
    obtain ⟨m, hm⟩ := hnil b
    refine ⟨m, ?_⟩
    simp only [hM_def]
    rw [← toSquareBlock_one (R := E) (d := d) t, ← toSquareBlock_sub,
      ← toSquareBlock_pow_of_isGradedUpper ((hup b).sub isGradedUpper_one), hm]
    ext
    simp [Matrix.toSquareBlock_def]
  set X : A → Matrix (Fin r) (Fin r) K := fun b => (gradedDiag d (T b)).map (algebraMap E K)
    with hX_def
  have hXbd : ∀ b i j, d i ≠ d j → X b i j = 0 := fun b i j h => by
    simp [hX_def, gradedDiag, h]
  have hXM : ∀ b, (X b).toSquareBlock d t = (M b).map (algebraMap E K) := fun b => by
    ext ⟨k, hk⟩ ⟨l, hl⟩
    simp [hX_def, hM_def, Matrix.toSquareBlock_def, gradedDiag, hk, hl]
  have hirr' : ∀ W : Submodule K ({k // d k = t} → K),
      (∀ b, ∀ v ∈ W, (M b).map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    forall_block_eq_bot_or_eq_top (X := X) hXbd (hirr t) W fun b v hv => by
      rw [hXM]; exact hW b v hv
  have h1 := eq_one_of_isNilpotent_sub_one (K := K) M hmul' hone' hirr' hnil' a
  have := congrFun (congrFun h1 ⟨i, rfl⟩) ⟨j, hij.symm⟩
  simpa [hM_def, Matrix.toSquareBlock_def, Matrix.one_apply] using this

end Burnside

end Stacks.TraceFormula

end
