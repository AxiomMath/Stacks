module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.ReductionBlocks
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.Defs
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.Iwasawa

/-!
# The Iwasawa decomposition `GL_n(A) = GL_n(O) · B(A)`

Let `F` be a field and `O` a valuation subring of `F`. Every `g ∈ GL_n(F)` is `k · b` with
`k ∈ GL_n(O)` and `b` upper triangular: choose in the first column an entry `c_p` of largest
valuation, move it to the top by a transposition, clear the rest of the column by a lower
unipotent matrix with entries `c_i / c_p ∈ O`, and proceed with the lower right block.

Over the adele ring `A` of a field `K` the local matrices at the places `v`, with entries in
`O_v`, assemble to an element of `GL_n(O)`: every `x ∈ GL_n(A)` is `κ · b` with `κ ∈ GL_n(O)` and
`b` upper triangular.

## Main results

* `Stacks.Adeles.GeneralLinear.exists_integral_mul_upperTriangular` — the local statement.
* `Stacks.Adeles.GeneralLinear.exists_mem_range_mapO_upperTriangular` — the adelic statement.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Adeles.GeneralLinear

section Local

variable {F : Type*} [Field F] (O : ValuationSubring F)

/-- The matrix with first column `l` and all other columns zero. -/
public def firstColumn {n : ℕ} (l : Fin (n + 1) → F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  of fun i j => if j = 0 then l i else 0

/-- The square of `firstColumn l` vanishes when `l 0 = 0`. -/
public theorem firstColumn_mul_self {n : ℕ} {l : Fin (n + 1) → F} (hl : l 0 = 0) :
    firstColumn l * firstColumn l = 0 := by
  ext i j
  simp [firstColumn, Matrix.mul_apply, hl]

/-- Multiplying by `firstColumn l` on the left, in the first column. -/
public theorem firstColumn_mul_apply_zero {n : ℕ} (l : Fin (n + 1) → F)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (i : Fin (n + 1)) :
    (firstColumn l * M) i 0 = l i * M 0 0 := by
  simp [firstColumn, Matrix.mul_apply]

/-- The permutation matrix of `σ`: `(permRows σ * M) i j = M (σ i) j`. -/
public def permRows {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) F :=
  (1 : Matrix (Fin n) (Fin n) F).submatrix σ id

/-- Multiplying by `permRows σ` on the left permutes the rows. -/
public theorem permRows_mul_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (permRows σ * M : Matrix (Fin n) (Fin n) F) i j = M (σ i) j := by
  simp [permRows, Matrix.mul_apply, Matrix.one_apply]

/-- The permutation matrix of a transposition is its own inverse. -/
public theorem permRows_swap_mul_self {n : ℕ} (a b : Fin n) :
    permRows (F := F) (Equiv.swap a b) * permRows (Equiv.swap a b) = 1 := by
  ext i j
  rw [permRows_mul_apply]
  simp only [permRows, submatrix_apply]
  rw [show (Equiv.swap a b) ((Equiv.swap a b) i) = i from Equiv.swap_apply_self a b i]
  rfl

/-- The entries of a permutation matrix lie in `O`. -/
public theorem permRows_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permRows (F := F) σ i j ∈ O.toSubring :=
  one_mem_entries O.toSubring (σ i) j

/-- **Local Iwasawa decomposition**: for `g` invertible over `F` there are mutually inverse
`k, k'` with entries in the valuation subring `O` such that `k' · g` is upper triangular. -/
public theorem exists_integral_mul_upperTriangular :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) F), g.det ≠ 0 →
      ∃ k k' : Matrix (Fin n) (Fin n) F, (∀ i j, k i j ∈ O.toSubring) ∧
        (∀ i j, k' i j ∈ O.toSubring) ∧ k * k' = 1 ∧ ∀ i j, j < i → (k' * g) i j = 0 := by
  intro n
  induction n with
  | zero =>
    intro g _
    exact ⟨1, 1, one_mem_entries _, one_mem_entries _, mul_one 1, fun i => i.elim0⟩
  | succ n ih =>
    intro g hg
    -- the pivot
    have hex : ∃ i, g i 0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (det_eq_zero_of_column_eq_zero 0 h)
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i => O.valuation (g i 0))
      ⟨i₀, Finset.mem_univ _⟩
    have hp0 : g p 0 ≠ 0 := by
      intro h
      have := hp i₀ (Finset.mem_univ _)
      rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at this
      exact hi₀ this
    set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
    set l : Fin (n + 1) → F := fun i => if i = 0 then 0 else g (σ i) 0 / g p 0
    have hl : ∀ i, l i ∈ O.toSubring := by
      intro i
      simp only [l]
      split_ifs
      · exact O.toSubring.zero_mem
      · rw [ValuationSubring.mem_toSubring, ← ValuationSubring.valuation_le_one_iff, map_div₀,
          div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0))]
        exact hp _ (Finset.mem_univ _)
    set E := firstColumn l
    have hE : ∀ i j, E i j ∈ O.toSubring := by
      intro i j
      simp only [E, firstColumn, of_apply]
      split_ifs
      · exact hl i
      · exact O.toSubring.zero_mem
    have hEE : E * E = 0 := firstColumn_mul_self (by simp [l])
    set k₁ := permRows (F := F) σ * (1 + E)
    set k₁' := (1 - E) * permRows (F := F) σ
    have hk₁ : ∀ i j, k₁ i j ∈ O.toSubring := mul_mem_entries (permRows_mem O σ)
      fun i j => O.toSubring.add_mem (one_mem_entries _ i j) (hE i j)
    have hk₁' : ∀ i j, k₁' i j ∈ O.toSubring := mul_mem_entries
      (fun i j => O.toSubring.sub_mem (one_mem_entries _ i j) (hE i j)) (permRows_mem O σ)
    have h1E : (1 + E) * (1 - E) = 1 := by
      rw [add_mul, one_mul, mul_sub, mul_one, hEE]
      abel
    have hkk₁ : k₁ * k₁' = 1 := by
      simp only [k₁, k₁']
      rw [mul_assoc, ← mul_assoc (1 + E), h1E, one_mul]
      exact permRows_swap_mul_self 0 p
    -- the first column of `k₁' g`
    set h := k₁' * g
    have hcol : ∀ i : Fin (n + 1), i ≠ 0 → h i 0 = 0 := by
      intro i hi
      have hσ0 : σ 0 = p := Equiv.swap_apply_left 0 p
      simp only [h, k₁', mul_assoc, sub_mul, one_mul, Matrix.sub_apply, firstColumn_mul_apply_zero,
        permRows_mul_apply, hσ0, E]
      simp only [l, hi, ↓reduceIte]
      field_simp
      ring
    have hdet : h.det ≠ 0 := by
      have h2 : k₁.det * k₁'.det = 1 := by rw [← det_mul, hkk₁, det_one]
      simp only [h, det_mul]
      exact mul_ne_zero (right_ne_zero_of_mul_eq_one h2) hg
    -- the lower right block
    have hsplit := eq_blockMat (m := 1) (n := n) h
    have hC : (of fun i j => h (blockEquiv 1 n (Sum.inr i)) (blockEquiv 1 n (Sum.inl j)) :
        Matrix (Fin n) (Fin 1) F) = 0 := by
      ext i j
      rw [of_apply, Matrix.zero_apply]
      have hj : blockEquiv 1 n (Sum.inl j) = 0 := Fin.ext (by simp)
      rw [hj]
      exact hcol _ (fun h0 => by
        have := congrArg Fin.val h0
        simp at this)
    rw [hC] at hsplit
    set A : Matrix (Fin 1) (Fin 1) F :=
      of fun i j => h (blockEquiv 1 n (Sum.inl i)) (blockEquiv 1 n (Sum.inl j))
    set B : Matrix (Fin 1) (Fin n) F :=
      of fun i j => h (blockEquiv 1 n (Sum.inl i)) (blockEquiv 1 n (Sum.inr j))
    set D : Matrix (Fin n) (Fin n) F :=
      of fun i j => h (blockEquiv 1 n (Sum.inr i)) (blockEquiv 1 n (Sum.inr j))
    have hD : D.det ≠ 0 := by
      have := hdet
      rw [hsplit, det_blockMat_zero] at this
      exact right_ne_zero_of_mul this
    obtain ⟨k₂, k₂', hk₂, hk₂', hkk₂, hut₂⟩ := ih D hD
    refine ⟨k₁ * blockRight F 1 n k₂, blockRight F 1 n k₂' * k₁', mul_mem_entries hk₁
      (blockMat_mem (one_mem_entries _) (zero_mem_entries _) (zero_mem_entries _) hk₂),
      mul_mem_entries (blockMat_mem (one_mem_entries _) (zero_mem_entries _)
        (zero_mem_entries _) hk₂') hk₁', ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc (blockRight F 1 n k₂), ← map_mul, hkk₂, map_one, one_mul, hkk₁]
    · have : blockRight F 1 n k₂' * k₁' * g = blockMat A B 0 (k₂' * D) := by
        rw [mul_assoc]
        change blockMat 1 0 0 k₂' * h = _
        rw [hsplit, blockMat_mul]
        simp
      rw [this]
      exact blockMat_upperTriangular B (upperTriangular_fin_one A) hut₂

end Local

section Adelic

open Stacks.Adeles.GlobalFunctionField

variable {K : Type u} [Field K] {n : ℕ}

/-- The adelic matrix with components `k v` at the places `v`, when all their entries are
integral. -/
public def adeleMatrix (k : ∀ v : Place K, Matrix (Fin n) (Fin n) v.completion)
    (hk : ∀ v i j, k v i j ∈ (v.integers).toSubring) : Matrix (Fin n) (Fin n) (AdeleRing K) :=
  of fun i j => ⟨fun v => k v i j, Filter.Eventually.of_forall fun v => hk v i j⟩

/-- The component of `adeleMatrix k hk` at `v` is `k v`. -/
public theorem evalAt_mapMatrix_adeleMatrix (k : ∀ v : Place K, Matrix (Fin n) (Fin n) v.completion)
    (hk : ∀ v i j, k v i j ∈ (v.integers).toSubring) (v : Place K) :
    (evalAt K v).mapMatrix (adeleMatrix k hk) = k v := by
  ext i j
  rfl

/-- Two adelic matrices with the same components at every place are equal. -/
public theorem matrix_ext_evalAt' {M N : Matrix (Fin n) (Fin n) (AdeleRing K)}
    (h : ∀ v, (evalAt K v).mapMatrix M = (evalAt K v).mapMatrix N) : M = N := by
  ext i j v
  exact congrFun (congrFun (h v) i) j

/-- **Iwasawa decomposition**: every `x ∈ GL_n(A)` is `κ · b` with `κ ∈ GL_n(O)` and `b` upper
triangular. -/
public theorem exists_mem_range_mapO_upperTriangular (x : GL (Fin n) (AdeleRing K)) :
    ∃ κ ∈ (mapO K n).range, ∀ i j, j < i →
      ((κ⁻¹ * x : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) i j = 0 := by
  set g : ∀ v : Place K, Matrix (Fin n) (Fin n) v.completion :=
    fun v => (evalAt K v).mapMatrix (x : Matrix (Fin n) (Fin n) (AdeleRing K))
  have hdet : ∀ v, (g v).det ≠ 0 := fun v => by
    simp only [g]
    rw [← RingHom.map_det]
    exact (((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).map (evalAt K v)).ne_zero
  choose k k' hk hk' hkk' hut using fun v =>
    exists_integral_mul_upperTriangular (v.integers) n (g v) (hdet v)
  set kM := adeleMatrix k hk
  set kI := adeleMatrix k' hk'
  have h1 : kM * kI = 1 := matrix_ext_evalAt' fun v => by
    rw [map_mul, evalAt_mapMatrix_adeleMatrix, evalAt_mapMatrix_adeleMatrix, hkk', map_one]
  set κ : GL (Fin n) (AdeleRing K) := ⟨kM, kI, h1, mul_eq_one_comm.1 h1⟩
  refine ⟨κ, (mem_range_map_subtype_iff _ κ).2 ⟨fun i j v => hk v i j, fun i j v => hk' v i j⟩,
    fun i j hij => ?_⟩
  have hb : ((κ⁻¹ * x : GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) =
      kI * (x : Matrix (Fin n) (Fin n) (AdeleRing K)) := rfl
  rw [hb]
  refine RestrictedProduct.ext _ _ fun v => ?_
  have := congrFun (congrFun (show (evalAt K v).mapMatrix
      (kI * (x : Matrix (Fin n) (Fin n) (AdeleRing K))) = k' v * g v by
    rw [map_mul, evalAt_mapMatrix_adeleMatrix]) i) j
  rw [hut v i j hij] at this
  exact this

end Adelic

end Stacks.Adeles.GeneralLinear

end
