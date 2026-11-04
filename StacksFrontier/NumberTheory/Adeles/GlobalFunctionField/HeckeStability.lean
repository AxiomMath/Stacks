module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsBaseChange

/-!
# Stability of `C(Λ)` under the Hecke operators

The Hecke operator `T_v f (x) = f(g₀ x) + ∑ᵢ f(gᵢ x)` maps `C(Λ)` to itself. The only nontrivial
point is left `GL₂(O)`-invariance: right multiplication by `u ∈ GL₂(O_v)` permutes the cosets
`GL₂(O_v) M_j` of the `q_v + 1` local matrices `M_j` of the formula, and this permutation is made
explicit here through the residues of the rows of `u`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section Local

variable {K : Type u} [Field K] (v : Place K)

/-- A `2 × 2` matrix over `K_v` with entries in `O_v`. -/
public def IsIntMat (N : Matrix (Fin 2) (Fin 2) v.completion) : Prop := ∀ i j, N i j ∈ v.integers

variable {v}

/-- A product of integral matrices is integral. -/
public theorem IsIntMat.mul {N N' : Matrix (Fin 2) (Fin 2) v.completion} (h : IsIntMat v N)
    (h' : IsIntMat v N') : IsIntMat v (N * N') := by
  intro i j
  rw [mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (h i 0) (h' 0 j)) (mul_mem (h i 1) (h' 1 j))

/-- An integral matrix with integral inverse determinant has integral inverse. -/
public theorem IsIntMat.inv {N : Matrix (Fin 2) (Fin 2) v.completion} (h : IsIntMat v N)
    (hdet : N.det⁻¹ ∈ v.integers) : IsIntMat v N⁻¹ := by
  intro i j
  rw [inv_def, Ring.inverse_eq_inv', adjugate_fin_two, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem hdet ?_
  fin_cases i <;> fin_cases j <;> simp [h 0 0, h 1 1, neg_mem (h 0 1), neg_mem (h 1 0)]

variable (v)

/-- The local matrices of the Hecke operator at `v`: `diag (π⁻¹, 1)` and
`(1, 0; -π⁻¹ λᵢ, π⁻¹)`. -/
public def heckeLocal (π : v.completion) {q : ℕ} (lam : Fin q → v.completion) :
    Option (Fin q) → Matrix (Fin 2) (Fin 2) v.completion
  | none => !![π⁻¹, 0; 0, 1]
  | some i => !![1, 0; -(π⁻¹ * lam i), π⁻¹]

/-- Their inverses `diag (π, 1)` and `(1, 0; λᵢ, π)`. -/
public def heckeLocalInv (π : v.completion) {q : ℕ} (lam : Fin q → v.completion) :
    Option (Fin q) → Matrix (Fin 2) (Fin 2) v.completion
  | none => !![π, 0; 0, 1]
  | some i => !![1, 0; lam i, π]

variable {v}

/-- `heckeLocalInv` is a right inverse of `heckeLocal`. -/
public theorem heckeLocal_mul_inv {π : v.completion} (hπ : π ≠ 0) {q : ℕ}
    (lam : Fin q → v.completion) (j : Option (Fin q)) :
    heckeLocal v π lam j * heckeLocalInv v π lam j = 1 := by
  cases j <;> simp only [heckeLocal, heckeLocalInv] <;> rw [mul_fin_two, one_fin_two] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [hπ]

/-- Every local Hecke matrix has determinant `π⁻¹`. -/
public theorem det_heckeLocal (π : v.completion) {q : ℕ} (lam : Fin q → v.completion)
    (j : Option (Fin q)) : (heckeLocal v π lam j).det = π⁻¹ := by
  cases j <;> simp [heckeLocal, det_fin_two]

/-- Every inverse local Hecke matrix has determinant `π`. -/
public theorem det_heckeLocalInv (π : v.completion) {q : ℕ} (lam : Fin q → v.completion)
    (j : Option (Fin q)) : (heckeLocalInv v π lam j).det = π := by
  cases j <;> simp [heckeLocalInv, det_fin_two]

/-- If `z ∈ (π)` then `z / π ∈ O_v`. -/
public theorem div_mem_integers_of_mem_span {π z : v.integers} (hz : z ∈ Ideal.span {π})
    (hπ : (π : v.completion) ≠ 0) : (z : v.completion) * (π : v.completion)⁻¹ ∈ v.integers := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  push_cast
  rw [mul_assoc, mul_inv_cancel₀ hπ, mul_one]
  exact t.2

/-- The matrix `!![e₁₁, e₁₂; e₂₁, e₂₂]` is integral when its four entries lie in `O_v`. -/
public theorem isIntMat_of {e₁₁ e₁₂ e₂₁ e₂₂ : v.completion} (h₁₁ : e₁₁ ∈ v.integers)
    (h₁₂ : e₁₂ ∈ v.integers) (h₂₁ : e₂₁ ∈ v.integers) (h₂₂ : e₂₂ ∈ v.integers) :
    IsIntMat v !![e₁₁, e₁₂; e₂₁, e₂₂] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

section Selector

variable {π : v.integers} {q : ℕ} {lam : Fin q → v.integers}

open scoped Classical in
/-- The residue selector: `none` if `y ∈ (π)`, else the `i` with `x + y λᵢ ∈ (π)`. -/
public def resSel (hlam : Place.IsResidueSystem v π lam) (x y : v.integers) : Option (Fin q) :=
  if y ∈ Ideal.span {π} then none else some (hlam (-(x * Ring.inverse y))).exists.choose

/-- The residue selector is `none` when `y ∈ (π)`. -/
public theorem resSel_of_mem (hlam : Place.IsResidueSystem v π lam) {x y : v.integers}
    (hy : y ∈ Ideal.span {π}) : resSel hlam x y = none := by
  classical
  simp [resSel, hy]

/-- When `y ∉ (π)`, the residue selector is `some i` with `x + y λᵢ ∈ (π)`. -/
public theorem resSel_of_notMem (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) {x y : v.integers} (hy : y ∉ Ideal.span {π}) :
    ∃ i, resSel hlam x y = some i ∧ x + y * lam i ∈ Ideal.span {π} := by
  classical
  refine ⟨(hlam (-(x * Ring.inverse y))).exists.choose, by simp [resSel, hy], ?_⟩
  have hspec := (hlam (-(x * Ring.inverse y))).exists.choose_spec
  have hunit : IsUnit y := by
    by_contra h
    exact hy (hπ ▸ (IsLocalRing.mem_maximalIdeal y).2 h)
  have : x + y * lam (hlam (-(x * Ring.inverse y))).exists.choose =
      -y * (-(x * Ring.inverse y) - lam (hlam (-(x * Ring.inverse y))).exists.choose) := by
    have h1 : y * Ring.inverse y = 1 := Ring.mul_inverse_cancel y hunit
    linear_combination (-x) * h1
  rw [this]
  exact Ideal.mul_mem_left _ _ hspec

end Selector

section Cases

variable {p : v.completion} (hp : p ≠ 0) {A B C D l l' : v.completion}
include hp

/-- The conjugate `M_∞ (A, B; C, D) M_∞⁻¹`, computed entrywise. -/
public theorem heckeLocal_triple_none_none :
    !![p⁻¹, 0; 0, 1] * !![A, B; C, D] * !![p, 0; 0, 1] = !![A, B * p⁻¹; C * p, D] := by
  rw [mul_fin_two, mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp <;>
    field_simp

/-- The product `M_∞ (A, B; C, D) M_{l'}⁻¹`, computed entrywise. -/
public theorem heckeLocal_triple_none_some :
    !![p⁻¹, 0; 0, 1] * !![A, B; C, D] * !![1, 0; l', p] =
      !![(A + B * l') * p⁻¹, B; C + D * l', D * p] := by
  rw [mul_fin_two, mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp <;>
    field_simp

/-- The product `M_l (A, B; C, D) M_∞⁻¹`, computed entrywise. -/
public theorem heckeLocal_triple_some_none :
    !![1, 0; -(p⁻¹ * l), p⁻¹] * !![A, B; C, D] * !![p, 0; 0, 1] =
      !![A * p, B; C - l * A, (D - l * B) * p⁻¹] := by
  rw [mul_fin_two, mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp <;>
    field_simp <;> ring

/-- The product `M_l (A, B; C, D) M_{l'}⁻¹`, computed entrywise. -/
public theorem heckeLocal_triple_some_some :
    !![1, 0; -(p⁻¹ * l), p⁻¹] * !![A, B; C, D] * !![1, 0; l', p] =
      !![A + B * l', B * p; ((C - l * A) + (D - l * B) * l') * p⁻¹, D - l * B] := by
  rw [mul_fin_two, mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp <;>
    field_simp <;> ring

end Cases

section Permutation

variable {π : v.integers} {q : ℕ} {lam : Fin q → v.integers}

/-- The determinant of an integral matrix is integral. -/
public theorem IsIntMat.det_mem {N : Matrix (Fin 2) (Fin 2) v.completion} (h : IsIntMat v N) :
    N.det ∈ v.integers := by
  rw [det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

/-- The permutation `σ` of the `q + 1` cosets induced by an integral matrix `u`: it is read off
from the residues of the rows `(a, b)` and `(c - λ_l a, d - λ_l b)` of `u`. -/
public def heckeSel (hlam : Place.IsResidueSystem v π lam) (u : Matrix (Fin 2) (Fin 2) v.completion)
    (hu : IsIntMat v u) : Option (Fin q) → Option (Fin q)
  | none => resSel hlam ⟨u 0 0, hu 0 0⟩ ⟨u 0 1, hu 0 1⟩
  | some l => resSel hlam (⟨u 1 0, hu 1 0⟩ - lam l * ⟨u 0 0, hu 0 0⟩)
      (⟨u 1 1, hu 1 1⟩ - lam l * ⟨u 0 1, hu 0 1⟩)

/-- `M_∞ u M_{σ ∞}⁻¹` is integral, for `u = (a, b; c, d)`. -/
public theorem isIntMat_heckeLocal_none (hπ : Place.IsUniformizer v π)
    (hπ0 : (π : v.completion) ≠ 0) (hlam : Place.IsResidueSystem v π lam) (a b c d : v.integers) :
    IsIntMat v (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) none *
      !![(a : v.completion), b; c, d] *
      heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) (resSel hlam a b)) := by
  by_cases hy : b ∈ Ideal.span {π}
  · rw [resSel_of_mem hlam hy]
    simp only [heckeLocal, heckeLocalInv]
    rw [heckeLocal_triple_none_none hπ0]
    exact isIntMat_of a.2 (div_mem_integers_of_mem_span hy hπ0) (mul_mem c.2 π.2) d.2
  · obtain ⟨i, hs, hx⟩ := resSel_of_notMem hπ hlam hy
    rw [hs]
    simp only [heckeLocal, heckeLocalInv]
    rw [heckeLocal_triple_none_some hπ0]
    have h := div_mem_integers_of_mem_span hx hπ0
    push_cast at h
    exact isIntMat_of h b.2 (add_mem c.2 (mul_mem d.2 (lam i).2)) (mul_mem d.2 π.2)

/-- `M_l u M_{σ l}⁻¹` is integral, for `u = (a, b; c, d)`. -/
public theorem isIntMat_heckeLocal_some (hπ : Place.IsUniformizer v π)
    (hπ0 : (π : v.completion) ≠ 0) (hlam : Place.IsResidueSystem v π lam) (l : Fin q)
    (a b c d : v.integers) :
    IsIntMat v (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) (some l) *
      !![(a : v.completion), b; c, d] *
      heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion))
        (resSel hlam (c - lam l * a) (d - lam l * b))) := by
  by_cases hy : d - lam l * b ∈ Ideal.span {π}
  · rw [resSel_of_mem hlam hy]
    simp only [heckeLocal, heckeLocalInv]
    rw [heckeLocal_triple_some_none hπ0]
    have h := div_mem_integers_of_mem_span hy hπ0
    push_cast at h
    exact isIntMat_of (mul_mem a.2 π.2) b.2 (sub_mem c.2 (mul_mem (lam l).2 a.2)) h
  · obtain ⟨i, hs, hx⟩ := resSel_of_notMem hπ hlam hy
    rw [hs]
    simp only [heckeLocal, heckeLocalInv]
    rw [heckeLocal_triple_some_some hπ0]
    have h := div_mem_integers_of_mem_span hx hπ0
    push_cast at h
    exact isIntMat_of (add_mem a.2 (mul_mem b.2 (lam i).2)) (mul_mem b.2 π.2) h
      (sub_mem d.2 (mul_mem (lam l).2 b.2))

/-- `M_j u M_{σ j}⁻¹` is integral. -/
public theorem isIntMat_heckeLocal_mul_mul (hπ : Place.IsUniformizer v π)
    (hπ0 : (π : v.completion) ≠ 0) (hlam : Place.IsResidueSystem v π lam)
    {u : Matrix (Fin 2) (Fin 2) v.completion} (hu : IsIntMat v u) (j : Option (Fin q)) :
    IsIntMat v (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) j * u *
      heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion))
        (heckeSel hlam u hu j)) := by
  obtain ⟨X, hX⟩ : ∃ X, X = heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion))
      (heckeSel hlam u hu j) := ⟨_, rfl⟩
  rw [← hX]
  have hu' : u = !![((⟨u 0 0, hu 0 0⟩ : v.integers) : v.completion),
      ((⟨u 0 1, hu 0 1⟩ : v.integers) : v.completion);
      ((⟨u 1 0, hu 1 0⟩ : v.integers) : v.completion),
      ((⟨u 1 1, hu 1 1⟩ : v.integers) : v.completion)] := eta_fin_two u
  rw [hu', hX]
  cases j with
  | none => exact isIntMat_heckeLocal_none hπ hπ0 hlam _ _ _ _
  | some l => exact isIntMat_heckeLocal_some hπ hπ0 hlam l _ _ _ _

/-- `π⁻¹ ∉ O_v`. -/
public theorem inv_notMem_integers (hπ : Place.IsUniformizer v π) (hπ0 : (π : v.completion) ≠ 0) :
    (π : v.completion)⁻¹ ∉ v.integers := by
  intro h
  have hunit : IsUnit π := isUnit_iff_exists_inv.2 ⟨⟨_, h⟩, Subtype.ext (mul_inv_cancel₀ hπ0)⟩
  have hmem : π ∈ IsLocalRing.maximalIdeal v.integers := hπ ▸ Ideal.subset_span rfl
  exact (IsLocalRing.mem_maximalIdeal π).1 hmem hunit

/-- If `M_j M_{j'}⁻¹` is integral then `j = j'`. -/
public theorem eq_of_isIntMat_heckeLocal_mul_inv (hπ : Place.IsUniformizer v π)
    (hπ0 : (π : v.completion) ≠ 0) (hlam : Place.IsResidueSystem v π lam) {j j' : Option (Fin q)}
    (h : IsIntMat v (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) j *
      heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) j')) : j = j' := by
  cases j with
  | none =>
    cases j' with
    | none => rfl
    | some l' =>
      have e : (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) none *
          heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) (some l')) 0 0 =
          (π : v.completion)⁻¹ := by
        simp [heckeLocal, heckeLocalInv, mul_apply, Fin.sum_univ_two]
      exact absurd (e ▸ h 0 0) (inv_notMem_integers hπ hπ0)
  | some l =>
    cases j' with
    | none =>
      have e : (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) (some l) *
          heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) none) 1 1 =
          (π : v.completion)⁻¹ := by
        simp [heckeLocal, heckeLocalInv, mul_apply, Fin.sum_univ_two]
      exact absurd (e ▸ h 1 1) (inv_notMem_integers hπ hπ0)
    | some l' =>
      have e : (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) (some l) *
          heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) (some l')) 1 0 =
          ((lam l' : v.completion) - (lam l : v.completion)) * (π : v.completion)⁻¹ := by
        simp [heckeLocal, heckeLocalInv, mul_apply, Fin.sum_univ_two]
        ring
      have h10 := e ▸ h 1 0
      have hmem : lam l' - lam l ∈ Ideal.span {π} := by
        refine Ideal.mem_span_singleton'.2 ⟨⟨_, h10⟩, Subtype.ext ?_⟩
        show ((lam l' : v.completion) - (lam l : v.completion)) * (π : v.completion)⁻¹ *
          (π : v.completion) = (lam l' : v.completion) - (lam l : v.completion)
        rw [mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
      obtain ⟨i₀, -, huniq⟩ := hlam (lam l')
      rw [huniq l hmem, huniq l' (by simp)]

end Permutation

end Local

section Global

variable {K : Type u} [Field K]

variable (K) in
/-- The component at `w` of a matrix of adeles. -/
public abbrev localMat (w : Place K) (x : GL (Fin 2) (AdeleRing K)) :
    Matrix (Fin 2) (Fin 2) w.completion :=
  (evalAt K w).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing K))

/-- Taking the component at `w` is multiplicative. -/
public theorem localMat_mul (w : Place K) (x y : GL (Fin 2) (AdeleRing K)) :
    localMat K w (x * y) = localMat K w x * localMat K w y := by
  simp only [localMat, Matrix.GeneralLinearGroup.coe_mul, map_mul]

/-- The component at `w` of the identity is the identity. -/
public theorem localMat_one (w : Place K) : localMat K w 1 = 1 := by
  simp only [localMat, Matrix.GeneralLinearGroup.coe_one, map_one]

/-- The component at `w` of an inverse is the inverse of the component. -/
public theorem localMat_inv (w : Place K) (x : GL (Fin 2) (AdeleRing K)) :
    localMat K w x⁻¹ = (localMat K w x)⁻¹ :=
  (Matrix.inv_eq_right_inv (by rw [← localMat_mul, mul_inv_cancel, localMat_one])).symm

/-- Two elements of `GL₂(A)` with the same component at every place are equal. -/
public theorem localMat_ext {x y : GL (Fin 2) (AdeleRing K)}
    (h : ∀ w, localMat K w x = localMat K w y) : x = y :=
  Units.ext (matrix_ext_evalAt h)

/-- The component at `w` of an element of `GL₂(O)` is integral. -/
public theorem isIntMat_localMat_mapO (w : Place K) (κ : GL (Fin 2) (integralAdeles K)) :
    IsIntMat w (localMat K w (mapO κ)) :=
  fun i j => ((κ : Matrix (Fin 2) (Fin 2) (integralAdeles K)) i j).2 w

/-- The inverse determinant of the component at `w` of an element of `GL₂(O)` lies in `O_w`. -/
public theorem det_localMat_mapO_inv_mem (w : Place K) (κ : GL (Fin 2) (integralAdeles K)) :
    (localMat K w (mapO κ)).det⁻¹ ∈ w.integers := by
  have h : localMat K w (mapO κ) * localMat K w (mapO κ⁻¹) = 1 := by
    rw [← localMat_mul, ← map_mul, mul_inv_cancel, map_one, localMat_one]
  have h' := congrArg Matrix.det h
  rw [det_mul, det_one] at h'
  rw [inv_eq_of_mul_eq_one_right h']
  exact (isIntMat_localMat_mapO w κ⁻¹).det_mem

/-- A matrix of adeles which is integral at every place, with inverse integral at every place,
lies in `GL₂(O)`. -/
public theorem exists_mapO_of_isIntMat (y : GL (Fin 2) (AdeleRing K))
    (h : ∀ w, IsIntMat w (localMat K w y)) (h' : ∀ w, IsIntMat w (localMat K w y⁻¹)) :
    ∃ κ : GL (Fin 2) (integralAdeles K), mapO κ = y := by
  let φ : Matrix (Fin 2) (Fin 2) (integralAdeles K) →+* Matrix (Fin 2) (Fin 2) (AdeleRing K) :=
    (integralAdeles K).subtype.mapMatrix
  let kM : Matrix (Fin 2) (Fin 2) (integralAdeles K) := Matrix.of fun i j =>
    ⟨(y : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j, fun w => h w i j⟩
  let kI : Matrix (Fin 2) (Fin 2) (integralAdeles K) := Matrix.of fun i j =>
    ⟨((y⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j,
      fun w => h' w i j⟩
  have hkM : φ kM = (y : Matrix (Fin 2) (Fin 2) (AdeleRing K)) := by ext i j; rfl
  have hkI : φ kI = ((y⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) := by
    ext i j; rfl
  have hinj : Function.Injective φ := Matrix.map_injective Subtype.val_injective
  have h1 : kM * kI = 1 := hinj (by
    rw [map_mul, map_one, hkM, hkI, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one])
  have h2 : kI * kM = 1 := hinj (by
    rw [map_mul, map_one, hkM, hkI, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one])
  exact ⟨⟨kM, kI, h1, h2⟩, Units.ext hkM⟩

/-- The `q + 1` matrices of the Hecke operator as one family indexed by `Option (Fin q)`. -/
public def heckeFamily {q : ℕ} (g₀ : GL (Fin 2) (AdeleRing K))
    (g : Fin q → GL (Fin 2) (AdeleRing K)) :
    Option (Fin q) → GL (Fin 2) (AdeleRing K) := fun j => Option.elim j g₀ g

/-- `T_v f (x)` is the sum of `f (gⱼ x)` over the family `heckeFamily g₀ g`. -/
public theorem heckeOperator_eq_sum {Λ : Type w} [AddCommMonoid Λ] {q : ℕ}
    (g₀ : GL (Fin 2) (AdeleRing K)) (g : Fin q → GL (Fin 2) (AdeleRing K))
    (f : GL (Fin 2) (AdeleRing K) → Λ) (x : GL (Fin 2) (AdeleRing K)) :
    heckeOperator g₀ g f x = ∑ j, f (heckeFamily g₀ g j * x) := by
  rw [Fintype.sum_option]; rfl

variable {v : Place K} {q : ℕ} {π : v.integers} {lam : Fin q → v.integers}
  {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)}

/-- The component at `v` of `gⱼ` is the local Hecke matrix `M_j`, and its component at every
other place is the identity. -/
public theorem localMat_heckeFamily (hd : IsHeckeDataAt v π lam g₀ g)
    (j : Option (Fin q)) :
    localMat K v (heckeFamily g₀ g j) =
        heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) j ∧
      ∀ w, w ≠ v → localMat K w (heckeFamily g₀ g j) = 1 := by
  cases j with
  | none =>
    refine ⟨?_, fun w hw => ?_⟩
    · ext i j
      refine (hd.diagonal.1 i j).trans ?_
      fin_cases i <;> fin_cases j <;> simp [heckeLocal]
    · ext i j
      exact hd.diagonal.2 w hw i j
  | some l =>
    refine ⟨?_, fun w hw => ?_⟩
    · ext i j
      exact (hd.coset l).1 i j
    · ext i j
      exact (hd.coset l).2 w hw i j

/-- The permutation of the cosets induced by `κ ∈ GL₂(O)`. -/
public def heckePerm (hd : IsHeckeDataAt v π lam g₀ g) (κ : GL (Fin 2) (integralAdeles K)) :
    Option (Fin q) → Option (Fin q) :=
  heckeSel hd.isResidueSystem (localMat K v (mapO κ)) (isIntMat_localMat_mapO v κ)

/-- The inverse of the local Hecke matrix `M_j` is `heckeLocalInv`. -/
public theorem inv_heckeLocal (hπ0 : (π : v.completion) ≠ 0) (j : Option (Fin q)) :
    (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) j)⁻¹ =
      heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) j :=
  Matrix.inv_eq_right_inv (heckeLocal_mul_inv hπ0 _ j)

/-- The components of `gⱼ κ g_{j'}⁻¹`: at `v` it is `M_j κ_v M_{j'}⁻¹`, elsewhere it is `κ_w`. -/
private theorem localMat_heckeFamily_mul_mapO_mul_inv (hd : IsHeckeDataAt v π lam g₀ g)
    (hπ0 : (π : v.completion) ≠ 0) (κ : GL (Fin 2) (integralAdeles K)) (j j' : Option (Fin q)) :
    localMat K v (heckeFamily g₀ g j * mapO κ * (heckeFamily g₀ g j')⁻¹) =
        heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) j *
          localMat K v (mapO κ) *
          heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) j' ∧
      ∀ w, w ≠ v → localMat K w (heckeFamily g₀ g j * mapO κ * (heckeFamily g₀ g j')⁻¹) =
        localMat K w (mapO κ) := by
  refine ⟨?_, fun w hw => ?_⟩ <;> rw [localMat_mul, localMat_mul, localMat_inv]
  · rw [(localMat_heckeFamily hd j).1, (localMat_heckeFamily hd j').1, inv_heckeLocal hπ0]
  · rw [(localMat_heckeFamily hd j).2 w hw, (localMat_heckeFamily hd j').2 w hw, inv_one,
      Matrix.one_mul, Matrix.mul_one]

/-- Every component of `gⱼ κ g_{σ j}⁻¹` is integral, where `σ = heckePerm hd κ`. -/
public theorem isIntMat_localMat_heckePerm (hd : IsHeckeDataAt v π lam g₀ g)
    (hπ0 : (π : v.completion) ≠ 0) (κ : GL (Fin 2) (integralAdeles K)) (j : Option (Fin q))
    (w : Place K) : IsIntMat w (localMat K w (heckeFamily g₀ g j * mapO κ *
      (heckeFamily g₀ g (heckePerm hd κ j))⁻¹)) := by
  by_cases hw : w = v
  · subst hw
    rw [(localMat_heckeFamily_mul_mapO_mul_inv hd hπ0 κ _ _).1]
    exact isIntMat_heckeLocal_mul_mul hd.isUniformizer hπ0 hd.isResidueSystem _ j
  · rw [(localMat_heckeFamily_mul_mapO_mul_inv hd hπ0 κ _ _).2 w hw]
    exact isIntMat_localMat_mapO w κ

/-- Every component of `gⱼ κ g_{σ j}⁻¹` has integral inverse determinant, where
`σ = heckePerm hd κ`. -/
public theorem det_localMat_heckePerm_inv_mem (hd : IsHeckeDataAt v π lam g₀ g)
    (hπ0 : (π : v.completion) ≠ 0) (κ : GL (Fin 2) (integralAdeles K)) (j : Option (Fin q))
    (w : Place K) : (localMat K w (heckeFamily g₀ g j * mapO κ *
      (heckeFamily g₀ g (heckePerm hd κ j))⁻¹)).det⁻¹ ∈ w.integers := by
  by_cases hw : w = v
  · subst hw
    rw [(localMat_heckeFamily_mul_mapO_mul_inv hd hπ0 κ _ _).1, det_mul, det_mul, det_heckeLocal,
      det_heckeLocalInv, mul_right_comm, inv_mul_cancel₀ hπ0, one_mul]
    exact det_localMat_mapO_inv_mem w κ
  · rw [(localMat_heckeFamily_mul_mapO_mul_inv hd hπ0 κ _ _).2 w hw]
    exact det_localMat_mapO_inv_mem w κ

/-- `gⱼ κ g_{σ j}⁻¹` lies in `GL₂(O)`, where `σ = heckePerm hd κ`. -/
public theorem exists_mapO_heckePerm (hd : IsHeckeDataAt v π lam g₀ g)
    (hπ0 : (π : v.completion) ≠ 0) (κ : GL (Fin 2) (integralAdeles K)) (j : Option (Fin q)) :
    ∃ κ' : GL (Fin 2) (integralAdeles K), mapO κ' = heckeFamily g₀ g j * mapO κ *
      (heckeFamily g₀ g (heckePerm hd κ j))⁻¹ :=
  exists_mapO_of_isIntMat _ (isIntMat_localMat_heckePerm hd hπ0 κ j) fun w => by
    rw [localMat_inv]
    exact (isIntMat_localMat_heckePerm hd hπ0 κ j w).inv
      (det_localMat_heckePerm_inv_mem hd hπ0 κ j w)

/-- If `gⱼ g_{j'}⁻¹` lies in `GL₂(O)`, then `M_j M_{j'}⁻¹` is integral. -/
public theorem isIntMat_heckeLocal_of_mapO (hd : IsHeckeDataAt v π lam g₀ g)
    (hπ0 : (π : v.completion) ≠ 0) {j j' : Option (Fin q)} {κ : GL (Fin 2) (integralAdeles K)}
    (h : mapO κ = heckeFamily g₀ g j * (heckeFamily g₀ g j')⁻¹) :
    IsIntMat v (heckeLocal v (π : v.completion) (fun i => (lam i : v.completion)) j *
      heckeLocalInv v (π : v.completion) (fun i => (lam i : v.completion)) j') := by
  have hI := isIntMat_localMat_mapO v κ
  rw [h, localMat_mul, localMat_inv, (localMat_heckeFamily hd j).1,
    (localMat_heckeFamily hd j').1, inv_heckeLocal hπ0] at hI
  exact hI

/-- The map `heckePerm hd κ` on the cosets is injective. -/
public theorem heckePerm_injective (hd : IsHeckeDataAt v π lam g₀ g)
    (hπ0 : (π : v.completion) ≠ 0) (κ : GL (Fin 2) (integralAdeles K)) :
    Function.Injective (heckePerm hd κ) := by
  intro j j' hjj'
  obtain ⟨κ₁, h₁⟩ := exists_mapO_heckePerm hd hπ0 κ j
  obtain ⟨κ₂, h₂⟩ := exists_mapO_heckePerm hd hπ0 κ j'
  have h12 : mapO (κ₁ * κ₂⁻¹) = heckeFamily g₀ g j * (heckeFamily g₀ g j')⁻¹ := by
    rw [map_mul, map_inv, h₁, h₂, hjj']; group
  exact eq_of_isIntMat_heckeLocal_mul_inv hd.isUniformizer hπ0 hd.isResidueSystem
    (isIntMat_heckeLocal_of_mapO hd hπ0 h12)

/-- Right multiplication by `κ ∈ GL₂(O)` permutes the cosets `GL₂(O) gⱼ`:
`gⱼ κ = κ'ⱼ g_{σ j}` for a permutation `σ`. -/
public theorem exists_equiv_heckeFamily (hd : IsHeckeDataAt v π lam g₀ g)
    (hπ0 : (π : v.completion) ≠ 0) (κ : GL (Fin 2) (integralAdeles K)) :
    ∃ σ : Option (Fin q) ≃ Option (Fin q), ∀ j, ∃ κ' : GL (Fin 2) (integralAdeles K),
      heckeFamily g₀ g j * mapO κ = mapO κ' * heckeFamily g₀ g (σ j) := by
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (heckePerm_injective hd hπ0 κ)),
    fun j => ?_⟩
  obtain ⟨κ', h'⟩ := exists_mapO_heckePerm hd hπ0 κ j
  exact ⟨κ', by rw [Equiv.ofBijective_apply, h', inv_mul_cancel_right]⟩

/-- `T_v f` is left `GL₂(O)`-invariant when `f` is. -/
public theorem heckeOperator_left_invariant {Λ : Type w} [AddCommMonoid Λ]
    (hd : IsHeckeDataAt v π lam g₀ g) (hπ0 : (π : v.completion) ≠ 0)
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : ∀ κ x, f (mapO κ * x) = f x)
    (κ : GL (Fin 2) (integralAdeles K)) (x : GL (Fin 2) (AdeleRing K)) :
    heckeOperator g₀ g f (mapO κ * x) = heckeOperator g₀ g f x := by
  obtain ⟨σ, hσ⟩ := exists_equiv_heckeFamily hd hπ0 κ
  rw [heckeOperator_eq_sum, heckeOperator_eq_sum,
    ← Equiv.sum_comp σ (fun j => f (heckeFamily g₀ g j * x))]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨κ', hκ'⟩ := hσ j
  rw [← mul_assoc, hκ', mul_assoc, hf]

/-- `T_v f` is right `GL₂(K)`-invariant when `f` is. -/
public theorem heckeOperator_right_invariant {Λ : Type w} [AddCommMonoid Λ]
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : ∀ γ x, f (x * mapK γ) = f x)
    (γ : GL (Fin 2) (principalAdeles K)) (x : GL (Fin 2) (AdeleRing K)) :
    heckeOperator g₀ g f (x * mapK γ) = heckeOperator g₀ g f x := by
  simp only [heckeOperator, ← mul_assoc, hf]

/-- The data of `U_w` is central in `GL₂(A)`. -/
public theorem mul_comm_of_isCentralDataAt {w : Place K} {a : GL (Fin 2) (AdeleRing K)}
    (ha : IsCentralDataAt w a) (y : GL (Fin 2) (AdeleRing K)) : a * y = y * a := by
  obtain ⟨ϖ, -, h1, h2⟩ := ha
  refine localMat_ext fun w' => ?_
  rw [localMat_mul, localMat_mul]
  have hc : ∃ c, localMat K w' a = Matrix.diagonal fun _ => c := by
    by_cases hw : w' = w
    · subst hw; exact ⟨_, by ext i j; exact h1 i j⟩
    · exact ⟨1, by rw [diagonal_one]; ext i j; exact h2 w' hw i j⟩
  obtain ⟨c, hc⟩ := hc
  rw [hc]
  ext i j
  simp [diagonal_mul, mul_diagonal, _root_.mul_comm]

/-- `T_v f` satisfies the central condition when `f` does. -/
public theorem heckeOperator_central {Λ : Type w} [CommRing Λ] {f : GL (Fin 2) (AdeleRing K) → Λ}
    {w : Place K} {a : GL (Fin 2) (AdeleRing K)} (ha : IsCentralDataAt w a)
    (hf : ∀ x, (Place.residueCard w : Λ) * centralOperator a f x = f x)
    (x : GL (Fin 2) (AdeleRing K)) :
    (Place.residueCard w : Λ) * centralOperator a (heckeOperator g₀ g f) x =
      heckeOperator g₀ g f x := by
  simp only [centralOperator, heckeOperator, mul_add, Finset.mul_sum]
  have key : ∀ y : GL (Fin 2) (AdeleRing K), (Place.residueCard w : Λ) * f (y * (a * x)) =
      f (y * x) := fun y => by
    rw [← mul_assoc, ← mul_comm_of_isCentralDataAt ha y, mul_assoc]; exact hf (y * x)
  simp only [key]

/-- `T_v` is additive in `f`. -/
public theorem heckeOperator_add {Λ : Type w} [AddCommMonoid Λ]
    (f₁ f₂ : GL (Fin 2) (AdeleRing K) → Λ) :
    heckeOperator g₀ g (f₁ + f₂) = heckeOperator g₀ g f₁ + heckeOperator g₀ g f₂ := by
  funext x
  simp only [heckeOperator, Pi.add_apply, Finset.sum_add_distrib]
  abel

/-- `T_v` is linear in `f`. -/
public theorem heckeOperator_smul {Λ : Type w} [CommRing Λ] (c : Λ)
    (f : GL (Fin 2) (AdeleRing K) → Λ) :
    heckeOperator g₀ g (c • f) = c • heckeOperator g₀ g f := by
  funext x
  simp only [heckeOperator, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]

/-- `T_v 0 = 0`. -/
public theorem heckeOperator_zero {Λ : Type w} [AddCommMonoid Λ] :
    heckeOperator g₀ g (0 : GL (Fin 2) (AdeleRing K) → Λ) = 0 := by
  funext x
  simp [heckeOperator]

end Global

section WithK

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k

/-- A uniformizer at a place of a function field is nonzero. -/
public theorem coe_ne_zero_of_isUniformizer {v : Place K} {π : v.integers}
    (hπ : Place.IsUniformizer v π) : (π : v.completion) ≠ 0 := by
  intro h0
  have hv := isDiscrete k v
  have hπ' : π = 0 := Subtype.ext h0
  have h1 : (⟨v.coeRingHom v.unif, Place.coeRingHom_unif_mem_integers hv⟩ : v.integers) ∈
      Ideal.span {π} := by
    rw [hπ, ← Place.isUniformizer_unif hv]
    exact Ideal.subset_span rfl
  rw [hπ', Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at h1
  exact Place.unif_ne_zero hv ((map_eq_zero _).1 (congrArg Subtype.val h1))

/-- `K + U` has finite index in `A` for every open subgroup `U`. -/
public theorem index_principal_sup_ne_zero {U : AddSubgroup (AdeleRing K)}
    (hU : IsOpen (U : Set (AdeleRing K))) : ((principalAdeles K).toAddSubgroup ⊔ U).index ≠ 0 := by
  obtain ⟨E, hE⟩ := exists_adeleLattice_le_of_isOpen k hU
  intro h0
  have hle : (principalAdeles K).toAddSubgroup ⊔ adeleLattice K E ≤
      (principalAdeles K).toAddSubgroup ⊔ U := sup_le_sup_left hE _
  have := AddSubgroup.relIndex_mul_index hle
  rw [h0, mul_zero, principalAdeles_toAddSubgroup k] at this
  exact hOne_ne_zero k E this.symm

variable {v : Place K} {q : ℕ} {π : v.integers} {lam : Fin q → v.integers}
  {g₀ : GL (Fin 2) (AdeleRing K)} {g : Fin q → GL (Fin 2) (AdeleRing K)}

/-- `T_v` maps unramified cusp forms to unramified cusp forms when `p` is invertible in `Λ`. -/
public theorem heckeOperator_isUnramifiedCuspForm {Λ : Type w} [CommRing Λ]
    (hp : IsUnit (ringChar k : Λ)) (hd : IsHeckeDataAt v π lam g₀ g)
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspForm f) :
    IsUnramifiedCuspForm (heckeOperator g₀ g f) := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hd.isUniformizer
  have hL : ∀ κ x, heckeOperator g₀ g f (mapO κ * x) = heckeOperator g₀ g f x :=
    heckeOperator_left_invariant hd hπ0 (fun κ x => hf.left_invariant x κ)
  have hR : ∀ γ x, heckeOperator g₀ g f (x * mapK γ) = heckeOperator g₀ g f x :=
    heckeOperator_right_invariant (fun γ x => hf.right_invariant x γ)
  refine ⟨fun x γ => hR γ x, fun x κ => hL κ x, fun x U hU hinv s hs => ?_⟩
  let U' : AddSubgroup (AdeleRing K) := U ⊓ ⨅ j, stabSubgroup K (heckeFamily g₀ g j * x)
  have hU' : IsOpen (U' : Set (AdeleRing K)) := by
    simp only [U', AddSubgroup.coe_inf, AddSubgroup.coe_iInf]
    exact hU.inter (isOpen_iInter_of_finite fun j => isOpen_stabSubgroup _)
  have hZ : ∀ s₀ : Finset (AdeleRing K),
      (∀ a, ∃! z ∈ s₀, a - z ∈ (principalAdeles K).toAddSubgroup ⊔ U') →
      ∑ z ∈ s₀, heckeOperator g₀ g f (x * GeneralLinearGroup.upperRightHom z) = 0 := by
    intro s₀ hs₀
    simp only [heckeOperator_eq_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [← mul_assoc]
    exact hf.vanishing_constant_term (heckeFamily g₀ g j * x) U' hU'
      (fun z y hy => left_inv_upperRight_add (fun κ x => hf.left_invariant x κ) _ z
        (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_inf.1 hy).2 j)) s₀ hs₀
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  have hW : ∀ z, ∀ y ∈ (principalAdeles K).toAddSubgroup ⊔ U,
      heckeOperator g₀ g f (x * GeneralLinearGroup.upperRightHom (z + y)) =
        heckeOperator g₀ g f (x * GeneralLinearGroup.upperRightHom z) :=
    fun z y hy => integrand_add_mem_sup k hR x hinv z hy
  have hle : (principalAdeles K).toAddSubgroup ⊔ U' ≤ (principalAdeles K).toAddSubgroup ⊔ U :=
    sup_le_sup_left inf_le_left _
  exact sum_eq_zero_of_finer k (ringChar_nsmul_adele k (K := K)) hp hle le_rfl
    (index_principal_sup_ne_zero k hU') hW (fun z y hy => hW z y (hle hy)) hZ hs

/-- `T_v` preserves the unramified cusp forms with central character. -/
public theorem isCuspFormCentralChar_heckeOperator {Λ : Type w} [CommRing Λ]
    (hp : IsUnit (ringChar k : Λ)) (hd : IsHeckeDataAt v π lam g₀ g)
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : IsCuspFormCentralChar Λ f) :
    IsCuspFormCentralChar Λ (heckeOperator g₀ g f) :=
  ⟨heckeOperator_isUnramifiedCuspForm k hp hd hf.1,
    fun _ _ ha x => heckeOperator_central ha (hf.2 _ _ ha) x⟩

/-- `T_v` maps `C(Λ)` to itself. -/
public theorem heckeOperator_mem_cuspFormsCentralChar {Λ : Type w} [CommRing Λ]
    (hp : IsUnit (ringChar k : Λ)) (hd : IsHeckeDataAt v π lam g₀ g)
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : f ∈ cuspFormsCentralChar K Λ) :
    heckeOperator g₀ g f ∈ cuspFormsCentralChar K Λ := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact mem_cuspFormsCentralChar (isCuspFormCentralChar_heckeOperator k hp hd hf)
  | zero => rw [heckeOperator_zero]; exact zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ => rw [heckeOperator_add]; exact add_mem h₁ h₂
  | smul c f _ h => rw [heckeOperator_smul]; exact Submodule.smul_mem _ _ h

/-- The Hecke operator `T_v` as a `Λ`-linear endomorphism of `C(Λ)`. -/
public def cuspFormsHecke (Λ : Type w) [CommRing Λ] (hp : IsUnit (ringChar k : Λ))
    (hd : IsHeckeDataAt v π lam g₀ g) :
    cuspFormsCentralChar K Λ →ₗ[Λ] cuspFormsCentralChar K Λ where
  toFun f := ⟨heckeOperator g₀ g f, heckeOperator_mem_cuspFormsCentralChar k hp hd f.2⟩
  map_add' _ _ := Subtype.ext (heckeOperator_add _ _)
  map_smul' c _ := Subtype.ext (heckeOperator_smul c _)

/-- The underlying function of `cuspFormsHecke k Λ hp hd f` is `T_v f`. -/
@[simp]
public theorem coe_cuspFormsHecke (Λ : Type w) [CommRing Λ] (hp : IsUnit (ringChar k : Λ))
    (hd : IsHeckeDataAt v π lam g₀ g) (f : cuspFormsCentralChar K Λ) :
    ((cuspFormsHecke k Λ hp hd f : cuspFormsCentralChar K Λ) : GL (Fin 2) (AdeleRing K) → Λ) =
      heckeOperator g₀ g f := rfl

variable {F Λ : Type w} [Field F] [Field Λ] [Algebra F Λ]

/-- The base change map `Λ ⊗_F C(F) → C(Λ)` intertwines `id ⊗ T_v` and `T_v`. -/
public theorem cuspFormsBaseChange_comp_baseChange_hecke (hp : IsUnit (ringChar k : Λ))
    (hd : IsHeckeDataAt v π lam g₀ g) :
    (cuspFormsBaseChange K F Λ).comp
        (LinearMap.baseChange Λ (cuspFormsHecke k F (isUnit_ringChar_of_algebra k hp) hd)) =
      (cuspFormsHecke k Λ hp hd).comp (cuspFormsBaseChange K F Λ) := by
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c f =>
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
      cuspFormsBaseChange_tmul, cuspFormsBaseChange_tmul, map_smul]
    congr 1
    refine Subtype.ext (funext fun x => ?_)
    exact (heckeOperator_mapCoeffs (algebraMap F Λ) g₀ g _ x).symm
  | add a b ha hb =>
    exact (LinearMap.map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
      (LinearMap.map_add _ a b).symm)

/-- The base change isomorphism `Λ ⊗_F C(F) ≃ C(Λ)`, `c ⊗ f ↦ c · (ι ∘ f)`, when `p` is
invertible in `Λ`. -/
public def cuspFormsBaseChangeEquiv (hp : IsUnit (ringChar k : Λ)) :
    TensorProduct F Λ (cuspFormsCentralChar K F) ≃ₗ[Λ] cuspFormsCentralChar K Λ :=
  LinearEquiv.ofBijective (cuspFormsBaseChange K F Λ)
    ⟨cuspFormsBaseChange_injective F Λ, cuspFormsBaseChange_surjective k hp⟩

/-- The base change isomorphism sends `c ⊗ f` to `c · (ι ∘ f)`. -/
public theorem cuspFormsBaseChangeEquiv_tmul (hp : IsUnit (ringChar k : Λ)) (c : Λ)
    (f : cuspFormsCentralChar K F) :
    ((cuspFormsBaseChangeEquiv k hp (c ⊗ₜ f) : cuspFormsCentralChar K Λ) :
      GL (Fin 2) (AdeleRing K) → Λ) = c • mapCoeffs (algebraMap F Λ) f := by
  show ((cuspFormsBaseChange K F Λ (c ⊗ₜ f) : cuspFormsCentralChar K Λ) :
    GL (Fin 2) (AdeleRing K) → Λ) = _
  rw [cuspFormsBaseChange_tmul]
  rfl

/-- The underlying linear map of `cuspFormsBaseChangeEquiv` is `cuspFormsBaseChange`. -/
public theorem cuspFormsBaseChangeEquiv_toLinearMap (hp : IsUnit (ringChar k : Λ)) :
    (cuspFormsBaseChangeEquiv k hp (F := F) (K := K)).toLinearMap = cuspFormsBaseChange K F Λ :=
  LinearMap.ext fun _ => rfl

end WithK

end Stacks.Adeles.GlobalFunctionField

end
