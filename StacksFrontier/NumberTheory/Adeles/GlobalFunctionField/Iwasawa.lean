module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.Ideles

/-!
# The Iwasawa decomposition `GL₂(A) = GL₂(O) · B(A)`

Every `x ∈ GL₂(A)` is `k · b` with `k ∈ GL₂(O)` and `b` upper triangular. At each place this is
row reduction over the valuation ring `O_v`; the local matrices have integral entries at every
place, so they assemble to an element of `GL₂(O)`.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.upperGL` — the upper triangular matrix `(α, β; 0, δ)` with
  `α, δ` units.

## Main results

* `Stacks.Adeles.GlobalFunctionField.exists_iwasawa` — `x = k · (α, β; 0, δ)`.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Adeles.GlobalFunctionField

variable {K : Type u} [Field K]

/-- The upper triangular matrix `(α, β; 0, δ)` with unit diagonal entries. -/
public def upperGL (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) : GL (Fin 2) (AdeleRing K) where
  val := !![(α : AdeleRing K), β; 0, (δ : AdeleRing K)]
  inv := !![((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K),
    -(((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β * ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)); 0,
    ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)]
  val_inv := by
    rw [mul_fin_two, one_fin_two]
    congr 1
    simp [mul_assoc]
  inv_val := by
    rw [mul_fin_two, one_fin_two]
    congr 1
    simp [mul_assoc]

/-- The underlying matrix of `upperGL α δ β` is `(α, β; 0, δ)`. -/
@[simp]
public theorem coe_upperGL (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) :
    ((upperGL α δ β : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) =
      !![(α : AdeleRing K), β; 0, (δ : AdeleRing K)] := rfl

/-- An invertible upper triangular matrix is `upperGL α δ β`. -/
public theorem exists_eq_upperGL {b : GL (Fin 2) (AdeleRing K)}
    (hb : (b : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 1 0 = 0) :
    ∃ α δ : (AdeleRing K)ˣ, ∃ β : AdeleRing K, b = upperGL α δ β := by
  have hdet : IsUnit (b : Matrix (Fin 2) (Fin 2) (AdeleRing K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
  rw [det_fin_two, hb, mul_zero, sub_zero] at hdet
  obtain ⟨α, hα⟩ := isUnit_of_mul_isUnit_left hdet
  obtain ⟨δ, hδ⟩ := isUnit_of_mul_isUnit_right hdet
  refine ⟨α, δ, (b : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hα, hδ, hb]

section Local

variable (v : Place K)

open scoped Classical in
/-- The local reduction matrix at `v` and its inverse: with integral entries, and such that
`kInv * g` has vanishing `(1, 0)` entry. -/
public def localRed (g : Matrix (Fin 2) (Fin 2) v.completion) :
    Matrix (Fin 2) (Fin 2) v.completion × Matrix (Fin 2) (Fin 2) v.completion :=
  if g 1 0 = 0 then (1, 1)
  else if Valued.v (g 1 0) ≤ Valued.v (g 0 0) then
    (!![1, 0; g 1 0 / g 0 0, 1], !![1, 0; -(g 1 0 / g 0 0), 1])
  else (!![g 0 0 / g 1 0, 1; 1, 0], !![0, 1; 1, -(g 0 0 / g 1 0)])

private theorem div_mem_integers_of_valued_le {a b : v.completion} (h : Valued.v a ≤ Valued.v b)
    (hb : b ≠ 0) : a / b ∈ v.integers := by
  refine (Valuation.mem_valuationSubring_iff _ _).2 ?_
  rwa [map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb))]

private theorem ne_zero_of_valued_le {a b : v.completion} (ha : a ≠ 0)
    (h : Valued.v a ≤ Valued.v b) : b ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact ha ((Valuation.zero_iff _).1 (le_antisymm h zero_le))

/-- The local reduction matrix has integral entries. -/
public theorem localRed_fst_mem (g : Matrix (Fin 2) (Fin 2) v.completion) (i j : Fin 2) :
    (localRed v g).1 i j ∈ v.integers := by
  classical
  unfold localRed
  split_ifs with h1 h2
  · simp only [one_apply]
    split_ifs <;> [exact v.integers.one_mem; exact v.integers.zero_mem]
  · have hg0 := ne_zero_of_valued_le v h1 h2
    have hm := div_mem_integers_of_valued_le v h2 hg0
    fin_cases i <;> fin_cases j <;> simp [v.integers.one_mem, v.integers.zero_mem, hm]
  · have hm := div_mem_integers_of_valued_le v (not_le.1 h2).le h1
    fin_cases i <;> fin_cases j <;> simp [v.integers.one_mem, v.integers.zero_mem, hm]

/-- The inverse of the local reduction matrix has integral entries. -/
public theorem localRed_snd_mem (g : Matrix (Fin 2) (Fin 2) v.completion) (i j : Fin 2) :
    (localRed v g).2 i j ∈ v.integers := by
  classical
  unfold localRed
  split_ifs with h1 h2
  · simp only [one_apply]
    split_ifs <;> [exact v.integers.one_mem; exact v.integers.zero_mem]
  · have hg0 := ne_zero_of_valued_le v h1 h2
    have hm := neg_mem (div_mem_integers_of_valued_le v h2 hg0)
    fin_cases i <;> fin_cases j <;> simp [v.integers.one_mem, v.integers.zero_mem, hm]
  · have hm := neg_mem (div_mem_integers_of_valued_le v (not_le.1 h2).le h1)
    fin_cases i <;> fin_cases j <;> simp [v.integers.one_mem, v.integers.zero_mem, hm]

/-- The local reduction matrix times its inverse is `1`. -/
public theorem localRed_mul (g : Matrix (Fin 2) (Fin 2) v.completion) :
    (localRed v g).1 * (localRed v g).2 = 1 := by
  classical
  unfold localRed
  split_ifs with h1 h2
  · simp
  · rw [mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The inverse of the local reduction matrix times the local reduction matrix is `1`. -/
public theorem localRed_mul' (g : Matrix (Fin 2) (Fin 2) v.completion) :
    (localRed v g).2 * (localRed v g).1 = 1 :=
  mul_eq_one_comm.1 (localRed_mul v g)

/-- Multiplying `g` on the left by the inverse of the local reduction matrix kills the `(1, 0)`
entry. -/
public theorem localRed_snd_mul_apply (g : Matrix (Fin 2) (Fin 2) v.completion) :
    ((localRed v g).2 * g) 1 0 = 0 := by
  classical
  rw [mul_apply, Fin.sum_univ_two]
  unfold localRed
  split_ifs with h1 h2
  · simp [h1]
  · have hg0 := ne_zero_of_valued_le v h1 h2
    simp
    field_simp
    ring
  · simp
    field_simp
    ring

end Local

variable (K) in
/-- Evaluation of adeles at a place. -/
public abbrev evalAt (v : Place K) : AdeleRing K →+* v.completion :=
  RestrictedProduct.evalRingHom _ v

/-- Two adelic matrices with the same components at every place are equal. -/
public theorem matrix_ext_evalAt {M N : Matrix (Fin 2) (Fin 2) (AdeleRing K)}
    (h : ∀ v, (evalAt K v).mapMatrix M = (evalAt K v).mapMatrix N) : M = N := by
  ext i j v
  exact congrFun (congrFun (h v) i) j

/-- **Iwasawa decomposition**: every `x ∈ GL₂(A)` is `k · (α, β; 0, δ)` with `k ∈ GL₂(O)`. -/
public theorem exists_iwasawa (x : GL (Fin 2) (AdeleRing K)) :
    ∃ (κ : GL (Fin 2) (integralAdeles K)) (α δ : (AdeleRing K)ˣ) (β : AdeleRing K),
      x = GeneralLinearGroup.map (integralAdeles K).subtype κ * upperGL α δ β := by
  set g : ∀ v : Place K, Matrix (Fin 2) (Fin 2) v.completion :=
    fun v => (evalAt K v).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing K))
  let φ : Matrix (Fin 2) (Fin 2) (integralAdeles K) →+* Matrix (Fin 2) (Fin 2) (AdeleRing K) :=
    (integralAdeles K).subtype.mapMatrix
  let kM : Matrix (Fin 2) (Fin 2) (integralAdeles K) := Matrix.of fun i j =>
    ⟨⟨fun v => (localRed v (g v)).1 i j, Filter.Eventually.of_forall fun v =>
      localRed_fst_mem v (g v) i j⟩, fun v => localRed_fst_mem v (g v) i j⟩
  let kI : Matrix (Fin 2) (Fin 2) (integralAdeles K) := Matrix.of fun i j =>
    ⟨⟨fun v => (localRed v (g v)).2 i j, Filter.Eventually.of_forall fun v =>
      localRed_snd_mem v (g v) i j⟩, fun v => localRed_snd_mem v (g v) i j⟩
  have hkM : ∀ v, (evalAt K v).mapMatrix (φ kM) =
      (localRed v (g v)).1 := fun v => by ext i j; rfl
  have hkI : ∀ v, (evalAt K v).mapMatrix (φ kI) =
      (localRed v (g v)).2 := fun v => by ext i j; rfl
  have hinj : Function.Injective φ := by
    intro M N h
    ext i j v
    exact congrArg (fun a : AdeleRing K => a v) (congrFun (congrFun h i) j)
  have h1 : kM * kI = 1 := hinj (by
    rw [map_mul, map_one]
    exact matrix_ext_evalAt fun v => by rw [map_mul, hkM, hkI, localRed_mul, map_one])
  let κ : GL (Fin 2) (integralAdeles K) := ⟨kM, kI, h1, mul_eq_one_comm.1 h1⟩
  set b := (GeneralLinearGroup.map (integralAdeles K).subtype κ)⁻¹ * x
  have hb : (b : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 1 0 = 0 := by
    have hbM : (b : Matrix (Fin 2) (Fin 2) (AdeleRing K)) =
        φ kI * (x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) := by
      simp only [b, Matrix.GeneralLinearGroup.coe_mul, ← map_inv]
      rfl
    rw [hbM]
    refine RestrictedProduct.ext _ _ fun v => ?_
    have := congrFun (congrFun (show (evalAt K v).mapMatrix
        (φ kI * (x : Matrix (Fin 2) (Fin 2) (AdeleRing K))) = (localRed v (g v)).2 * g v by
      rw [map_mul, hkI]) 1) 0
    rwa [localRed_snd_mul_apply] at this
  obtain ⟨α, δ, β, hαδ⟩ := exists_eq_upperGL hb
  exact ⟨κ, α, δ, β, by rw [← hαδ, mul_inv_cancel_left]⟩

end Stacks.Adeles.GlobalFunctionField

end
