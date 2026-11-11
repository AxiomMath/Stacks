module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.ReductionIwasawa
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsFinite
public import StacksFrontier.NumberTheory.Drinfeld.UnitEigenform

/-!
# Reduction theory for `GL_n` of the adeles of a global function field

Let `K` be a global function field over the finite field `k`, `A` its adele ring and `O` the
integral adeles. We prove `Stacks.Adeles.GeneralLinear.ReductionTheory K n k` for every `n`: every
`x ∈ GL_n(A)` is `κ b γ` with `κ ∈ GL_n(O)`, `γ ∈ GL_n(K)` and `b` upper triangular whose
diagonal entries satisfy `c₀ ≤ N(div a_i - div a_{i+1})`, with `c₀` the reduction constant of
`GL₂` (`Stacks.Adeles.GlobalFunctionField.redConst`).

The proof is by induction on `n`. The decompositions `x = κ b γ` with `b` upper triangular exist
by the Iwasawa decomposition, and the degree of `div a_0` is bounded above on them: the first
column of `γ⁻¹ = x⁻¹ κ b` is `a_0` times an adelic vector with bounded poles, and it has a nonzero
entry in `K`. Choose a decomposition with `deg (div a_0)` maximal and reduce the lower right block
by induction. If `N(div a_0 - div a_1) < c₀`, the reduction of `GL₂` applied to the upper left
`2 × 2` block gives another decomposition with first diagonal entry `α`, where
`N(div α - div δ) ≥ c₀` and `N(div α) N(div δ) = N(div a_0) N(div a_1)` (product formula), hence
`N(div α) > N(div a_0)`, contradicting maximality.

## Main results

* `Stacks.Adeles.GeneralLinear.exists_degree_bound` — the bound on `deg (div a_0)`.
* `Stacks.Adeles.GeneralLinear.exists_reduction_step` — the reduction of the upper left block.
* `Stacks.Adeles.GeneralLinear.reductionTheory` — reduction theory for `GL_n(A)`.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField (idelDiv divNorm adeleLattice redConst redConst_pos diag
  range_diag idelDiv_mul idelDiv_diagUnit diagUnit coe_diagUnit divNorm_principalDivisor
  idele_apply_ne_zero nonempty_place exists_mem_adeleLattice adeleLattice_mono
  integral_mul_mem_adeleLattice idele_mul_mem_adeleLattice_iff eq_zero_of_mem_of_divNorm_lt_one
  upperGL coe_upperGL det_upperGL idelDiv_det_mapO exists_reduction divNorm_add divNorm_pos
  divNorm_sub)

open Stacks.Drinfeld (divisorDegree divNorm_eq_zpow_divisorDegree)

variable {K : Type u} [Field K]

section DoubleCoset

variable {n : ℕ}

/-- `x ∈ GL_n(O) · b · GL_n(K)`. -/
public def SameDoubleCoset (x b : GL (Fin n) (AdeleRing K)) : Prop :=
  ∃ κ ∈ (mapO K n).range, ∃ γ ∈ (mapK K n).range, x = κ * b * γ

/-- `x ∈ GL_n(O) · x · GL_n(K)`. -/
public theorem SameDoubleCoset.refl (x : GL (Fin n) (AdeleRing K)) : SameDoubleCoset x x :=
  ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩

/-- Double cosets compose. -/
public theorem SameDoubleCoset.trans {x b b' : GL (Fin n) (AdeleRing K)}
    (h : SameDoubleCoset x b) (h' : SameDoubleCoset b b') : SameDoubleCoset x b' := by
  obtain ⟨κ, hκ, γ, hγ, rfl⟩ := h
  obtain ⟨κ', hκ', γ', hγ', rfl⟩ := h'
  exact ⟨κ * κ', mul_mem hκ hκ', γ' * γ, mul_mem hγ' hγ, by simp only [mul_assoc]⟩

end DoubleCoset

section Embeddings

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- `(g, 0; 0, 1)` comes from `GL(S)` when `g` does. -/
public theorem blockLeftGL_mem_range {S : Subring R} {g : GL (Fin m) R}
    (hg : g ∈ (GeneralLinearGroup.map S.subtype).range) :
    blockLeftGL R m n g ∈ (GeneralLinearGroup.map S.subtype).range := by
  rw [mem_range_map_subtype_iff] at hg ⊢
  refine ⟨blockMat_mem hg.1 (zero_mem_entries S) (zero_mem_entries S) (one_mem_entries S), ?_⟩
  rw [← map_inv, coe_blockLeftGL]
  exact blockMat_mem hg.2 (zero_mem_entries S) (zero_mem_entries S) (one_mem_entries S)

/-- `(1, 0; 0, g)` comes from `GL(S)` when `g` does. -/
public theorem blockRightGL_mem_range {S : Subring R} {g : GL (Fin n) R}
    (hg : g ∈ (GeneralLinearGroup.map S.subtype).range) :
    blockRightGL R m n g ∈ (GeneralLinearGroup.map S.subtype).range := by
  rw [mem_range_map_subtype_iff] at hg ⊢
  refine ⟨blockMat_mem (one_mem_entries S) (zero_mem_entries S) (zero_mem_entries S) hg.1, ?_⟩
  rw [← map_inv, coe_blockRightGL]
  exact blockMat_mem (one_mem_entries S) (zero_mem_entries S) (zero_mem_entries S) hg.2

/-- The determinant of an element of `GL(S)` lies in `S`. -/
public theorem val_det_mem_of_mem_range {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Subring R}
    {g : GL ι R} (hg : g ∈ (GeneralLinearGroup.map S.subtype).range) :
    ((GeneralLinearGroup.det g : Rˣ) : R) ∈ S := by
  obtain ⟨h, rfl⟩ := hg
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (S.subtype.mapMatrix (h : Matrix ι ι S)).det ∈ S
  rw [← RingHom.map_det]
  exact (h : Matrix ι ι S).det.2

end Embeddings

variable (k : Type u) [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

section Degree

/-- `N` and `deg` define the same order on divisors (strict form). -/
public theorem divNorm_lt_divNorm_iff (D D' : Place K →₀ ℤ) :
    divNorm K D < divNorm K D' ↔ divisorDegree k K D < divisorDegree k K D' := by
  have hq : (1 : ℚ) < Nat.card k := by
    have := Fintype.ofFinite k
    exact_mod_cast Finite.one_lt_card
  rw [divNorm_eq_zpow_divisorDegree k, divNorm_eq_zpow_divisorDegree k]
  exact zpow_lt_zpow_iff_right₀ hq

/-- An idele whose value is a principal adele has divisor of norm `1`. -/
public theorem divNorm_idelDiv_eq_one_of_mem {u : (AdeleRing K)ˣ}
    (hu : (u : AdeleRing K) ∈ principalAdeles K) : divNorm K (idelDiv k K u) = 1 := by
  rw [← range_diag k] at hu
  obtain ⟨c, hc⟩ := hu
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := nonempty_place k (K := K)
    exact idele_apply_ne_zero u v (by rw [← hc, map_zero]; rfl)
  have : u = diagUnit k hc0 := Units.ext (by rw [coe_diagUnit, hc])
  rw [this, idelDiv_diagUnit, divNorm_principalDivisor k hc0]

end Degree

section Bound

variable {n : ℕ}

omit [Finite k] in
include k in
/-- The adele ring is not the zero ring. -/
public theorem adeleRing_one_ne_zero : (1 : AdeleRing K) ≠ 0 := by
  intro h
  obtain ⟨v⟩ := nonempty_place k (K := K)
  exact one_ne_zero (congrArg (fun a : AdeleRing K => a v) h)

/-- **Bound on the first diagonal entry**: for `x ∈ GL_{n+1}(A)` the degree of `div a_0` is
bounded above on the decompositions `x = κ b γ` with `b` upper triangular of diagonal `a`. -/
public theorem exists_degree_bound (x : GL (Fin (n + 1)) (AdeleRing K)) :
    ∃ C : ℤ, ∀ (b : GL (Fin (n + 1)) (AdeleRing K)) (a : Fin (n + 1) → (AdeleRing K)ˣ),
      SameDoubleCoset x b → IsUpperTriangularWith b a →
        divisorDegree k K (idelDiv k K (a 0)) ≤ C := by
  classical
  choose D hD0 hD using fun i l => exists_mem_adeleLattice k
    (((x⁻¹ : GL (Fin (n + 1)) (AdeleRing K)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (AdeleRing K)) i l)
  set E := ∑ i, ∑ l, D i l
  have hDE : ∀ i l, D i l ≤ E := fun i l =>
    (Finset.single_le_sum (fun l' _ => hD0 i l') (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun i => ∑ l', D i l')
        (fun i' _ => Finset.sum_nonneg fun l' _ => hD0 i' l') (Finset.mem_univ i))
  refine ⟨divisorDegree k K E, fun b a hred hut => ?_⟩
  obtain ⟨κ, hκ, γ, hγ, hx⟩ := hred
  have hκO := ((mem_range_map_subtype_iff _ κ).1 hκ).1
  have hγK := ((mem_range_map_subtype_iff _ γ).1 hγ).2
  have hγinv : γ⁻¹ = x⁻¹ * κ * b := by rw [hx]; group
  -- the first column of `x⁻¹ κ` has bounded poles
  have hcolE : ∀ i, ((x⁻¹ * κ : GL (Fin (n + 1)) (AdeleRing K)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (AdeleRing K)) i 0 ∈ adeleLattice K E := by
    intro i
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    refine AddSubgroup.sum_mem _ fun l _ => ?_
    rw [mul_comm]
    exact integral_mul_mem_adeleLattice (hκO l 0) (adeleLattice_mono k (hDE i l) (hD i l))
  have hcol : ∀ i, ((γ⁻¹ : GL (Fin (n + 1)) (AdeleRing K)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (AdeleRing K)) i 0 = (a 0 : AdeleRing K) *
      ((x⁻¹ * κ : GL (Fin (n + 1)) (AdeleRing K)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (AdeleRing K)) i 0 := by
    intro i
    rw [hγinv, Matrix.GeneralLinearGroup.coe_mul _ b, Matrix.mul_apply,
      Finset.sum_eq_single (0 : Fin (n + 1)), hut.2, mul_comm]
    · intro l _ hl
      rw [hut.1 l 0 (Fin.pos_iff_ne_zero.2 hl), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- a nonzero entry of the first column of `γ⁻¹`
  obtain ⟨i, hi⟩ : ∃ i, ((γ⁻¹ : GL (Fin (n + 1)) (AdeleRing K)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (AdeleRing K)) i 0 ≠ 0 := by
    by_contra h
    push Not at h
    have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (γ⁻¹).isUnit
    rw [det_eq_zero_of_column_eq_zero 0 h, isUnit_zero_iff] at hdet
    exact adeleRing_one_ne_zero k hdet.symm
  obtain ⟨c, hc⟩ := (show _ ∈ (diag k K).range by rw [range_diag k]; exact hγK i 0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact hi hc.symm
  have hmem : diag k K c ∈ adeleLattice K (E - idelDiv k K (a 0)) := by
    rw [hc, hcol]
    exact (idele_mul_mem_adeleLattice_iff k (a 0)).2 (hcolE i)
  have hle : ¬ divNorm K (E - idelDiv k K (a 0)) < divNorm K 0 := fun hlt =>
    hc0 (eq_zero_of_mem_of_divNorm_lt_one k (by
      rwa [Stacks.Adeles.GlobalFunctionField.divNorm_zero] at hlt) hmem)
  rw [divNorm_lt_divNorm_iff k, map_sub, map_zero] at hle
  omega

end Bound

section Step

variable {n : ℕ}

/-- The determinant of an element of `GL₂(K)` has divisor of norm `1`. -/
public theorem divNorm_idelDiv_det_mapK (γ : GL (Fin 2) (principalAdeles K)) :
    divNorm K (idelDiv k K (GeneralLinearGroup.det
      (Stacks.Adeles.GlobalFunctionField.mapK γ))) = 1 :=
  divNorm_idelDiv_eq_one_of_mem k (val_det_mem_of_mem_range ⟨γ, rfl⟩)

/-- The reduction of `GL₂` increases the first diagonal entry when the gap is small: if
`N(div a₀ - div a₁) < c₀`, then `(a₀, β; 0, a₁) = κ (α, β'; 0, δ) γ` with `κ ∈ GL₂(O)`,
`γ ∈ GL₂(K)` and `N(div a₀) < N(div α)`. -/
public theorem exists_reduction_gl_two (a₀ a₁ : (AdeleRing K)ˣ) (β : AdeleRing K)
    (h : divNorm K (idelDiv k K a₀ - idelDiv k K a₁) < redConst k K) :
    ∃ (κ : GL (Fin 2) (integralAdeles K)) (γ : GL (Fin 2) (principalAdeles K))
      (α δ : (AdeleRing K)ˣ) (β' : AdeleRing K),
      upperGL a₀ a₁ β = Stacks.Adeles.GlobalFunctionField.mapO κ * upperGL α δ β' *
        Stacks.Adeles.GlobalFunctionField.mapK γ ∧
        divNorm K (idelDiv k K a₀) < divNorm K (idelDiv k K α) := by
  obtain ⟨κ, γ, α, δ, β', hy, hred⟩ := exists_reduction k (upperGL a₀ a₁ β)
  refine ⟨κ, γ, α, δ, β', hy, ?_⟩
  have hdet := congrArg (fun g => idelDiv k K (GeneralLinearGroup.det g)) hy
  simp only [map_mul, idelDiv_mul k, idelDiv_det_mapO k, zero_add] at hdet
  rw [det_upperGL, det_upperGL, idelDiv_mul k, idelDiv_mul k] at hdet
  have hN := congrArg (divNorm K) hdet
  rw [divNorm_add k, divNorm_add k, divNorm_add k, divNorm_idelDiv_det_mapK k, mul_one] at hN
  rw [divNorm_sub k] at h hred
  set X := divNorm K (idelDiv k K a₀)
  set Y := divNorm K (idelDiv k K a₁)
  set Z := divNorm K (idelDiv k K α)
  set W := divNorm K (idelDiv k K δ)
  have hX := divNorm_pos k (idelDiv k K a₀)
  have hY := divNorm_pos k (idelDiv k K a₁)
  have hZ := divNorm_pos k (idelDiv k K α)
  have hW := divNorm_pos k (idelDiv k K δ)
  have hlt : X / Y < Z / W := h.trans_le hred
  rw [div_lt_div_iff₀ hY hW] at hlt
  by_contra hle
  push Not at hle
  have h1 : Z * Y ≤ X * Y := mul_le_mul_of_nonneg_right hle hY.le
  have h2 : Y ≤ W := by nlinarith
  have h3 : X * Y ≤ X * W := mul_le_mul_of_nonneg_left h2 hX.le
  linarith

/-- The matrix `(α, β; 0, δ)` is upper triangular. -/
public theorem upperGL_upperTriangular (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) :
    ∀ i j : Fin 2, j < i →
      ((upperGL α δ β : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j =
        0 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd hij (lt_irrefl _)
  · exact absurd hij (by decide)
  · simp [coe_upperGL]
  · exact absurd hij (lt_irrefl _)

/-- The upper left `2 × 2` block of `b`, as an element of `GL₂(A)`. -/
public theorem blockMat_two_eq (b : GL (Fin (n + 2)) (AdeleRing K))
    (a : Fin (n + 2) → (AdeleRing K)ˣ) (hut : IsUpperTriangularWith b a) :
    (b : Matrix (Fin (n + 2)) (Fin (n + 2)) (AdeleRing K)) =
      blockMat ((upperGL (a 0) (a 1) ((b : Matrix (Fin (n + 2)) (Fin (n + 2)) (AdeleRing K)) 0 1) :
        GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K))
        (of fun i j => (b : Matrix (Fin (n + 2)) (Fin (n + 2)) (AdeleRing K))
          (blockEquiv 2 n (Sum.inl i)) (blockEquiv 2 n (Sum.inr j))) 0
        (of fun i j => (b : Matrix (Fin (n + 2)) (Fin (n + 2)) (AdeleRing K))
          (blockEquiv 2 n (Sum.inr i)) (blockEquiv 2 n (Sum.inr j))) := by
  set M := (b : Matrix (Fin (n + 2)) (Fin (n + 2)) (AdeleRing K))
  have e0 : blockEquiv 2 n (Sum.inl 0) = 0 := Fin.ext (by simp)
  have e1 : blockEquiv 2 n (Sum.inl 1) = 1 := Fin.ext (by simp)
  conv_lhs => rw [eq_blockMat (m := 2) (n := n) M]
  congr 1
  · refine Matrix.ext fun i j => ?_
    rw [of_apply, coe_upperGL]
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, e0, of_apply, cons_val', cons_val_zero, empty_val',
        cons_val_fin_one]
      exact hut.2 0
    · simp [e0, e1, M]
    · simp only [Fin.mk_one, Fin.isValue, e1, e0, Fin.zero_eta, of_apply, cons_val', cons_val_one,
        cons_val_zero, empty_val', cons_val_fin_one]
      exact hut.1 1 0 Fin.zero_lt_one
    · simp only [Fin.mk_one, Fin.isValue, e1, of_apply, cons_val', cons_val_one, empty_val',
        cons_val_fin_one]
      exact hut.2 1
  · refine Matrix.ext fun i j => ?_
    rw [of_apply, Matrix.zero_apply]
    exact hut.1 _ _ (Fin.lt_def.2 (by simp; omega))

/-- An invertible upper triangular matrix has unit diagonal entries. -/
public theorem exists_isUpperTriangularWith {n : ℕ} (b : GL (Fin n) (AdeleRing K))
    (hb : ∀ i j, j < i → (b : Matrix (Fin n) (Fin n) (AdeleRing K)) i j = 0) :
    ∃ a : Fin n → (AdeleRing K)ˣ, IsUpperTriangularWith b a :=
  ⟨fun i => (isUnit_diag_of_upperTriangular b hb i).unit,
    hb, fun i => (isUnit_diag_of_upperTriangular b hb i).unit_spec.symm⟩

/-- **The reduction step**: if `b ∈ GL_{n+2}(A)` is upper triangular with diagonal `a` and
`N(div a_0 - div a_1) < c₀`, there is `b₁ ∈ GL_{n+2}(O) b GL_{n+2}(K)` upper triangular with
diagonal `a'` and `N(div a_0) < N(div a'_0)`. -/
public theorem exists_reduction_step (b : GL (Fin (n + 2)) (AdeleRing K))
    (a : Fin (n + 2) → (AdeleRing K)ˣ) (hut : IsUpperTriangularWith b a)
    (h : divNorm K (idelDiv k K (a 0) - idelDiv k K (a 1)) < redConst k K) :
    ∃ (b₁ : GL (Fin (n + 2)) (AdeleRing K)) (a₁ : Fin (n + 2) → (AdeleRing K)ˣ),
      SameDoubleCoset b b₁ ∧ IsUpperTriangularWith b₁ a₁ ∧
        divNorm K (idelDiv k K (a 0)) < divNorm K (idelDiv k K (a₁ 0)) := by
  set R := AdeleRing K
  set M := (b : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
  obtain ⟨κ, γ, α, δ, β', hy, hlt⟩ := exists_reduction_gl_two k (a 0) (a 1) (M 0 1) h
  set κA := Stacks.Adeles.GlobalFunctionField.mapO κ
  set γA := Stacks.Adeles.GlobalFunctionField.mapK γ
  set B : Matrix (Fin 2) (Fin n) R :=
    of fun i j => M (blockEquiv 2 n (Sum.inl i)) (blockEquiv 2 n (Sum.inr j))
  set D : Matrix (Fin n) (Fin n) R :=
    of fun i j => M (blockEquiv 2 n (Sum.inr i)) (blockEquiv 2 n (Sum.inr j))
  have hM := blockMat_two_eq b a hut
  set b₁ := (blockLeftGL R 2 n κA)⁻¹ * b * (blockLeftGL R 2 n γA)⁻¹
  have hU : κA⁻¹ * upperGL (a 0) (a 1) (M 0 1) * γA⁻¹ = upperGL α δ β' := by
    rw [hy]; group
  have hb₁ : (b₁ : Matrix (Fin (n + 2)) (Fin (n + 2)) R) =
      blockMat ((upperGL α δ β' : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
        (((κA⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * B) 0 D := by
    simp only [b₁, Matrix.GeneralLinearGroup.coe_mul, ← map_inv, coe_blockLeftGL]
    rw [hM, blockMat_mul, blockMat_mul, ← hU]
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, Matrix.one_mul, Matrix.mul_one]
    rfl
  have hDut : ∀ i j, j < i → D i j = 0 := fun i j hij => hut.1 _ _
    (Fin.lt_def.2 (by simp [Fin.lt_def.1 hij]))
  have hUut := upperGL_upperTriangular α δ β'
  have hut₁ : ∀ i j, j < i → (b₁ : Matrix (Fin (n + 2)) (Fin (n + 2)) R) i j = 0 := by
    rw [hb₁]
    exact blockMat_upperTriangular _ hUut hDut
  obtain ⟨a₁, ha₁⟩ := exists_isUpperTriangularWith b₁ hut₁
  have hκA : κA ∈ (GeneralLinearGroup.map (integralAdeles K).subtype).range :=
    MonoidHom.mem_range.2 ⟨κ, rfl⟩
  have hγA : γA ∈ (GeneralLinearGroup.map (principalAdeles K).subtype).range :=
    MonoidHom.mem_range.2 ⟨γ, rfl⟩
  have hbb : b = blockLeftGL R 2 n κA * b₁ * blockLeftGL R 2 n γA := by
    simp only [b₁, mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel_left]
  refine ⟨b₁, a₁, ⟨blockLeftGL R 2 n κA, blockLeftGL_mem_range hκA,
    blockLeftGL R 2 n γA, blockLeftGL_mem_range hγA, hbb⟩, ha₁, ?_⟩
  have hα : a₁ 0 = α := by
    ext1
    rw [← ha₁.2 0, hb₁]
    have e0 : (0 : Fin (n + 2)) = blockEquiv 2 n (Sum.inl 0) := Fin.ext (by simp)
    rw [e0, blockMat_inl_inl, coe_upperGL]
    simp
  rw [hα]
  exact hlt

end Step

section Main

/-- **Reduction theory**, in the form proved by induction on `n`: every `x ∈ GL_n(A)` lies in
`GL_n(O) b GL_n(K)` for an upper triangular `b` with diagonal `a` and
`c₀ ≤ N(div a_i - div a_{i+1})`, `c₀ = redConst k K`. -/
public theorem exists_sameDoubleCoset_reduced :
    ∀ (n : ℕ) (x : GL (Fin n) (AdeleRing K)), ∃ (b : GL (Fin n) (AdeleRing K))
      (a : Fin n → (AdeleRing K)ˣ), SameDoubleCoset x b ∧ IsUpperTriangularWith b a ∧
        ∀ i j : Fin n, (j : ℕ) = i + 1 →
          redConst k K ≤ divNorm K (idelDiv k K (a i) - idelDiv k K (a j)) := by
  intro n
  induction n with
  | zero =>
    intro x
    exact ⟨x, fun i => i.elim0, SameDoubleCoset.refl x, ⟨fun i => i.elim0, fun i => i.elim0⟩,
      fun i => i.elim0⟩
  | succ n ih =>
    intro x
    set R := AdeleRing K
    -- a decomposition with `deg (div a_0)` maximal
    obtain ⟨C, hC⟩ := exists_degree_bound k x
    have hinh : ∃ d : ℤ, ∃ (b : GL (Fin (n + 1)) R) (a : Fin (n + 1) → Rˣ),
        SameDoubleCoset x b ∧ IsUpperTriangularWith b a ∧
          divisorDegree k K (idelDiv k K (a 0)) = d := by
      obtain ⟨κ, hκ, hut⟩ := exists_mem_range_mapO_upperTriangular x
      obtain ⟨a, ha⟩ := exists_isUpperTriangularWith (κ⁻¹ * x) hut
      exact ⟨_, κ⁻¹ * x, a, ⟨κ, hκ, 1, one_mem _, by group⟩, ha, rfl⟩
    obtain ⟨d, ⟨b, a, hxb, hut, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
      ⟨C, fun z ⟨b, a, hxb, hut, hz⟩ => hz ▸ hC b a hxb hut⟩ hinh
    -- the lower right block
    set M := (b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) with hMdef
    set A : Matrix (Fin 1) (Fin 1) R :=
      of fun i j => M (blockEquiv 1 n (Sum.inl i)) (blockEquiv 1 n (Sum.inl j))
    set B : Matrix (Fin 1) (Fin n) R :=
      of fun i j => M (blockEquiv 1 n (Sum.inl i)) (blockEquiv 1 n (Sum.inr j))
    set D : Matrix (Fin n) (Fin n) R :=
      of fun i j => M (blockEquiv 1 n (Sum.inr i)) (blockEquiv 1 n (Sum.inr j))
    have hM : M = blockMat A B 0 D := by
      conv_lhs => rw [eq_blockMat (m := 1) (n := n) M]
      congr 1
      refine Matrix.ext fun i j => ?_
      rw [of_apply, Matrix.zero_apply]
      exact hut.1 _ _ (Fin.lt_def.2 (by simp))
    have hDdet : IsUnit D.det := by
      have := (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
      change IsUnit M.det at this
      rw [hM, det_blockMat_zero] at this
      exact isUnit_of_mul_isUnit_right this
    set Dg : GL (Fin n) R := Matrix.nonsingInvUnit D hDdet
    have hDut : ∀ i j, j < i → (Dg : Matrix (Fin n) (Fin n) R) i j = 0 := fun i j hij =>
      hut.1 _ _ (Fin.lt_def.2 (by simp [Fin.lt_def.1 hij]))
    obtain ⟨b'', a'', ⟨κ', hκ', γ', hγ', hD⟩, hut'', hpair''⟩ := ih Dg
    set bn := (blockRightGL R 1 n κ')⁻¹ * b * (blockRightGL R 1 n γ')⁻¹
    have hbn : (bn : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
        blockMat A (B * ((γ'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) 0
          (b'' : Matrix (Fin n) (Fin n) R) := by
      have hD' : (b'' : Matrix (Fin n) (Fin n) R) =
          ((κ'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * D *
            ((γ'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
        have : b'' = κ'⁻¹ * Dg * γ'⁻¹ := by rw [hD]; group
        rw [this]
        rfl
      simp only [bn, Matrix.GeneralLinearGroup.coe_mul, ← map_inv, coe_blockRightGL]
      rw [← hMdef, hM, blockMat_mul, blockMat_mul, hD']
      simp [mul_assoc]
    have hutn : ∀ i j, j < i → (bn : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j = 0 := by
      rw [hbn]
      exact blockMat_upperTriangular _ (upperTriangular_fin_one A) hut''.1
    obtain ⟨an, han⟩ := exists_isUpperTriangularWith bn hutn
    have hxbn : SameDoubleCoset x bn := hxb.trans ⟨blockRightGL R 1 n κ',
      blockRightGL_mem_range hκ', blockRightGL R 1 n γ', blockRightGL_mem_range hγ',
      by simp only [bn]; group⟩
    have e0 : (0 : Fin (n + 1)) = blockEquiv 1 n (Sum.inl 0) := Fin.ext (by simp)
    have han0 : an 0 = a 0 := by
      ext1
      rw [← han.2 0, ← hut.2 0, hbn, e0, blockMat_inl_inl]
      rfl
    have hanr : ∀ i : Fin n, an (blockEquiv 1 n (Sum.inr i)) = a'' i := by
      intro i
      ext1
      rw [← han.2, ← hut''.2 i, hbn, blockMat_inr_inr]
    refine ⟨bn, an, hxbn, han, fun i j hij => ?_⟩
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
    · -- the pair `(0, 1)`: maximality of `deg (div a_0)`
      cases n with
      | zero => have := j.isLt; omega
      | succ n =>
        have hi0 : i = 0 := Fin.ext hi
        have hj1 : j = 1 := Fin.ext (by simp [hij, hi])
        subst hi0 hj1
        by_contra hlt
        push Not at hlt
        obtain ⟨b₁, a₁, hb₁, hut₁, hgt⟩ := exists_reduction_step k bn an han hlt
        rw [divNorm_lt_divNorm_iff k, han0] at hgt
        have := hmax _ ⟨b₁, a₁, hxbn.trans hb₁, hut₁, rfl⟩
        omega
    · -- the pairs inside the lower right block
      obtain ⟨i', hi'⟩ : ∃ i' : Fin n, blockEquiv 1 n (Sum.inr i') = i :=
        ⟨⟨i - 1, by have := i.isLt; omega⟩, Fin.ext (by simp; omega)⟩
      obtain ⟨j', hj'⟩ : ∃ j' : Fin n, blockEquiv 1 n (Sum.inr j') = j :=
        ⟨⟨j - 1, by have := j.isLt; omega⟩, Fin.ext (by simp; omega)⟩
      rw [← hi', ← hj', hanr, hanr]
      refine hpair'' i' j' ?_
      have h1 := congrArg Fin.val hi'
      have h2 := congrArg Fin.val hj'
      simp only [blockEquiv_inr_val] at h1 h2
      omega

end Main

variable (K) in
/-- **Reduction theory for `GL_n(A)`** (Harder): there is `c₀ > 0` such that every
`x ∈ GL_n(A)` is `κ b γ` with `κ ∈ GL_n(O)`, `γ ∈ GL_n(K)` and `b` upper triangular with
diagonal `a` satisfying `c₀ ≤ N(div a_i - div a_{i+1})`. -/
public theorem reductionTheory (n : ℕ) : ReductionTheory K n k := by
  refine ⟨redConst k K, redConst_pos k, fun x => ?_⟩
  obtain ⟨b, a, ⟨κ, ⟨κ', rfl⟩, γ, ⟨γ', rfl⟩, hx⟩, hut, hpair⟩ :=
    exists_sameDoubleCoset_reduced k n x
  exact ⟨κ', γ', b, a, hx, hut, hpair⟩

end Stacks.Adeles.GeneralLinear

end
