module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Duality from a diagonal class: the linear algebra

Let `A = H^*(X)` and `B = H^*(X × X)` be `ℤ`-graded graded-commutative `F`-algebras with two graded
algebra maps `p₁, p₂ : A ⟶ B` (the pullbacks along the projections) such that the Künneth map
`κ : A ⊗_F A ⟶ B`, `a ⊗ b ↦ p₁ a · p₂ b`, is bijective. Let `η ∈ B^{2d}` (the class `γ([Δ])` of
the diagonal) and `λ : A ⟶ F` a linear form vanishing outside degree `2d` (a trace map). This file
proves the algebra in the proofs of Lemma 0FIJ and Remark 0FIK of the Stacks Project: if

* `η · p₁ a = η · p₂ a` for all `a` (Lemma 0FII applied to the diagonal),
* `(id ⊗ λ)(κ⁻¹ η) = 1` (axiom (A6)),

then `(id ⊗ λ(- · a))(κ⁻¹ η) = a` for every `a` — the first triangle identity of the proof of
Lemma 0FIJ. From it alone: `H^*(X)` is finite dimensional (spanned by the `e_t`); the pairing
`(y, x) ↦ λ(y x)` between `A^j` and `A^i`, `i + j = 2d`, is perfect (nondegenerate on the right by
the identity, on the left after graded commutativity); hence contraction against the `(i, j)`
Künneth component of `η` is a linear isomorphism `(A^j)^* ≃ A^i`, inverse to `x ↦ λ(- · x)`, and
the trace map is unique. The second triangle identity of the source, which would need the
invariance of `η` under the switch of the factors, is not needed.

## Main results

* `Stacks.WeilCohomology.DiagonalExpansion.exists_expansion`: a homogeneous `η ∈ B^n` is `κ` of a
  finite sum of `e ⊗ f` with `e`, `f` homogeneous of complementary degrees.
* `Stacks.WeilCohomology.DiagonalExpansion.sum_trace_mul_smul`: `∑ λ(f a) e = a`.
* `Stacks.WeilCohomology.DiagonalExpansion.isPerfPair_tracePairing`: `λ(y x)` is perfect.
* `Stacks.WeilCohomology.DiagonalExpansion.bijective_diagonalContract`: the perfect duality
  defined by `η`.
* `Stacks.WeilCohomology.DiagonalExpansion.trace_unique`: uniqueness of `λ`.
-/

@[expose] public section

open TensorProduct DirectSum

namespace Stacks.WeilCohomology.DiagonalExpansion

variable {F : Type*} [Field F] {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
  (𝒜 : ℤ → Submodule F A) [GradedAlgebra 𝒜] (ℬ : ℤ → Submodule F B) [GradedAlgebra ℬ]
  (p₁ p₂ : A →ₐ[F] B)

/-- The Künneth map `a ⊗ b ↦ p₁ a · p₂ b`. -/
def kunneth : A ⊗[F] A →ₗ[F] B :=
  TensorProduct.lift ((LinearMap.mul F B).compl₁₂ p₁.toLinearMap p₂.toLinearMap)

/-- The Künneth map sends `a ⊗ b` to `p₁ a * p₂ b`. -/
@[simp]
theorem kunneth_tmul (a b : A) : kunneth p₁ p₂ (a ⊗ₜ b) = p₁ a * p₂ b := rfl

/-- The sum `∑ e ⊗ f` of a list of triples `(degree, e, f)`. -/
def tensorSum (l : List (ℤ × A × A)) : A ⊗[F] A :=
  (l.map fun t => t.2.1 ⊗ₜ[F] t.2.2).sum

/-- The sum over the empty list is `0`. -/
@[simp]
theorem tensorSum_nil : tensorSum (F := F) ([] : List (ℤ × A × A)) = 0 := rfl

/-- The sum over `t :: l` is `t.2.1 ⊗ t.2.2` plus the sum over `l`. -/
@[simp]
theorem tensorSum_cons (t : ℤ × A × A) (l : List (ℤ × A × A)) :
    tensorSum (F := F) (t :: l) = t.2.1 ⊗ₜ t.2.2 + tensorSum l := rfl

/-- The sum over `l ++ l'` is the sum over `l` plus the sum over `l'`. -/
theorem tensorSum_append (l l' : List (ℤ × A × A)) :
    tensorSum (F := F) (l ++ l') = tensorSum l + tensorSum l' := by
  simp [tensorSum]

/-- A list of triples `(a, e, f)` is homogeneous of total degree `n` if `e ∈ 𝒜 a` and
`f ∈ 𝒜 (n - a)`. -/
def IsHomogeneous (n : ℤ) (l : List (ℤ × A × A)) : Prop :=
  ∀ t ∈ l, t.2.1 ∈ 𝒜 t.1 ∧ t.2.2 ∈ 𝒜 (n - t.1)

variable {𝒜 ℬ p₁ p₂}

/-- A linear map `φ` sends `∑ e ⊗ f` to `∑ φ (e ⊗ f)`. -/
theorem map_tensorSum {M : Type*} [AddCommGroup M] [Module F M] (φ : A ⊗[F] A →ₗ[F] M)
    (l : List (ℤ × A × A)) :
    φ (tensorSum l) = (l.map fun t => φ (t.2.1 ⊗ₜ t.2.2)).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih]

/-- The sum `∑ e ⊗ f` of a list of quadruples `(deg e, deg f, e, f)`. -/
def tensorSum₄ (l : List (ℤ × ℤ × A × A)) : A ⊗[F] A :=
  (l.map fun t => t.2.2.1 ⊗ₜ[F] t.2.2.2).sum

variable (𝒜) in
/-- Every element of `A ⊗ A` is a finite sum of `e ⊗ f` with `e` and `f` homogeneous. -/
theorem exists_homogeneous_list (z : A ⊗[F] A) :
    ∃ l : List (ℤ × ℤ × A × A), (∀ t ∈ l, t.2.2.1 ∈ 𝒜 t.1 ∧ t.2.2.2 ∈ 𝒜 t.2.1) ∧
      z = tensorSum₄ l := by
  let P : A ⊗[F] A → Prop := fun z => ∃ l : List (ℤ × ℤ × A × A),
    (∀ t ∈ l, t.2.2.1 ∈ 𝒜 t.1 ∧ t.2.2.2 ∈ 𝒜 t.2.1) ∧ z = tensorSum₄ l
  have h0 : P 0 := ⟨[], by simp, by simp [tensorSum₄]⟩
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
    exact ⟨l ++ l', List.forall_mem_append.2 ⟨hl, hl'⟩, by simp [tensorSum₄]⟩
  change P z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => exact hadd _ _ hx hy
  | tmul e f =>
    induction e using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rwa [zero_tmul]
    | add e e' he he' => rw [add_tmul]; exact hadd _ _ he he'
    | @homogeneous i e =>
      induction f using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => rwa [tmul_zero]
      | add f f' hf hf' => rw [tmul_add]; exact hadd _ _ hf hf'
      | @homogeneous j f =>
        exact ⟨[(i, j, (e : A), (f : A))], by simp, by simp [tensorSum₄]⟩

variable (hp₁ : ∀ (n : ℤ) (a : A), a ∈ 𝒜 n → p₁ a ∈ ℬ n)
  (hp₂ : ∀ (n : ℤ) (a : A), a ∈ 𝒜 n → p₂ a ∈ ℬ n)

include hp₁ hp₂ in
omit [GradedAlgebra 𝒜] in
/-- The degree-`n` part of `κ(∑ e ⊗ f)`, for `e`, `f` homogeneous, is `κ` of the sum of the terms
of total degree `n`. -/
theorem decompose_kunneth_tensorSum₄ (n : ℤ) (l : List (ℤ × ℤ × A × A))
    (hl : ∀ t ∈ l, t.2.2.1 ∈ 𝒜 t.1 ∧ t.2.2.2 ∈ 𝒜 t.2.1) :
    (decompose ℬ (kunneth p₁ p₂ (tensorSum₄ l)) n : B) =
      kunneth p₁ p₂ (tensorSum₄ (l.filter fun t => t.1 + t.2.1 = n)) := by
  induction l with
  | nil => simp [tensorSum₄]
  | cons t l ih =>
    have hmem : kunneth p₁ p₂ (t.2.2.1 ⊗ₜ t.2.2.2) ∈ ℬ (t.1 + t.2.1) :=
      SetLike.GradedMul.mul_mem (hp₁ _ _ (hl t (by simp)).1) (hp₂ _ _ (hl t (by simp)).2)
    have ih := ih fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')
    simp only [tensorSum₄, List.map_cons, List.sum_cons, map_add, decompose_add, add_apply,
      Submodule.coe_add] at ih ⊢
    rw [ih]
    by_cases h : t.1 + t.2.1 = n
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, List.sum_cons, map_add]
      rw [← h, decompose_of_mem_same ℬ hmem]
    · rw [List.filter_cons_of_neg (by simpa using h), decompose_of_mem_ne ℬ hmem h, zero_add]

include hp₁ hp₂ in
/-- **Homogeneous expansion of a class of `B^n`**: if the Künneth map is surjective, every
`η ∈ B^n` is `κ(∑ e_j ⊗ f_j)` with `e_j ∈ A^{a_j}` and `f_j ∈ A^{n - a_j}`. -/
theorem exists_expansion (hκ : Function.Surjective (kunneth p₁ p₂)) {n : ℤ} {η : B}
    (hη : η ∈ ℬ n) :
    ∃ l : List (ℤ × A × A), IsHomogeneous 𝒜 n l ∧ kunneth p₁ p₂ (tensorSum l) = η := by
  obtain ⟨z, rfl⟩ := hκ η
  obtain ⟨l, hl, rfl⟩ := exists_homogeneous_list 𝒜 z
  refine ⟨(l.filter fun t => t.1 + t.2.1 = n).map fun t => (t.1, t.2.2.1, t.2.2.2), ?_, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    obtain ⟨ht'l, ht'n⟩ := List.mem_filter.1 ht'
    have : t'.2.1 = n - t'.1 := by simp at ht'n; omega
    exact ⟨(hl t' ht'l).1, this ▸ (hl t' ht'l).2⟩
  · have h := decompose_kunneth_tensorSum₄ hp₁ hp₂ n l hl
    rw [decompose_of_mem_same ℬ hη] at h
    rw [h]
    congr 1
    simp [tensorSum, tensorSum₄, Function.comp_def]

/-! ### The first triangle identity -/

section Triangle

variable (𝒜 ℬ p₁ p₂)

/-- The data of a diagonal class `η = κ(∑ e_t ⊗ f_t) ∈ B^n` with a trace `λ` normalised as
in axiom (A6), satisfying `η · p₁ a = η · p₂ a`, with `B` graded commutative. -/
structure DiagonalData (n : ℤ) (η : B) (lam : A →ₗ[F] F) (l : List (ℤ × A × A)) : Prop where
  pull₁ : ∀ (m : ℤ) (a : A), a ∈ 𝒜 m → p₁ a ∈ ℬ m
  pull₂ : ∀ (m : ℤ) (a : A), a ∈ 𝒜 m → p₂ a ∈ ℬ m
  graded_comm : ∀ (i j : ℤ) (x y : B), x ∈ ℬ i → y ∈ ℬ j →
    x * y = (Int.negOnePow (i * j) : ℤ) • (y * x)
  graded_comm_left : ∀ (i j : ℤ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
    x * y = (Int.negOnePow (i * j) : ℤ) • (y * x)
  injective : Function.Injective (kunneth p₁ p₂)
  even : Even n
  homogeneous : IsHomogeneous 𝒜 n l
  expansion : kunneth p₁ p₂ (tensorSum l) = η
  trace_eq_zero : ∀ i, i ≠ n → ∀ x ∈ 𝒜 i, lam x = 0
  normalized : (l.map fun t => lam t.2.2 • t.2.1).sum = 1
  key : ∀ a, η * p₁ a = η * p₂ a

variable {𝒜 ℬ p₁ p₂} {n : ℤ} {η : B} {lam : A →ₗ[F] F} {l : List (ℤ × A × A)}

/-- `κ(∑ e ⊗ f a) = κ(∑ e ⊗ f) · p₂ a`. -/
theorem kunneth_tensorSum_mul_right (l : List (ℤ × A × A)) (a : A) :
    kunneth p₁ p₂ (tensorSum (l.map fun t => (t.1, t.2.1, t.2.2 * a))) =
      kunneth p₁ p₂ (tensorSum l) * p₂ a := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih, add_mul, mul_assoc]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- For `a ∈ A^m` and `∑ e ⊗ f` homogeneous of degree `n`,
`κ(∑ (-1)^{(n - a_t) m} e a ⊗ f) = κ(∑ e ⊗ f) · p₁ a`. -/
theorem kunneth_tensorSum_mul_left
    (pull₁ : ∀ (m : ℤ) (a : A), a ∈ 𝒜 m → p₁ a ∈ ℬ m)
    (pull₂ : ∀ (m : ℤ) (a : A), a ∈ 𝒜 m → p₂ a ∈ ℬ m)
    (graded_comm : ∀ (i j : ℤ) (x y : B), x ∈ ℬ i → y ∈ ℬ j →
      x * y = (Int.negOnePow (i * j) : ℤ) • (y * x))
    (l : List (ℤ × A × A)) (hl : IsHomogeneous 𝒜 n l) {m : ℤ} {a : A} (ha : a ∈ 𝒜 m) :
    kunneth p₁ p₂ ((l.map fun t =>
        ((Int.negOnePow ((n - t.1) * m) : ℤ) : F) • ((t.2.1 * a) ⊗ₜ[F] t.2.2)).sum) =
      kunneth p₁ p₂ (tensorSum l) * p₁ a := by
  induction l with
  | nil => simp
  | cons t l ih =>
    have ht := hl t (by simp)
    simp only [List.map_cons, List.sum_cons, map_add, tensorSum_cons, add_mul]
    rw [ih fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')]
    congr 1
    rw [map_smul, kunneth_tmul, kunneth_tmul, map_mul, mul_assoc, mul_assoc,
      graded_comm _ _ (p₂ t.2.2) (p₁ a) (pull₂ _ _ ht.2) (pull₁ _ _ ha),
      mul_smul_comm, ← Int.cast_smul_eq_zsmul F]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- Only the terms with `f ∈ A^n` see the trace, and their sign `(-1)^{(n - a) m} = (-1)^{nm}` is
`1` because `n` is even. -/
theorem negOnePow_mul_trace (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) (m : ℤ) {t : ℤ × A × A}
    (ht : t ∈ l) :
    ((Int.negOnePow ((n - t.1) * m) : ℤ) : F) * lam t.2.2 = lam t.2.2 := by
  by_cases h0 : t.1 = 0
  · obtain ⟨k, hk⟩ := hD.even
    rw [h0, sub_zero, hk, show (k + k) * m = 2 * (k * m) by ring, Int.negOnePow_two_mul]
    simp
  · rw [hD.trace_eq_zero (n - t.1) (by omega) _ (hD.homogeneous t ht).2, mul_zero]

/-- The map `x ⊗ y ↦ λ(y) x`. -/
def contractRight (lam : A →ₗ[F] F) : A ⊗[F] A →ₗ[F] A :=
  (TensorProduct.rid F A).toLinearMap ∘ₗ LinearMap.lTensor A lam

/-- `contractRight lam` sends `x ⊗ y` to `λ(y) x`. -/
@[simp]
theorem contractRight_tmul (x y : A) : contractRight lam (x ⊗ₜ y) = lam y • x := by
  simp [contractRight]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- **The first triangle identity** `∑ λ(f a) e = a`, for `a` homogeneous. -/
theorem sum_trace_mul_smul_of_mem (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {m : ℤ} {a : A}
    (ha : a ∈ 𝒜 m) : (l.map fun t => lam (t.2.2 * a) • t.2.1).sum = a := by
  have hk : kunneth p₁ p₂ (tensorSum (l.map fun t => (t.1, t.2.1, t.2.2 * a))) =
      kunneth p₁ p₂ ((l.map fun t =>
        ((Int.negOnePow ((n - t.1) * m) : ℤ) : F) • ((t.2.1 * a) ⊗ₜ[F] t.2.2)).sum) := by
    rw [kunneth_tensorSum_mul_right, kunneth_tensorSum_mul_left hD.pull₁ hD.pull₂ hD.graded_comm l
      hD.homogeneous ha, hD.expansion, hD.key]
  have h' := congrArg (contractRight lam) (hD.injective hk)
  rw [map_tensorSum, map_list_sum, List.map_map, List.map_map] at h'
  simp only [Function.comp_def, contractRight_tmul, map_smul] at h'
  refine h'.trans ?_
  calc (l.map fun t => ((Int.negOnePow ((n - t.1) * m) : ℤ) : F) • lam t.2.2 • (t.2.1 * a)).sum
      = (l.map fun t => lam t.2.2 • t.2.1).sum * a := by
        rw [← List.sum_map_mul_right]
        congr 1
        refine List.map_congr_left fun t ht => ?_
        rw [smul_smul, negOnePow_mul_trace hD m ht, smul_mul_assoc]
    _ = a := by rw [hD.normalized, one_mul]

omit [GradedAlgebra ℬ] in
/-- **The first triangle identity** `∑ λ(f a) e = a`. -/
theorem sum_trace_mul_smul (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) (a : A) :
    (l.map fun t => lam (t.2.2 * a) • t.2.1).sum = a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb =>
    simp only [mul_add, map_add, add_smul, List.sum_map_add, ha, hb]
  | @homogeneous i a => exact sum_trace_mul_smul_of_mem hD a.2

omit [GradedAlgebra ℬ] in
/-- `H^*(X)` is spanned by the first factors `e_t` of the expansion, so it is finite
dimensional. -/
theorem finiteDimensional (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) : FiniteDimensional F A := by
  classical
  refine Module.Finite.of_fg_top ?_
  refine ⟨(l.map fun t => t.2.1).toFinset, eq_top_iff.2 fun a _ => ?_⟩
  rw [← sum_trace_mul_smul hD a]
  refine list_sum_mem fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (List.mem_toFinset.2 (List.mem_map_of_mem ht)))

omit [GradedAlgebra ℬ] in
/-- **Nondegeneracy**: for `x ∈ A^i`, if `λ(y x) = 0` for all `y ∈ A^j`, `i + j = n`, then
`x = 0`. -/
theorem eq_zero_of_trace_mul (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {i j : ℤ} (hij : i + j = n)
    {x : A} (hx : x ∈ 𝒜 i) (h : ∀ y ∈ 𝒜 j, lam (y * x) = 0) : x = 0 := by
  rw [← sum_trace_mul_smul hD x]
  refine List.sum_eq_zero fun z hz => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
  have hf := (hD.homogeneous t ht).2
  by_cases hj : n - t.1 = j
  · rw [h _ (hj ▸ hf), zero_smul]
  · rw [hD.trace_eq_zero (n - t.1 + i) (by omega) _ (SetLike.GradedMul.mul_mem hf hx), zero_smul]

variable (lam) in
/-- The pairing `A^j × A^i ⟶ F`, `(y, x) ↦ λ(y x)`, for `i + j = n`. -/
def tracePairing (i j : ℤ) : 𝒜 j →ₗ[F] 𝒜 i →ₗ[F] F :=
  LinearMap.mk₂ F (fun y x => lam ((y : A) * x))
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp)

omit [GradedAlgebra 𝒜] in
/-- The trace pairing sends `(y, x)` to `λ(y x)`. -/
@[simp]
theorem tracePairing_apply (i j : ℤ) (y : 𝒜 j) (x : 𝒜 i) :
    tracePairing (𝒜 := 𝒜) lam i j y x = lam ((y : A) * x) := rfl

omit [GradedAlgebra ℬ] in
/-- **The trace pairing is perfect**: `(y, x) ↦ λ(y x)` is a perfect pairing between `A^j` and
`A^i` for `i + j = n`. -/
theorem isPerfPair_tracePairing (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {i j : ℤ}
    (hij : i + j = n) : (tracePairing (𝒜 := 𝒜) lam i j).IsPerfPair := by
  have := finiteDimensional hD
  refine LinearMap.IsPerfPair.of_injective (fun y y' hyy' => ?_) (fun x x' hxx' => ?_)
  · have := eq_zero_of_trace_mul hD (by omega : j + i = n) (sub_mem y.2 y'.2) fun x hx => by
      have := LinearMap.congr_fun hyy' ⟨x, hx⟩
      simp only [tracePairing_apply] at this
      rw [hD.graded_comm_left _ _ _ _ hx (sub_mem y.2 y'.2), map_zsmul, sub_mul, map_sub, this,
        sub_self, smul_zero]
    exact Subtype.ext (sub_eq_zero.1 this)
  · have := eq_zero_of_trace_mul hD hij (sub_mem x.2 x'.2) fun y hy => by
      have := LinearMap.congr_fun hxx' ⟨y, hy⟩
      simp only [LinearMap.flip_apply, tracePairing_apply] at this
      rw [mul_sub, map_sub, this, sub_self]
    exact Subtype.ext (sub_eq_zero.1 this)

variable (l) in
/-- **Contraction against the `(i, j)` component of the diagonal class**,
`μ ↦ (1 ⊗ μ)(η_{i,j}) = ∑_{a_t = i} μ(f_t) e_t`, for `μ` a linear form on `A^j`, as an element
of `A`. -/
def diagonalContractA (i j : ℤ) : (𝒜 j →ₗ[F] F) →ₗ[F] A where
  toFun μ := (l.map fun t => μ (decompose 𝒜 t.2.2 j) • (decompose 𝒜 t.2.1 i : A)).sum
  map_add' μ ν := by simp [add_smul, List.sum_map_add]
  map_smul' c μ := by
    simp only [LinearMap.smul_apply, RingHom.id_apply, smul_assoc]
    rw [List.smul_sum, List.map_map]
    rfl

/-- The contraction `diagonalContractA l i j μ` lies in `A^i`. -/
theorem diagonalContractA_mem (i j : ℤ) (μ : 𝒜 j →ₗ[F] F) :
    diagonalContractA (𝒜 := 𝒜) l i j μ ∈ 𝒜 i :=
  list_sum_mem fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact Submodule.smul_mem _ _ (decompose 𝒜 t.2.1 i).2

variable (l) in
/-- The contraction against the `(i, j)` component of the diagonal class, with values in
`A^i`. -/
def diagonalContract (i j : ℤ) : (𝒜 j →ₗ[F] F) →ₗ[F] 𝒜 i :=
  (diagonalContractA (𝒜 := 𝒜) l i j).codRestrict (𝒜 i) (diagonalContractA_mem i j)

/-- As an element of `A`, `diagonalContract l i j μ` is `∑ μ(f_t^{(j)}) e_t^{(i)}`, the sum over
the degree-`j` and degree-`i` components of the `f_t` and `e_t`. -/
theorem coe_diagonalContract (i j : ℤ) (μ : 𝒜 j →ₗ[F] F) :
    (diagonalContract (𝒜 := 𝒜) l i j μ : A) =
      (l.map fun t => μ (decompose 𝒜 t.2.2 j) • (decompose 𝒜 t.2.1 i : A)).sum := rfl

omit [GradedAlgebra ℬ] in
/-- Contraction of the diagonal class against `y ↦ λ(y x)` returns `x`. -/
theorem diagonalContract_tracePairing_flip (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {i j : ℤ}
    (hij : i + j = n) (x : 𝒜 i) :
    diagonalContract (𝒜 := 𝒜) l i j ((tracePairing (𝒜 := 𝒜) lam i j).flip x) = x := by
  apply Subtype.ext
  rw [coe_diagonalContract]
  conv_rhs => rw [← sum_trace_mul_smul hD (x : A)]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨he, hf⟩ := hD.homogeneous t ht
  simp only [LinearMap.flip_apply, tracePairing_apply]
  by_cases hi : t.1 = i
  · subst hi
    rw [decompose_of_mem_same 𝒜 he, show j = n - t.1 by omega, decompose_of_mem_same 𝒜 hf]
  · rw [decompose_of_mem_ne 𝒜 he hi, smul_zero,
      hD.trace_eq_zero (n - t.1 + i) (by omega) _ (SetLike.GradedMul.mul_mem hf x.2), zero_smul]

omit [GradedAlgebra ℬ] in
/-- **The duality defined by the diagonal class**: for `i + j = n`, contraction against the
`(i, j)` Künneth component of `η` is bijective, `(A^j)^* ≃ A^i`, inverse to `x ↦ λ(- · x)`. -/
theorem bijective_diagonalContract (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {i j : ℤ}
    (hij : i + j = n) : Function.Bijective (diagonalContract (𝒜 := 𝒜) l i j) := by
  have := isPerfPair_tracePairing hD hij
  have hΦ : Function.Bijective (tracePairing (𝒜 := 𝒜) lam i j).flip :=
    LinearMap.IsPerfPair.bijective_right _
  refine ⟨fun μ μ' h => ?_, fun x => ⟨_, diagonalContract_tracePairing_flip hD hij x⟩⟩
  obtain ⟨x, rfl⟩ := hΦ.2 μ
  obtain ⟨x', rfl⟩ := hΦ.2 μ'
  rw [diagonalContract_tracePairing_flip hD hij, diagonalContract_tracePairing_flip hD hij] at h
  rw [h]

omit [GradedAlgebra ℬ] in
/-- **Uniqueness of the trace map** (Remark 0FIK): two linear forms vanishing outside degree `n`
and both normalised by `∑ λ(f_t) e_t = 1` against the same expansion of the diagonal class agree,
as soon as one of them satisfies the hypotheses of `DiagonalData`. -/
theorem trace_unique (hD : DiagonalData 𝒜 ℬ p₁ p₂ n η lam l) {lam' : A →ₗ[F] F}
    (h0 : ∀ i, i ≠ n → ∀ x ∈ 𝒜 i, lam' x = 0)
    (h1 : (l.map fun t => lam' t.2.2 • t.2.1).sum = 1) : lam' = lam := by
  have key : ∀ μ : A →ₗ[F] F, (∀ i, i ≠ n → ∀ x ∈ 𝒜 i, μ x = 0) →
      (diagonalContract (𝒜 := 𝒜) l 0 n (μ ∘ₗ (𝒜 n).subtype) : A) =
        GradedAlgebra.proj 𝒜 0 ((l.map fun t => μ t.2.2 • t.2.1).sum) := by
    intro μ hμ
    rw [coe_diagonalContract, map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨he, hf⟩ := hD.homogeneous t ht
    simp only [Function.comp_apply, map_smul, GradedAlgebra.proj_apply, LinearMap.comp_apply,
      Submodule.subtype_apply]
    congr 1
    by_cases h : t.1 = 0
    · rw [h, sub_zero] at hf
      rw [decompose_of_mem_same 𝒜 hf]
    · rw [decompose_of_mem_ne 𝒜 hf (by omega), hμ _ (by omega) _ hf]
      simp
  have hD0 := (bijective_diagonalContract hD (zero_add n)).1
    (Subtype.ext ((key lam' h0).trans ((by rw [h1, hD.normalized] :
      GradedAlgebra.proj 𝒜 0 ((l.map fun t => lam' t.2.2 • t.2.1).sum) =
        GradedAlgebra.proj 𝒜 0 ((l.map fun t => lam t.2.2 • t.2.1).sum)).trans
      (key lam hD.trace_eq_zero).symm)))
  ext x
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | @homogeneous i x =>
    by_cases hi : i = n
    · subst hi
      exact LinearMap.congr_fun hD0 x
    · rw [h0 i hi _ x.2, hD.trace_eq_zero i hi _ x.2]

end Triangle

end Stacks.WeilCohomology.DiagonalExpansion

end
