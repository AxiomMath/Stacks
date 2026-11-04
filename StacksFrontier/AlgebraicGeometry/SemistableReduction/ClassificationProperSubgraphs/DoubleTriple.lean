module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Fork
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.QuadraticForm
public import StacksCore.Tactic.StacksAttribute

/-!
# Nonexistence of double-triple proper subgraphs

A numerical type cannot contain, as a proper collection of minus-two indices, a
chain of length at least four with an additional leaf attached at each of the
two vertices next to its ends. Equivalently, the affine Dynkin diagram `D̃` does
not occur as a proper subgraph, so no proper connected subgraph of minus-two
indices has two trivalent vertices.

Such a configuration contains two forks sharing all but one vertex: discarding
the leaf attached to the second vertex of the chain leaves one fork, and
discarding the second vertex of the chain leaves the other. Each has constant
weight `w`, and on its affine coefficient vector — `2` on the interior of the
chain and `1` at the two leaves — the intersection form takes the value
`-4 * w`. The two coefficient vectors agree except at the vertex that was
discarded, so the parallelogram law evaluates the form on their sum as
`8 * a`, where `a` is the intersection number of the two discarded vertices.
Since `a ≥ 0` and the form is nonpositive, `a = 0` and the form vanishes on
that sum; the zero locus of the form is the line spanned by the multiplicity
vector, which is nowhere zero, while the sum vanishes on any component outside
the configuration. So the sum is zero, and it is not.

## Main results

* `AlgebraicGeometry.NumericalType.not_exists_double_triple_subgraph`: the
  double-triple configuration does not occur.

## Implementation notes

The indices `i₀, …, iₜ₊₁` are a sequence of component indices which is injective
on the natural numbers below `t + 2`; values of the sequence outside this range
are immaterial. The chain is `i 1, …, i t`, the leaf `i 0` is attached to `i 2`,
and the leaf `i (t + 1)` is attached to `i (t - 1)`. The result is independent
of the genus, so it is stated for an arbitrary numerical type.

## References

* [Stacks Project, Tag 0C8H](https://stacks.math.columbia.edu/tag/0C8H)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

open Matrix

/-! ### The affine coefficient vector of a fork -/

/-- The affine coefficient vector of a fork on `t + 1` vertices: `2` on the
interior of the chain and `1` at the two leaves. -/
private def forkCoeff (t : ℕ) : Fin (t + 1) → ℚ :=
  fun k => if k.val < t - 1 then 2 else 1

private lemma forkCoeff_zero {t : ℕ} (ht : 3 ≤ t) : forkCoeff t 0 = 2 := by
  simp [forkCoeff, show 0 < t - 1 by omega]

/-- The vector supported on the vertices of a fork with the affine
coefficients. -/
private def forkVector {T : NumericalType} {t : ℕ}
    (g : Fin (t + 1) → Fin T.componentCount) : Fin T.componentCount → ℚ :=
  ∑ r, forkCoeff t r • Pi.single (g r) (1 : ℚ)

/-- The intersection form of a fork of shape `w`, evaluated on its affine
coefficient vector, is `-4 * w`. -/
private lemma forkVector_quadratic (T : NumericalType) (t : ℕ) (ht : 3 ≤ t)
    (g : Fin (t + 1) → Fin T.componentCount) (w : ℤ)
    (hs : ForkShape T t g w) (hm : ∀ j, IsMinusTwoIndex T (g j)) :
    forkVector g ⬝ᵥ (ratIntersection T *ᵥ forkVector g) = -4 * (w : ℚ) := by
  rw [forkVector,
    Matrix.dotProduct_mulVec_sum_single (ratIntersection T) g (forkCoeff t)]
  have hcast := congrArg (fun z : ℤ => (z : ℚ))
    (fork_quadratic_value T ht g w hm hs)
  push_cast at hcast
  simpa [ratIntersection, forkCoeff] using hcast

/-- Two forks agreeing away from their first vertex have affine vectors
differing by twice the difference of the two first basis vectors. -/
private lemma forkVector_sub {T : NumericalType} {t : ℕ} (ht : 3 ≤ t)
    (g₀ g₁ : Fin (t + 1) → Fin T.componentCount)
    (htail : ∀ k : Fin (t + 1), k ≠ 0 → g₀ k = g₁ k) :
    forkVector g₀ - forkVector g₁ =
      (2 : ℚ) • (Pi.single (g₀ 0) (1 : ℚ) - Pi.single (g₁ 0) (1 : ℚ)) := by
  rw [forkVector, forkVector, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single (0 : Fin (t + 1)) ?_ ?_]
  · rw [forkCoeff_zero ht, smul_sub]
  · intro r _ hr
    rw [htail r hr, sub_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The affine vector of a fork vanishes on components outside the fork. -/
private lemma forkVector_apply_outside {T : NumericalType} {t : ℕ}
    (g : Fin (t + 1) → Fin T.componentCount) (k : Fin T.componentCount)
    (hk : ∀ r, g r ≠ k) : forkVector g k = 0 := by
  rw [forkVector, Finset.sum_apply]
  exact Finset.sum_eq_zero fun r _ => by simp [hk r]

/-- The affine vector of an injectively indexed fork takes the value `2` at the
fork's first vertex. -/
private lemma forkVector_apply_first {T : NumericalType} {t : ℕ} (ht : 3 ≤ t)
    (g : Fin (t + 1) → Fin T.componentCount) (hinj : Function.Injective g) :
    forkVector g (g 0) = 2 := by
  rw [forkVector, Finset.sum_apply,
    Finset.sum_eq_single (0 : Fin (t + 1)) ?_ ?_]
  · rw [forkCoeff_zero ht]; simp
  · intro r _ hr
    simp [show g r ≠ g 0 from fun h => hr (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The intersection form on the difference of two standard basis vectors. -/
private lemma quadratic_single_sub_single (T : NumericalType)
    (a b : Fin T.componentCount) :
    (Pi.single a (1 : ℚ) - Pi.single b (1 : ℚ)) ⬝ᵥ
      (ratIntersection T *ᵥ (Pi.single a (1 : ℚ) - Pi.single b (1 : ℚ))) =
    (T.intersection a a : ℚ) - 2 * (T.intersection a b : ℚ) +
      (T.intersection b b : ℚ) := by
  have hsymm : (T.intersection b a : ℚ) = (T.intersection a b : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (T.intersection_symm b a)
  have hrw : (Pi.single a (1 : ℚ) - Pi.single b (1 : ℚ)) =
      ∑ r : Fin 2, (![1, -1] : Fin 2 → ℚ) r •
        Pi.single ((![a, b] : Fin 2 → Fin T.componentCount) r) (1 : ℚ) := by
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  rw [hrw, Matrix.dotProduct_mulVec_sum_single (ratIntersection T)
    (![a, b] : Fin 2 → Fin T.componentCount) (![1, -1] : Fin 2 → ℚ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ratIntersection]
  rw [hsymm]
  ring

private lemma dotProduct_mulVec_smul {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℚ) (c : ℚ) (u : ι → ℚ) :
    (c • u) ⬝ᵥ (A *ᵥ (c • u)) = c ^ 2 * (u ⬝ᵥ (A *ᵥ u)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul]
  ring

/-! ### Two forks cannot share all but one vertex -/

/-- Two forks of the same constant weight inside a proper subset of the
components of a numerical type cannot agree away from their first vertices.
This is the engine of `not_exists_double_triple_subgraph`: the double-triple
configuration gives exactly such a pair. -/
private lemma not_two_forks_sharing_tail (T : NumericalType) (t : ℕ) (ht : 3 ≤ t)
    (g₀ g₁ : Fin (t + 1) → Fin T.componentCount) (w : ℤ)
    (hs₀ : ForkShape T t g₀ w) (hs₁ : ForkShape T t g₁ w)
    (hm₀ : ∀ j, IsMinusTwoIndex T (g₀ j)) (hm₁ : ∀ j, IsMinusTwoIndex T (g₁ j))
    (hinj₀ : Function.Injective g₀)
    (htail : ∀ k : Fin (t + 1), k ≠ 0 → g₀ k = g₁ k)
    (hne : ∀ r, g₁ r ≠ g₀ 0)
    (k₀ : Fin T.componentCount) (hk₀ : ∀ r, g₀ r ≠ k₀)
    (hk₁ : ∀ r, g₁ r ≠ k₀) :
    False := by
  have hQ₀ := forkVector_quadratic T t ht g₀ w hs₀ hm₀
  have hQ₁ := forkVector_quadratic T t ht g₁ w hs₁ hm₁
  have hd : ∀ g : Fin (t + 1) → Fin T.componentCount, ForkShape T t g w →
      (∀ j, IsMinusTwoIndex T (g j)) → T.intersection (g 0) (g 0) = -2 * w := by
    intro g hs hm
    have h := (hm 0).2
    rwa [hs.1 0] at h
  have hd₀ := hd g₀ hs₀ hm₀
  have hd₁ := hd g₁ hs₁ hm₁
  have hQdiff : (forkVector g₀ - forkVector g₁) ⬝ᵥ
      (ratIntersection T *ᵥ (forkVector g₀ - forkVector g₁)) =
      4 * (-4 * (w : ℚ) - 2 * (T.intersection (g₀ 0) (g₁ 0) : ℚ)) := by
    rw [forkVector_sub ht g₀ g₁ htail, dotProduct_mulVec_smul,
      quadratic_single_sub_single]
    push_cast [hd₀, hd₁]
    ring
  have hQsum : (forkVector g₀ + forkVector g₁) ⬝ᵥ
      (ratIntersection T *ᵥ (forkVector g₀ + forkVector g₁)) =
      8 * (T.intersection (g₀ 0) (g₁ 0) : ℚ) := by
    have hpar := Matrix.dotProduct_mulVec_parallelogram (ratIntersection T)
      (forkVector g₀) (forkVector g₁)
    rw [hQ₀, hQ₁, hQdiff] at hpar
    linarith
  have hb : 0 ≤ T.intersection (g₀ 0) (g₁ 0) :=
    T.intersection_nonneg _ _ fun h => hne 0 h.symm
  have hle := intersection_quadratic_nonpos T (forkVector g₀ + forkVector g₁)
  rw [hQsum] at hle
  have hbz : T.intersection (g₀ 0) (g₁ 0) = 0 := by
    have hq : (T.intersection (g₀ 0) (g₁ 0) : ℚ) ≤ 0 := by linarith
    have hz : T.intersection (g₀ 0) (g₁ 0) ≤ 0 := by exact_mod_cast hq
    omega
  have hzero : (forkVector g₀ + forkVector g₁) ⬝ᵥ
      (ratIntersection T *ᵥ (forkVector g₀ + forkVector g₁)) = 0 := by
    rw [hQsum, hbz]
    norm_num
  obtain ⟨q, hq⟩ := (intersection_quadratic_eq_zero_iff T _).mp hzero
  have hqzero : q = 0 := by
    have hval : (forkVector g₀ + forkVector g₁) k₀ = 0 := by
      rw [Pi.add_apply, forkVector_apply_outside g₀ k₀ hk₀,
        forkVector_apply_outside g₁ k₀ hk₁]
      ring
    have hqk := congrFun hq k₀
    rw [hval] at hqk
    have hmk : (0 : ℚ) < (T.multiplicity k₀ : ℚ) := by
      exact_mod_cast T.multiplicity_pos k₀
    simp only [Pi.smul_apply, smul_eq_mul] at hqk
    rcases mul_eq_zero.mp hqk.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hmk)
  have hat : (forkVector g₀ + forkVector g₁) (g₀ 0) = 2 := by
    rw [Pi.add_apply, forkVector_apply_first ht g₀ hinj₀,
      forkVector_apply_outside g₁ (g₀ 0) hne]
    ring
  have hcontra := congrFun hq (g₀ 0)
  rw [hat, hqzero] at hcontra
  simp at hcontra

/-! ### The two forks of a double-triple configuration -/

/-- The fork obtained from a double-triple configuration by keeping the leaf
`indices first` and discarding the other one: its chain is
`indices first, indices 2, …, indices t` and its leaf is `indices (t + 1)`,
attached to `indices (t - 1)`. -/
private def doubleTripleFork (T : NumericalType) (t : ℕ)
    (indices : ℕ → Fin T.componentCount) (first : ℕ) :
    Fin (t + 1) → Fin T.componentCount := fun k =>
  if k.val = 0 then indices first else indices (k.val + 1)

private lemma doubleTripleFork_of_zero (T : NumericalType) (t : ℕ)
    (indices : ℕ → Fin T.componentCount) (first : ℕ) (k : Fin (t + 1))
    (hk : k.val = 0) :
    doubleTripleFork T t indices first k = indices first := by
  simp [doubleTripleFork, hk]

private lemma doubleTripleFork_of_ne_zero (T : NumericalType) (t : ℕ)
    (indices : ℕ → Fin T.componentCount) (first : ℕ) (k : Fin (t + 1))
    (hk : k.val ≠ 0) :
    doubleTripleFork T t indices first k = indices (k.val + 1) := by
  simp [doubleTripleFork, hk]

private lemma doubleTripleFork_mk_zero (T : NumericalType) (t : ℕ)
    (indices : ℕ → Fin T.componentCount) (first m : ℕ) (hm : m < t + 1)
    (hm0 : m = 0) :
    doubleTripleFork T t indices first ⟨m, hm⟩ = indices first :=
  doubleTripleFork_of_zero T t indices first ⟨m, hm⟩ hm0

private lemma doubleTripleFork_mk (T : NumericalType) (t : ℕ)
    (indices : ℕ → Fin T.componentCount) (first m : ℕ) (hm : m < t + 1)
    (hm0 : m ≠ 0) :
    doubleTripleFork T t indices first ⟨m, hm⟩ = indices (m + 1) :=
  doubleTripleFork_of_ne_zero T t indices first ⟨m, hm⟩ hm0

/-- Every vertex of either fork is one of the `t + 2` named indices. -/
private lemma doubleTripleFork_mem_iio (T : NumericalType) {t first : ℕ}
    (hfirst : first < 2) (ht : 4 ≤ t)
    (indices : ℕ → Fin T.componentCount) (k : Fin (t + 1)) :
    ∃ m, m < t + 2 ∧ doubleTripleFork T t indices first k = indices m := by
  by_cases hk : k.val = 0
  · exact ⟨first, by omega, doubleTripleFork_of_zero T t indices first k hk⟩
  · exact ⟨k.val + 1, by have := k.isLt; omega,
      doubleTripleFork_of_ne_zero T t indices first k hk⟩

/-- Every vertex of either fork is a minus-two index. -/
private lemma isMinusTwoIndex_doubleTripleFork (T : NumericalType) {t first : ℕ}
    (hfirst : first < 2) (ht : 4 ≤ t)
    (indices : ℕ → Fin T.componentCount)
    (hminus : ∀ j < t + 2, IsMinusTwoIndex T (indices j)) (j : Fin (t + 1)) :
    IsMinusTwoIndex T (doubleTripleFork T t indices first j) := by
  obtain ⟨m, hm, hmj⟩ := doubleTripleFork_mem_iio T hfirst ht indices j
  rw [hmj]
  exact hminus m hm

/-- A component outside the named indices lies outside either fork. -/
private lemma doubleTripleFork_ne_of_outside (T : NumericalType) {t first : ℕ}
    (hfirst : first < 2) (ht : 4 ≤ t)
    (indices : ℕ → Fin T.componentCount) {k₀ : Fin T.componentCount}
    (hk₀ : ∀ j, j < t + 2 → indices j ≠ k₀) (r : Fin (t + 1)) :
    doubleTripleFork T t indices first r ≠ k₀ := by
  obtain ⟨m, hm, hmr⟩ := doubleTripleFork_mem_iio T hfirst ht indices r
  rw [hmr]
  exact hk₀ m hm

private lemma doubleTripleFork_injective (T : NumericalType) {t first : ℕ}
    (hfirst : first < 2) (ht : 4 ≤ t)
    (indices : ℕ → Fin T.componentCount)
    (hindices : Set.InjOn indices (Set.Iio (t + 2))) :
    Function.Injective (doubleTripleFork T t indices first) := by
  intro a b hab
  apply Fin.ext
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
  · omega
  · rw [doubleTripleFork_of_zero T t indices first a ha,
      doubleTripleFork_of_ne_zero T t indices first b hb] at hab
    have := hindices (show first ∈ Set.Iio (t + 2) by simp; omega)
      (show b.val + 1 ∈ Set.Iio (t + 2) by simp; have := b.isLt; omega) hab
    omega
  · rw [doubleTripleFork_of_ne_zero T t indices first a ha,
      doubleTripleFork_of_zero T t indices first b hb] at hab
    have := hindices
      (show a.val + 1 ∈ Set.Iio (t + 2) by simp; have := a.isLt; omega)
      (show first ∈ Set.Iio (t + 2) by simp; omega) hab
    omega
  · rw [doubleTripleFork_of_ne_zero T t indices first a ha,
      doubleTripleFork_of_ne_zero T t indices first b hb] at hab
    have := hindices
      (show a.val + 1 ∈ Set.Iio (t + 2) by simp; have := a.isLt; omega)
      (show b.val + 1 ∈ Set.Iio (t + 2) by simp; have := b.isLt; omega) hab
    omega

/-- The two forks of a double-triple configuration agree away from the vertex
each of them discards. -/
private lemma doubleTripleFork_eq_of_ne_zero (T : NumericalType) (t : ℕ)
    (indices : ℕ → Fin T.componentCount) (a b : ℕ) {k : Fin (t + 1)}
    (hk : k ≠ 0) :
    doubleTripleFork T t indices a k = doubleTripleFork T t indices b k := by
  have hk' : k.val ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
  rw [doubleTripleFork_of_ne_zero T t indices a k hk',
    doubleTripleFork_of_ne_zero T t indices b k hk']

/-- A sequence injective on an initial segment shorter than the index type
misses a component. -/
private lemma exists_outside_indices {n t : ℕ} (indices : ℕ → Fin n)
    (ht : t < n) :
    ∃ k : Fin n, ∀ j, j < t → indices j ≠ k := by
  classical
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun j : Fin t => indices j.val) := by
    intro k
    obtain ⟨j, hj, hjk⟩ := h k
    exact ⟨⟨j, hj⟩, hjk⟩
  have hcard := Fintype.card_le_of_surjective _ hsurj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Each of the two forks of a double-triple configuration has a fork shape. -/
private lemma exists_doubleTripleFork_shape (T : NumericalType) (t : ℕ)
    (ht : 4 ≤ t) (hproper : t + 2 < T.componentCount)
    (indices : ℕ → Fin T.componentCount)
    (hindices : Set.InjOn indices (Set.Iio (t + 2)))
    (hminus : ∀ j < t + 2, IsMinusTwoIndex T (indices j))
    (hchain : ∀ j, 1 ≤ j → j ≤ t - 1 →
      0 < T.intersection (indices j) (indices (j + 1)))
    (hright : 0 < T.intersection (indices (t - 1)) (indices (t + 1)))
    (first : ℕ) (hfirst : first < 2)
    (hedge : 0 < T.intersection (indices first) (indices 2)) :
    ∃ w : ℤ, ForkShape T t (doubleTripleFork T t indices first) w := by
  refine exists_forkShape_of_isMinusTwoIndex T t (by omega) (by omega)
    (doubleTripleFork T t indices first)
    (doubleTripleFork_injective T hfirst ht indices hindices) ?_ ?_ ?_
  · exact isMinusTwoIndex_doubleTripleFork T hfirst ht indices hminus
  · intro j
    have hjlt : (j : ℕ) < t - 1 := j.isLt
    by_cases hj0 : (j : ℕ) = 0
    · rw [doubleTripleFork_mk_zero T t indices first (j : ℕ) (by omega) hj0,
        doubleTripleFork_mk T t indices first ((j : ℕ) + 1) (by omega) (by omega),
        show (j : ℕ) + 1 + 1 = 2 by omega]
      exact ne_of_gt hedge
    · rw [doubleTripleFork_mk T t indices first (j : ℕ) (by omega) hj0,
        doubleTripleFork_mk T t indices first ((j : ℕ) + 1) (by omega) (by omega)]
      exact ne_of_gt (hchain ((j : ℕ) + 1) (by omega) (by omega))
  · rw [doubleTripleFork_mk T t indices first (t - 2) (by omega) (by omega),
      doubleTripleFork_mk T t indices first t (by omega) (by omega),
      show t - 2 + 1 = t - 1 by omega]
    exact ne_of_gt hright

/-- **Stacks Project, Tag 0C8H.** There is no proper double-triple
configuration consisting of distinct minus-two indices in a numerical type. -/
@[stacks 0C8H]
public lemma not_exists_double_triple_subgraph
    (T : NumericalType) (t : ℕ) (ht : 4 ≤ t)
    (hproper : t + 2 < T.componentCount) :
    ¬ ∃ indices : ℕ → Fin T.componentCount,
      Set.InjOn indices (Set.Iio (t + 2)) ∧
        (∀ j < t + 2, IsMinusTwoIndex T (indices j)) ∧
        (∀ j, 1 ≤ j → j ≤ t - 1 →
          0 < T.intersection (indices j) (indices (j + 1))) ∧
        0 < T.intersection (indices 0) (indices 2) ∧
        0 < T.intersection (indices (t - 1)) (indices (t + 1)) := by
  classical
  rintro ⟨indices, hindices, hminus, hchain, hleft, hright⟩
  obtain ⟨w₀, hs₀⟩ := exists_doubleTripleFork_shape T t ht hproper indices
    hindices hminus hchain hright 0 (by omega) hleft
  obtain ⟨w₁, hs₁⟩ := exists_doubleTripleFork_shape T t ht hproper indices
    hindices hminus hchain hright 1 (by omega)
    (by simpa using hchain 1 (by omega) (by omega))
  have hval (first : ℕ) :
      doubleTripleFork T t indices first (⟨1, by omega⟩ : Fin (t + 1)) =
        indices 2 :=
    doubleTripleFork_mk T t indices first 1 (by omega) (by omega)
  have hww : w₀ = w₁ := by
    have h₀ := hs₀.1 (⟨1, by omega⟩ : Fin (t + 1))
    have h₁ := hs₁.1 (⟨1, by omega⟩ : Fin (t + 1))
    rw [hval 0] at h₀
    rw [hval 1] at h₁
    exact h₀.symm.trans h₁
  subst hww
  have hzeroval (first : ℕ) :
      doubleTripleFork T t indices first (0 : Fin (t + 1)) = indices first :=
    doubleTripleFork_of_zero T t indices first _ rfl
  obtain ⟨k₀, hk₀⟩ := exists_outside_indices indices (by omega)
  refine not_two_forks_sharing_tail T t (by omega)
    (doubleTripleFork T t indices 0) (doubleTripleFork T t indices 1) w₀ hs₀ hs₁
    (isMinusTwoIndex_doubleTripleFork T (by omega) ht indices hminus)
    (isMinusTwoIndex_doubleTripleFork T (by omega) ht indices hminus)
    (doubleTripleFork_injective T (by omega) ht indices hindices)
    (fun k hk => doubleTripleFork_eq_of_ne_zero T t indices 0 1 hk) ?_ k₀ ?_ ?_
  · intro r
    rw [hzeroval 0]
    by_cases hr : r.val = 0
    · rw [doubleTripleFork_of_zero T t indices 1 r hr]
      intro heq
      have h := hindices (show (1 : ℕ) ∈ Set.Iio (t + 2) by simp)
        (show (0 : ℕ) ∈ Set.Iio (t + 2) by simp) heq
      omega
    · rw [doubleTripleFork_of_ne_zero T t indices 1 r hr]
      intro heq
      have h := hindices
        (show r.val + 1 ∈ Set.Iio (t + 2) by simp; have := r.isLt; omega)
        (show (0 : ℕ) ∈ Set.Iio (t + 2) by simp) heq
      omega
  · exact doubleTripleFork_ne_of_outside T (by omega) ht indices hk₀
  · exact doubleTripleFork_ne_of_outside T (by omega) ht indices hk₀

end AlgebraicGeometry.NumericalType
