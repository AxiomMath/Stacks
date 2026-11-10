module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.Algebra.Homology.FiniteFreeComplex.BoundedFreeComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exact complexes over a local ring of depth zero are trivial

This file proves that over a Noetherian local ring whose maximal ideal is an associated prime, an
exact `BoundedFreeComplex` is isomorphic to a direct sum of trivial complexes (Stacks, Tag 00MY),
by repeatedly splitting off identity blocks.
-/

@[expose] public section

open Matrix

variable {R : Type*} [CommRing R]

namespace BoundedFreeComplex

/-- The block-diagonal matrix `diag(1, A)` obtained by adjoining a leading `1 × 1` identity block
to a matrix `A`. -/
def padBlock {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) : Matrix (Fin (a + 1)) (Fin (b + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases (1 : R) (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

/-- The corner entry of `padBlock A` is `1`. -/
@[simp] theorem padBlock_zero_zero {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) :
    padBlock A 0 0 = 1 := rfl
/-- The first row of `padBlock A` vanishes away from the corner. -/
@[simp] theorem padBlock_zero_succ {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (j : Fin b) :
    padBlock A 0 j.succ = 0 := rfl
/-- The first column of `padBlock A` vanishes away from the corner. -/
@[simp] theorem padBlock_succ_zero {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i : Fin a) :
    padBlock A i.succ 0 = 0 := rfl
/-- The lower-right block of `padBlock A` is `A`. -/
@[simp] theorem padBlock_succ_succ {a b : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (i : Fin a) (j : Fin b) : padBlock A i.succ j.succ = A i j := rfl

/-- Padding is multiplicative: `padBlock (A * B) = padBlock A * padBlock B`. -/
theorem padBlock_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R) :
    padBlock A * padBlock B = padBlock (A * B) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply]

/-- Padding the identity gives the identity. -/
theorem padBlock_one {a : ℕ} : padBlock (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp []
  · simp [ Fin.ext_iff]
  · simp [ Fin.ext_iff]
  · simp only [padBlock_succ_succ, Matrix.one_apply, Fin.succ_inj]

/-- Padding commutes with taking inverses. -/
theorem padBlock_inv {a : ℕ} (A : Matrix (Fin a) (Fin a) R) (hA : IsUnit A.det) :
    (padBlock A)⁻¹ = padBlock A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [padBlock_mul, Matrix.mul_nonsing_inv _ hA, padBlock_one]

/-- Padding does not change the determinant. -/
theorem padBlock_det {a : ℕ} (A : Matrix (Fin a) (Fin a) R) :
    (padBlock A).det = A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [padBlock_zero_zero, padBlock_zero_succ, Fin.val_zero, pow_zero, one_mul,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1

/-- Padding a partial permutation matrix with a leading identity block gives a partial
permutation matrix. -/
theorem padBlock_isPartialPerm [Nontrivial R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (hA : IsPartialPerm A) : IsPartialPerm (padBlock A) := by
  obtain ⟨h01, hrow, hcol⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [h01]
  · intro i j j'
    refine Fin.cases ?_ (fun i' => ?_) i <;>
      refine Fin.cases ?_ (fun jj => ?_) j <;>
      refine Fin.cases ?_ (fun jj' => ?_) j' <;>
      intro hj hj' <;>
      first
        | rfl
        | (rw [padBlock_zero_succ] at hj; exact absurd hj zero_ne_one)
        | (rw [padBlock_zero_succ] at hj'; exact absurd hj' zero_ne_one)
        | (rw [padBlock_succ_zero] at hj; exact absurd hj zero_ne_one)
        | (rw [padBlock_succ_zero] at hj'; exact absurd hj' zero_ne_one)
        | (exact congrArg Fin.succ (hrow i' jj jj' (by simpa using hj) (by simpa using hj')))
  · intro i i' j
    refine Fin.cases ?_ (fun jj => ?_) j <;>
      refine Fin.cases ?_ (fun ii => ?_) i <;>
      refine Fin.cases ?_ (fun ii' => ?_) i' <;>
      intro hi hi' <;>
      first
        | rfl
        | (rw [padBlock_zero_succ] at hi; exact absurd hi zero_ne_one)
        | (rw [padBlock_zero_succ] at hi'; exact absurd hi' zero_ne_one)
        | (rw [padBlock_succ_zero] at hi; exact absurd hi zero_ne_one)
        | (rw [padBlock_succ_zero] at hi'; exact absurd hi' zero_ne_one)
        | (exact congrArg Fin.succ (hcol ii ii' jj (by simpa using hi) (by simpa using hi')))

/-- The exactness equation is preserved under reindexing the free modules along rank
equalities. -/
theorem exact_eqn_reindex {a b c a' b' c' : ℕ}
    (Mi : Matrix (Fin a) (Fin b) R) (Mi1 : Matrix (Fin b) (Fin c) R)
    (ea : Fin a' ≃ Fin a) (eb : Fin b' ≃ Fin b) (ec : Fin c' ≃ Fin c)
    (h : LinearMap.ker Mi.toLin' = LinearMap.range Mi1.toLin') :
    LinearMap.ker (Mi.submatrix ea eb).toLin' = LinearMap.range (Mi1.submatrix eb ec).toLin' := by
  have hi : (Mi.submatrix ea eb).toLin'
      = (LinearEquiv.funCongrLeft R R ea : (Fin a → R) ≃ₗ[R] (Fin a' → R)).toLinearMap
        ∘ₗ Mi.toLin'
        ∘ₗ (LinearEquiv.funCongrLeft R R eb.symm : (Fin b' → R) ≃ₗ[R] (Fin b → R)).toLinearMap := by
    rw [show ea = ⇑(ea : Fin a' ≃ Fin a) from rfl, show eb = ⇑(eb : Fin b' ≃ Fin b) from rfl,
        Matrix.toLin'_submatrix]; rfl
  have hi1 : (Mi1.submatrix eb ec).toLin'
      = (LinearEquiv.funCongrLeft R R eb : (Fin b → R) ≃ₗ[R] (Fin b' → R)).toLinearMap
        ∘ₗ Mi1.toLin'
        ∘ₗ (LinearEquiv.funCongrLeft R R ec.symm : (Fin c' → R) ≃ₗ[R] (Fin c → R)).toLinearMap := by
    rw [show eb = ⇑(eb : Fin b' ≃ Fin b) from rfl, show ec = ⇑(ec : Fin c' ≃ Fin c) from rfl,
        Matrix.toLin'_submatrix]; rfl
  rw [hi, hi1, LinearEquiv.ker_comp, LinearMap.ker_comp]
  rw [← LinearMap.comp_assoc, LinearEquiv.range_comp, LinearMap.range_comp]
  rw [h, Submodule.comap_equiv_eq_map_symm]
  congr 1

/-- Prepending a zero column to a partial permutation matrix gives a partial permutation
matrix. -/
theorem isPartialPerm_prepend_zero_col [Nontrivial R] {m β : ℕ}
    (M : Matrix (Fin m) (Fin (β + 1)) R) (hz : ∀ p, M p 0 = 0)
    (h : IsPartialPerm (M.submatrix id Fin.succ)) : IsPartialPerm M := by
  obtain ⟨h01, hrow, hcol⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    refine Fin.cases ?_ (fun j' => ?_) j
    · rw [hz i]; left; rfl
    · have := h01 i j'
      simpa [Matrix.submatrix_apply] using this
  · intro i j j'
    refine Fin.cases ?_ (fun jj => ?_) j <;> refine Fin.cases ?_ (fun jj' => ?_) j' <;>
      intro hj hj'
    · rfl
    · rw [hz i] at hj; exact absurd hj zero_ne_one
    · rw [hz i] at hj'; exact absurd hj' zero_ne_one
    · have := hrow i jj jj' (by simpa [Matrix.submatrix_apply] using hj)
        (by simpa [Matrix.submatrix_apply] using hj')
      exact congrArg Fin.succ this
  · intro i i' j
    refine Fin.cases ?_ (fun jj => ?_) j <;> intro hi hi'
    · rw [hz i] at hi; exact absurd hi zero_ne_one
    · exact hcol i i' jj (by simpa [Matrix.submatrix_apply] using hi)
        (by simpa [Matrix.submatrix_apply] using hi')

/-- Reindexing rows and columns of a square matrix along `Fin.cast` does not change the
determinant. -/
private theorem det_submatrix_fin_cast {a b : ℕ} (h : a = b) (A : Matrix (Fin b) (Fin b) R) :
    (A.submatrix (Fin.cast h) (Fin.cast h)).det = A.det :=
  Matrix.det_submatrix_equiv_self (finCongr h) A

/-- Let `C₁` be an exact complex and `t` an index with `1 ≤ t ≤ e`, `n t > 0` and
`n (t + 1) = 0`, such that `C₁.φ (t - 1)` has block form `diag(1, ψ)` and, if `t ≥ 2`, the column
of `C₁.φ (t - 2)` at the pivot index vanishes. Then there is an exact complex `C'` of strictly
smaller total rank such that `C₁` is trivializable whenever `C'` is. -/
theorem exists_exact_totalRank_lt_of_blockDiag_one [IsNoetherianRing R] [IsLocalRing R]
    (C₁ : BoundedFreeComplex R) (hC₁ : C₁.Exact)
    (t : ℕ) (ht1 : 1 ≤ t) (hte : t ≤ C₁.e) (htpos : 0 < C₁.n t) (htzero : C₁.n (t + 1) = 0)
    (α β : ℕ) (hα : C₁.n (t - 1) = α + 1) (hβ : C₁.n (t - 1 + 1) = β + 1)
    (ψ : Matrix (Fin α) (Fin β) R)
    (hcorner : C₁.φ (t - 1) (Fin.cast hα.symm 0) (Fin.cast hβ.symm 0) = 1)
    (hrow0 : ∀ q : Fin β, C₁.φ (t - 1) (Fin.cast hα.symm 0) (Fin.cast hβ.symm q.succ) = 0)
    (hcol0 : ∀ p : Fin α, C₁.φ (t - 1) (Fin.cast hα.symm p.succ) (Fin.cast hβ.symm 0) = 0)
    (hψ : ∀ (p : Fin α) (q : Fin β),
      C₁.φ (t - 1) (Fin.cast hα.symm p.succ) (Fin.cast hβ.symm q.succ) = ψ p q)
    (hpivotcol : ∀ (_ : 2 ≤ t), ∃ hα2 : C₁.n (t - 2 + 1) = α + 1,
      (∀ p, C₁.φ (t - 2) p (Fin.cast hα2.symm 0) = 0)) :
    ∃ C' : BoundedFreeComplex R, C'.Exact ∧ C'.totalRank < C₁.totalRank ∧
      (Trivializable C' → Trivializable C₁) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hα hβ hcorner hrow0 hcol0 hψ hpivotcol htpos htzero ⊢
  have htzero' : C₁.n (s + 2) = 0 := htzero
  set n' : ℕ → ℕ := Function.update (Function.update C₁.n s α) (s + 1) β with hn'def
  have ens : n' s = α := by
    rw [hn'def, Function.update_of_ne (by omega : s ≠ s + 1), Function.update_self]
  have ens1 : n' (s + 1) = β := by rw [hn'def, Function.update_self]
  have enother : ∀ i, i ≠ s → i ≠ s + 1 → n' i = C₁.n i := by
    intro i h1 h2; rw [hn'def, Function.update_of_ne h2, Function.update_of_ne h1]
  set φ' : ∀ i : ℕ, Matrix (Fin (n' i)) (Fin (n' (i + 1))) R := fun i =>
    if hi : i = s then
      ψ.submatrix (Fin.cast (hi ▸ ens)) (Fin.cast (by rw [hi]; exact ens1))
    else if hi1 : i + 1 = s then
      (C₁.φ i).submatrix (Fin.cast (enother i (by omega) (by omega)))
        (fun (j : Fin (n' (i + 1))) =>
          (Fin.cast (show α + 1 = C₁.n (i + 1) by rw [hi1]; exact hα.symm)
            ((Fin.cast (show n' (i + 1) = α by rw [hi1]; exact ens) j).succ)))
    else if hi2 : i = s + 1 then
      Matrix.of (fun (_ : Fin (n' i)) (j : Fin (n' (i + 1))) =>
        (Fin.cast (by rw [hi2]; rw [enother (s + 2) (by omega) (by omega)]; exact htzero') j).elim0)
    else
      (C₁.φ i).submatrix (Fin.cast (enother i hi hi2))
        (Fin.cast (enother (i + 1) (by omega) (by omega))) with hφ'def
  have eval_s : ∀ (p : Fin (n' s)) (q : Fin (n' (s + 1))),
      φ' s p q = ψ (Fin.cast ens p) (Fin.cast ens1 q) := by
    intro p q
    simp only [hφ'def, dite_eq_left rfl, Matrix.submatrix_apply]
  have eval_sm1 : ∀ (i : ℕ) (hi1 : i + 1 = s) (p : Fin (n' i)) (q : Fin (n' (i + 1))),
      φ' i p q = C₁.φ i (Fin.cast (enother i (by omega) (by omega)) p)
        (Fin.cast (show α + 1 = C₁.n (i + 1) by rw [hi1]; exact hα.symm)
          ((Fin.cast (show n' (i + 1) = α by rw [hi1]; exact ens) q).succ)) := by
    intro i hi1 p q
    have hine : i ≠ s := by omega
    simp only [hφ'def, dite_eq_right hine, dite_eq_left hi1, Matrix.submatrix_apply]
  have eval_other : ∀ (i : ℕ) (hi : i ≠ s) (hi1 : i + 1 ≠ s) (hi2 : i ≠ s + 1)
      (p : Fin (n' i)) (q : Fin (n' (i + 1))),
      φ' i p q = C₁.φ i (Fin.cast (enother i hi hi2) p)
        (Fin.cast (enother (i + 1) (by omega) (by omega)) q) := by
    intro i hi hi1 hi2 p q
    simp only [hφ'def, dite_eq_right hi, dite_eq_right hi1, dite_eq_right hi2,
               Matrix.submatrix_apply]
  have mat_other : ∀ (i : ℕ) (hi : i ≠ s) (hi1 : i + 1 ≠ s) (hi2 : i ≠ s + 1),
      φ' i = (C₁.φ i).submatrix (Fin.cast (enother i hi hi2))
        (Fin.cast (enother (i + 1) (by omega) (by omega))) := by
    intro i hi hi1 hi2
    simp only [hφ'def, dite_eq_right hi, dite_eq_right hi1, dite_eq_right hi2]
  have mat_s : φ' s = ψ.submatrix (Fin.cast ens) (Fin.cast ens1) := by
    simp only [hφ'def, dite_eq_left rfl]
  have hcomplex : ∀ i : ℕ, φ' i * φ' (i + 1) = 0 := by
    intro i
    by_cases hcs : i + 2 = s
    · have hi_ne_s : i ≠ s := by omega
      have hi_ne_s1 : i ≠ s + 1 := by omega
      have hi1_ne_s : i + 1 ≠ s := by omega
      have hi1_ne_s1 : i + 1 ≠ s + 1 := by omega
      have hi1p1 : i + 1 + 1 = s := by omega
      ext p q
      rw [Matrix.mul_apply, Matrix.zero_apply]
      have hC1 := C₁.isComplex i
      have hkey := congrFun (congrFun hC1 (Fin.cast (enother i hi_ne_s hi_ne_s1) p))
        (Fin.cast (show α + 1 = C₁.n (i + 1 + 1) by rw [hi1p1]; exact hα.symm)
          ((Fin.cast (show n' (i + 1 + 1) = α by rw [hi1p1]; exact ens) q).succ))
      rw [Matrix.mul_apply, Matrix.zero_apply] at hkey
      rw [← hkey, ← Equiv.sum_comp (finCongr (enother (i + 1) hi1_ne_s hi1_ne_s1)).symm]
      apply Finset.sum_congr rfl
      intro k _
      rw [eval_other i hi_ne_s hi1_ne_s hi_ne_s1, eval_sm1 (i + 1) hi1p1]
      congr 2
    by_cases hbs : i + 1 = s
    · subst hbs
      have hi_ne_s : i ≠ i + 1 := by omega
      have hi_ne_s1 : i ≠ i + 1 + 1 := by omega
      set A₁ : Matrix (Fin (C₁.n i)) (Fin (α + 1)) R :=
        (C₁.φ i).submatrix id (Fin.cast hα.symm) with hA₁
      set B₁ : Matrix (Fin (α + 1)) (Fin (β + 1)) R :=
        (C₁.φ (i + 1)).submatrix (Fin.cast hα.symm) (Fin.cast hβ.symm) with hB₁
      have hAB : A₁ * B₁ = 0 := by
        refine (Matrix.submatrix_mul_equiv (C₁.φ i) (C₁.φ (i + 1)) id (finCongr hα.symm)
          (finCongr hβ.symm)).trans ?_
        rw [C₁.isComplex i]
        simp
      have hrowB : ∀ q : Fin β, B₁ 0 q.succ = 0 := by
        intro q
        rw [hB₁, Matrix.submatrix_apply]
        have := hrow0 q
        exact this
      have hpeel := peel_drop_both A₁ B₁ hAB hrowB
      ext p q
      rw [Matrix.mul_apply, Matrix.zero_apply]
      have hpeelpq := congrFun (congrFun hpeel (Fin.cast (enother i hi_ne_s hi_ne_s1) p))
        (Fin.cast (ens1) q)
      rw [Matrix.mul_apply, Matrix.zero_apply] at hpeelpq
      rw [← hpeelpq, ← Equiv.sum_comp (finCongr ens).symm]
      apply Finset.sum_congr rfl
      intro k _
      rw [eval_sm1 i rfl, eval_s]
      rw [hA₁, hB₁, Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.submatrix_apply, ← hψ]
      congr 1
    by_cases his : i = s
    · have hempty : n' (i + 1 + 1) = 0 := by
        rw [enother (i + 1 + 1) (by omega) (by omega)]; rw [his]; exact htzero'
      ext p q
      exact (Fin.cast hempty q).elim0
    by_cases his1 : i = s + 1
    · have hempty : n' (i + 1) = 0 := by
        rw [enother (i + 1) (by omega) (by omega)]; rw [his1]; exact htzero'
      ext p q
      rw [Matrix.mul_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro k _
      exact (Fin.cast hempty k).elim0
    · have hi_ne_s : i ≠ s := his
      have hi_ne_s1 : i ≠ s + 1 := his1
      have hi1_ne_s : i + 1 ≠ s := hbs
      have hi1_ne_s1 : i + 1 ≠ s + 1 := by omega
      have hi2_ne_s : i + 2 ≠ s := hcs
      ext p q
      rw [Matrix.mul_apply, Matrix.zero_apply]
      have hC1 := C₁.isComplex i
      have hkey := congrFun (congrFun hC1 (Fin.cast (enother i hi_ne_s hi_ne_s1) p))
        (Fin.cast (enother (i + 1 + 1) (by omega) (by omega)) q)
      rw [Matrix.mul_apply, Matrix.zero_apply] at hkey
      rw [← hkey, ← Equiv.sum_comp (finCongr (enother (i + 1) hi1_ne_s hi1_ne_s1)).symm]
      apply Finset.sum_congr rfl
      intro k _
      rw [eval_other i hi_ne_s hi1_ne_s hi_ne_s1, eval_other (i + 1) hi1_ne_s hi2_ne_s hi1_ne_s1]
      congr 1
  have hpcol : ∀ i (hi : i + 1 = s) (p : Fin (C₁.n i)),
      C₁.φ i p (Fin.cast (hi ▸ hα).symm 0) = 0 := by
    intro i hi p
    obtain ⟨_, hpc⟩ := hpivotcol (by omega)
    obtain rfl : s + 1 - 2 = i := by omega
    exact hpc p
  set C' : BoundedFreeComplex R :=
    { e := C₁.e
      n := n'
      φ := φ'
      length := by
        intro i hi
        have hine : i ≠ s := by omega
        have hine1 : i ≠ s + 1 := by omega
        rw [enother i hine hine1]
        exact C₁.length i hi
      isComplex := hcomplex } with hC'def
  set M : Matrix (Fin (α + 1)) (Fin (β + 1)) R :=
    (C₁.φ s).submatrix (Fin.cast hα.symm) (Fin.cast hβ.symm) with hMdef
  have hM00 : M 0 0 = 1 := by rw [hMdef, Matrix.submatrix_apply]; exact hcorner
  have hM0s : ∀ q : Fin β, M 0 q.succ = 0 := by
    intro q; rw [hMdef, Matrix.submatrix_apply]; exact hrow0 q
  have hMs0 : ∀ p : Fin α, M p.succ 0 = 0 := by
    intro p; rw [hMdef, Matrix.submatrix_apply]; exact hcol0 p
  have hMss : ∀ (p : Fin α) (q : Fin β), M p.succ q.succ = ψ p q := by
    intro p q; rw [hMdef, Matrix.submatrix_apply]; exact hψ p q
  have hCsInj : Function.Injective (C₁.φ s).toLin' :=
    top_map_injective C₁ hC₁ s (by omega) htzero'
  have hψinj : Function.Injective ψ.toLin' := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff] at hCsInj ⊢
    intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
    set w : Fin (C₁.n (s + 1)) → R :=
      fun j => (Fin.cons 0 v : Fin (β + 1) → R) (Fin.cast hβ j) with hwdef
    have hMw : (C₁.φ s).mulVec w = 0 := by
      funext i'
      set i : Fin (α + 1) := Fin.cast hα i' with hidef
      have hreidx : (C₁.φ s).mulVec w i'
          = M.mulVec (fun q => (Fin.cons 0 v : Fin (β + 1) → R) q) i := by
        rw [hMdef, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
        rw [← Equiv.sum_comp (finCongr hβ.symm)]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Matrix.submatrix_apply, hwdef, hidef, finCongr_apply, Fin.cast_cast,
          Fin.cast_eq_self]
      rw [Pi.zero_apply, hreidx, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨p, hp⟩
      · rw [hi0, hM00, Fin.cons_zero, mul_zero, zero_add]
        apply Finset.sum_eq_zero; intro q _
        rw [hM0s q, zero_mul]
      · rw [hp, hMs0 p, Fin.cons_zero, mul_zero, zero_add]
        have : ∑ q : Fin β, M p.succ q.succ * (Fin.cons (0 : R) v : Fin (β + 1) → R) q.succ
            = ∑ q : Fin β, ψ p q * v q := by
          apply Finset.sum_congr rfl; intro q _; rw [hMss p q, Fin.cons_succ]
        rw [this]
        have := congrFun hv p
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
        exact this
    have hwker : w ∈ LinearMap.ker (C₁.φ s).toLin' := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact hMw
    have hw0 : w = 0 := hCsInj w hwker
    funext q
    have : w (Fin.cast hβ.symm q.succ) = 0 := by rw [hw0]; rfl
    rw [hwdef] at this
    simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.cons_succ] at this
    exact this
  refine ⟨C', ?_, ?_, ?_⟩
  · change ∀ i, i ≤ C₁.e →
      LinearMap.ker (φ' i).toLin' = LinearMap.range (φ' (i + 1)).toLin'
    intro i hi
    by_cases hcs : i + 2 = s
    · have hs2 : 2 ≤ s := by omega
      obtain ⟨hα2, hpc⟩ := hpivotcol (by omega)
      have hi_s : i ≠ s := by omega
      have hi_s1 : i ≠ s + 1 := by omega
      have hi1_s : i + 1 ≠ s := by omega
      have hi1_s1 : i + 1 ≠ s + 1 := by omega
      have hi1p1 : i + 1 + 1 = s := by omega
      set e1 : Fin (n' (i + 1)) ≃ Fin (C₁.n (i + 1)) := finCongr (enother (i + 1) hi1_s hi1_s1)
          with he1
      have hcs' : C₁.n (i + 1 + 1) = α + 1 := by rw [hi1p1]; exact hα
      set ec : Fin (α + 1) ≃ Fin (C₁.n (i + 1 + 1)) := finCongr hcs'.symm with hec
      set Bmid : Matrix (Fin (n' (i + 1))) (Fin (α + 1)) R :=
        (C₁.φ (i + 1)).submatrix e1 ec with hBmid
      have hcs2 : n' (i + 1 + 1) = α := by rw [hi1p1]; exact ens
      have hφ'eq : φ' (i + 1) = (Bmid.submatrix id Fin.succ).submatrix id (finCongr hcs2) := by
        ext p q
        rw [eval_sm1 (i + 1) hi1p1, Matrix.submatrix_apply, Matrix.submatrix_apply, hBmid,
          Matrix.submatrix_apply]
        simp only [id_eq, he1, hec, finCongr_apply]
      have hsi : s + 1 - 2 = i + 1 := by omega
      have hBcol0 : ∀ p, Bmid p 0 = 0 := by
        intro p
        rw [hBmid, Matrix.submatrix_apply]
        have := hpc (Fin.cast (by rw [hsi]) (e1 p))
        convert this using 2 <;>
          first
          | omega
          | (refine (Fin.heq_ext_iff (by rw [hsi])).mpr ?_; simp [hec])
      rw [hφ'eq, range_reindex_col, range_drop_zero_col Bmid hBcol0]
      rw [mat_other i hi_s hi1_s hi_s1, hBmid]
      exact exact_eqn_reindex (C₁.φ i) (C₁.φ (i + 1))
        (finCongr (enother i hi_s hi_s1)) e1 ec (hC₁ i hi)
    by_cases hbs : i + 1 = s
    · subst hbs
      have hi_s : i ≠ i + 1 := by omega
      have hi_s1 : i ≠ i + 1 + 1 := by omega
      apply le_antisymm
      · intro v hv
        rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
        have hcol0' := hpcol i rfl
        set w : Fin (C₁.n (i + 1)) → R :=
          fun K =>
            (Fin.cons 0 (fun q => v (Fin.cast ens.symm q)) : Fin (α + 1) → R) (Fin.cast hα K)
            with hwdef
        have hwker : w ∈ LinearMap.ker (C₁.φ i).toLin' := by
          rw [LinearMap.mem_ker, Matrix.toLin'_apply]
          funext p
          rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← Equiv.sum_comp (finCongr hα.symm)]
          rw [Fin.sum_univ_succ, hwdef]
          simp only [finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.cons_zero, mul_zero,
            zero_add]
          have hvp := congrFun hv (Fin.cast (enother i hi_s hi_s1).symm p)
          rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at hvp
          rw [← hvp, ← Equiv.sum_comp (finCongr ens.symm)]
          apply Finset.sum_congr rfl
          intro q _
          rw [eval_sm1 i rfl]
          simp only [finCongr_apply, Fin.cons_succ, Fin.cast_cast, Fin.cast_eq_self]
        rw [hC₁ i hi] at hwker
        obtain ⟨z, hz⟩ := hwker
        rw [Matrix.toLin'_apply] at hz
        rw [LinearMap.mem_range]
        refine ⟨fun j => z (Fin.cast hβ.symm (Fin.cast ens1 j).succ), ?_⟩
        rw [Matrix.toLin'_apply]
        funext p
        have hzp := congrFun hz (Fin.cast hα.symm (Fin.cast ens p).succ)
        rw [Matrix.mulVec, dotProduct] at hzp
        rw [Matrix.mulVec, dotProduct]
        have hwval : w (Fin.cast hα.symm (Fin.cast ens p).succ) = v p := by
          rw [hwdef]
          simp only [ Fin.cast_cast, Fin.cast_eq_self, Fin.cons_succ]
        rw [hwval] at hzp
        rw [← hzp]
        rw [← Equiv.sum_comp (finCongr ens1.symm) (fun j => φ' (i + 1) p j *
              z (Fin.cast hβ.symm (Fin.cast ens1 j).succ))]
        rw [← Equiv.sum_comp (finCongr hβ.symm)
              (fun K => C₁.φ (i + 1) (Fin.cast hα.symm (Fin.cast ens p).succ) K * z K)]
        rw [Fin.sum_univ_succ]
        have hcolval : C₁.φ (i + 1) (Fin.cast hα.symm (Fin.cast ens p).succ)
            ((finCongr hβ.symm) 0) = 0 := hcol0 (Fin.cast ens p)
        rw [hcolval, zero_mul, zero_add]
        apply Finset.sum_congr rfl
        intro q _
        rw [eval_s]
        have hψq : C₁.φ (i + 1) (Fin.cast hα.symm (Fin.cast ens p).succ)
            ((finCongr hβ.symm) q.succ) = ψ (Fin.cast ens p) q := by
          have := hψ (Fin.cast ens p) q
          exact this
        rw [hψq]
        congr 1
      · rw [LinearMap.range_le_iff_comap, eq_top_iff]
        intro u _
        rw [Submodule.mem_comap, LinearMap.mem_ker, ← LinearMap.comp_apply,
          ← Matrix.toLin'_mul, hcomplex i]
        simp
    by_cases his : i = s
    · subst his
      have hrangebot : LinearMap.range (φ' (i + 1)).toLin' = ⊥ := by
        apply range_eq_bot_of_zero_source (show n' (i + 1 + 1) = 0 by
          rw [enother (i + 1 + 1) (by omega) (by omega)]; exact htzero')
      rw [hrangebot, LinearMap.ker_eq_bot, mat_s]
      rw [show ψ.submatrix (Fin.cast ens) (Fin.cast ens1)
          = ψ.submatrix (finCongr ens) (finCongr ens1) from rfl]
      rw [Matrix.toLin'_submatrix, LinearMap.coe_comp, LinearMap.coe_comp]
      apply Function.Injective.comp
      · exact LinearMap.funLeft_injective_of_surjective R R _ (finCongr ens).surjective
      apply Function.Injective.comp hψinj
      exact LinearMap.funLeft_injective_of_surjective R R _ (finCongr ens1).symm.surjective
    by_cases his1 : i = s + 1
    · have hz : n' (i + 1) = 0 := by
        rw [enother (i + 1) (by omega) (by omega)]; rw [his1]; exact htzero'
      have : Subsingleton (Fin (n' (i + 1)) → R) := by
        rw [hz]; infer_instance
      exact Subsingleton.elim _ _
    · have hi_s : i ≠ s := his
      have hi_s1 : i ≠ s + 1 := his1
      have hi1_s : i + 1 ≠ s := hbs
      have hi1_s1 : i + 1 ≠ s + 1 := by omega
      have hi2_s : i + 2 ≠ s := hcs
      have hi2_s1 : i + 1 + 1 ≠ s + 1 := by omega
      rw [mat_other i hi_s hi1_s hi_s1, mat_other (i + 1) hi1_s hi2_s hi1_s1]
      exact exact_eqn_reindex (C₁.φ i) (C₁.φ (i + 1))
        (finCongr (enother i hi_s hi_s1)) (finCongr (enother (i + 1) (by omega) (by omega)))
        (finCongr (enother (i + 1 + 1) (by omega) (by omega))) (hC₁ i hi)
  · change (∑ i ∈ Finset.range (C₁.e + 1), n' i) < ∑ i ∈ Finset.range (C₁.e + 1), C₁.n i
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = s
      · rw [hi, ens, hα]; omega
      · by_cases hi1 : i = s + 1
        · rw [hi1, ens1, hβ]; omega
        · rw [enother i hi hi1]
    · refine ⟨s, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · rw [ens, hα]; omega
  · intro hC'triv
    obtain ⟨D', g', hD'e, hD'n, hD'triv⟩ := hC'triv
    have hNT : Nontrivial R := inferInstance
    set Ppad : ∀ i, Matrix (Fin (C₁.n i)) (Fin (C₁.n i)) R := fun i =>
      if hi : i = s then
        (padBlock ((g'.P i).submatrix (Fin.cast (hi ▸ ens).symm) (Fin.cast (hi ▸
            ens).symm))).submatrix
          (Fin.cast (hi ▸ hα)) (Fin.cast (hi ▸ hα))
      else if hi1 : i = s + 1 then
        (padBlock ((g'.P i).submatrix (Fin.cast (hi1 ▸ ens1).symm) (Fin.cast (hi1 ▸
            ens1).symm))).submatrix
          (Fin.cast (hi1 ▸ hβ)) (Fin.cast (hi1 ▸ hβ))
      else
        (g'.P i).submatrix (Fin.cast (enother i hi hi1).symm) (Fin.cast (enother i hi hi1).symm)
      with hPpaddef
    have hPpadunit : ∀ i, IsUnit (Ppad i).det := by
      intro i
      simp only [hPpaddef]
      by_cases hi : i = s
      · rw [dite_eq_left hi, det_submatrix_fin_cast, padBlock_det, det_submatrix_fin_cast]
        exact g'.unit i
      · rw [dite_eq_right hi]
        by_cases hi1 : i = s + 1
        · rw [dite_eq_left hi1, det_submatrix_fin_cast, padBlock_det, det_submatrix_fin_cast]
          exact g'.unit i
        · rw [dite_eq_right hi1, det_submatrix_fin_cast]
          exact g'.unit i
    set D : BoundedFreeComplex R :=
      { e := C₁.e
        n := C₁.n
        φ := fun i => (Ppad i)⁻¹ * C₁.φ i * Ppad (i + 1)
        length := C₁.length
        isComplex := by
          intro i
          have h1 : Ppad (i + 1) * (Ppad (i + 1))⁻¹ = 1 :=
            Matrix.mul_nonsing_inv _ (hPpadunit (i + 1))
          calc ((Ppad i)⁻¹ * C₁.φ i * Ppad (i + 1)) *
                  ((Ppad (i + 1))⁻¹ * C₁.φ (i + 1) * Ppad (i + 1 + 1))
              = (Ppad i)⁻¹ * C₁.φ i * (Ppad (i + 1) * (Ppad (i + 1))⁻¹) * C₁.φ (i + 1) *
                  Ppad (i + 1 + 1) := by simp only [Matrix.mul_assoc]
            _ = (Ppad i)⁻¹ * (C₁.φ i * C₁.φ (i + 1)) * Ppad (i + 1 + 1) := by
                rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_one]
            _ = 0 := by rw [C₁.isComplex i]; simp } with hDdef
    have htrans : ∀ i, transportφ C₁ D (fun _ => rfl) i = D.φ i := by
      intro i; unfold transportφ; ext x y; simp [Matrix.submatrix_apply]
    set fD : C₁.Iso D :=
      { hn := fun _ => rfl
        P := Ppad
        unit := hPpadunit
        comm := by
          intro i
          rw [htrans]
          change Ppad i * ((Ppad i)⁻¹ * C₁.φ i * Ppad (i + 1)) = C₁.φ i * Ppad (i + 1)
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
              Matrix.mul_nonsing_inv _ (hPpadunit i), Matrix.one_mul] } with hfD
    refine ⟨D, fD, rfl, fun _ => rfl, ?_⟩
    set D'φ' : ∀ i, Matrix (Fin (n' i)) (Fin (n' (i + 1))) R :=
      fun i => transportφ C' D' g'.hn i with hD'φ'def
    have hD'φ'pp : ∀ i, IsPartialPerm (D'φ' i) := by
      intro i
      rw [hD'φ'def]
      unfold transportφ
      exact isPartialPerm_submatrix (D'.φ i) (finCongr (g'.hn i)) (finCongr (g'.hn (i + 1)))
        (hD'triv i)
    have hgcomm : ∀ i, g'.P i * D'φ' i = φ' i * g'.P (i + 1) := g'.comm
    have hD'φ : ∀ i, D'φ' i = (g'.P i)⁻¹ * φ' i * g'.P (i + 1) := by
      intro i
      rw [Matrix.mul_assoc, ← hgcomm i, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (g'.unit i), Matrix.one_mul]
    intro i
    change IsPartialPerm ((Ppad i)⁻¹ * C₁.φ i * Ppad (i + 1))
    by_cases his1 : i = s + 1
    · apply isPartialPerm_of_no_cols
      rw [his1]; exact htzero'
    by_cases his : i = s
    · subst his
      set Qs : Matrix (Fin α) (Fin α) R :=
        (g'.P i).submatrix (finCongr ens.symm) (finCongr ens.symm) with hQs
      set Qs1 : Matrix (Fin β) (Fin β) R :=
        (g'.P (i + 1)).submatrix (finCongr ens1.symm) (finCongr ens1.symm) with hQs1
      have hPi : Ppad i = (padBlock Qs).submatrix (finCongr hα) (finCongr hα) := by
        simp only [hPpaddef, dite_eq_left rfl]
        rfl
      have hPi1 : Ppad (i + 1) = (padBlock Qs1).submatrix (finCongr hβ) (finCongr hβ) := by
        simp only [hPpaddef, dite_eq_right (by omega : i + 1 ≠ i)]
        rfl
      have hMpsi : M = padBlock ψ := by
        ext a b
        refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b
        · rw [hM00, padBlock_zero_zero]
        · rw [hM0s b', padBlock_zero_succ]
        · rw [hMs0 a', padBlock_succ_zero]
        · rw [hMss a' b', padBlock_succ_succ]
      have hC1 : C₁.φ i = (padBlock ψ).submatrix (finCongr hα) (finCongr hβ) := by
        rw [← hMpsi, hMdef]
        ext a b
        simp only [Matrix.submatrix_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
      have hψeq : ψ = (φ' i).submatrix (finCongr ens.symm) (finCongr ens1.symm) := by
        rw [mat_s]
        ext a b
        simp only [Matrix.submatrix_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
      have hinner : Qs⁻¹ * ψ * Qs1
          = (D'φ' i).submatrix (finCongr ens.symm) (finCongr ens1.symm) := by
        rw [hQs, hQs1, hψeq, hD'φ i, Matrix.inv_submatrix_equiv]
        rw [Matrix.submatrix_mul_equiv (g'.P i)⁻¹ (φ' i)
              (finCongr ens.symm) (finCongr ens.symm) (finCongr ens1.symm)]
        rw [Matrix.submatrix_mul_equiv ((g'.P i)⁻¹ * φ' i) (g'.P (i + 1))
              (finCongr ens.symm) (finCongr ens1.symm) (finCongr ens1.symm)]
      have hQsunit : IsUnit Qs.det := by
        rw [hQs, Matrix.det_submatrix_equiv_self]; exact g'.unit i
      have hkey : (Ppad i)⁻¹ * C₁.φ i * Ppad (i + 1)
          = (padBlock ((D'φ' i).submatrix (finCongr ens.symm) (finCongr ens1.symm))).submatrix
              (finCongr hα) (finCongr hβ) := by
        rw [hPi, hPi1, hC1, Matrix.inv_submatrix_equiv, padBlock_inv Qs hQsunit]
        rw [Matrix.submatrix_mul_equiv (padBlock Qs⁻¹) (padBlock ψ)
              (finCongr hα) (finCongr hα) (finCongr hβ)]
        rw [Matrix.submatrix_mul_equiv (padBlock Qs⁻¹ * padBlock ψ) (padBlock Qs1)
              (finCongr hα) (finCongr hβ) (finCongr hβ)]
        rw [padBlock_mul, padBlock_mul, ← hinner]
      rw [hkey]
      apply isPartialPerm_submatrix
      apply padBlock_isPartialPerm
      exact isPartialPerm_submatrix (D'φ' i) (finCongr ens.symm) (finCongr ens1.symm) (hD'φ'pp i)
    by_cases hbs : i + 1 = s
    · subst hbs
      have hi_ne_s : i ≠ i + 1 := by omega
      have hi_ne_s1 : i ≠ i + 1 + 1 := by omega
      set ei : Fin (n' i) ≃ Fin (C₁.n i) := finCongr (enother i hi_ne_s hi_ne_s1) with hei
      have hcol0' := hpcol i rfl
      set Q : Matrix (Fin α) (Fin α) R :=
        (g'.P (i + 1)).submatrix (finCongr ens.symm) (finCongr ens.symm) with hQ
      have hPi : Ppad i = (g'.P i).submatrix ei.symm ei.symm := by
        simp only [hPpaddef, dite_eq_right hi_ne_s, dite_eq_right hi_ne_s1]
        rfl
      have hPi1 : Ppad (i + 1) = (padBlock Q).submatrix (finCongr hα) (finCongr hα) := by
        simp only [hPpaddef, dite_eq_left rfl]
        rfl
      set Cr : Matrix (Fin (n' i)) (Fin (α + 1)) R :=
        (C₁.φ i).submatrix ei (finCongr hα.symm) with hCr
      have hCrcol0 : ∀ p, Cr p 0 = 0 := by
        intro p
        rw [hCr, Matrix.submatrix_apply]
        have := hcol0' (ei p)
        simpa using this
      set E : Matrix (Fin (n' i)) (Fin (α + 1)) R := (g'.P i)⁻¹ * Cr * padBlock Q with hE
      have hDeq : (Ppad i)⁻¹ * C₁.φ i * Ppad (i + 1)
          = E.submatrix ei.symm (finCongr hα) := by
        rw [hPi, hPi1, hE]
        have hC1 : C₁.φ i = Cr.submatrix ei.symm (finCongr hα) := by
          rw [hCr]; ext a b
          simp only [Matrix.submatrix_apply, finCongr_apply, Equiv.apply_symm_apply,
            Fin.cast_cast, Fin.cast_eq_self]
        rw [hC1, Matrix.inv_submatrix_equiv]
        rw [Matrix.submatrix_mul_equiv (g'.P i)⁻¹ Cr ei.symm ei.symm (finCongr hα)]
        rw [Matrix.submatrix_mul_equiv ((g'.P i)⁻¹ * Cr) (padBlock Q)
              ei.symm (finCongr hα) (finCongr hα)]
      rw [hDeq]
      apply isPartialPerm_submatrix
      apply isPartialPerm_prepend_zero_col
      · intro p
        rw [hE, Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        refine Fin.cases ?_ (fun k' => ?_) k
        · rw [padBlock_zero_zero, mul_one]
          rw [Matrix.mul_apply]
          apply Finset.sum_eq_zero
          intro j _
          rw [hCrcol0 j, mul_zero]
        · rw [padBlock_succ_zero, mul_zero]
      · have hdrop : E.submatrix id Fin.succ
            = (D'φ' i).submatrix id (finCongr ens.symm) := by
          have step1 : E.submatrix id Fin.succ
              = (g'.P i)⁻¹ * Cr * (padBlock Q).submatrix id Fin.succ := by
            rw [hE]; ext p q
            simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply]
          have step2 : Cr * (padBlock Q).submatrix id Fin.succ
              = (Cr.submatrix id Fin.succ) * Q := by
            ext p q
            rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ]
            simp only [Matrix.submatrix_apply, id_eq, padBlock_zero_succ, hCrcol0 p,
              mul_zero, zero_add, padBlock_succ_succ]
          have step3 : Cr.submatrix id Fin.succ = (φ' i).submatrix id (finCongr ens.symm) := by
            ext p q
            simp only [Matrix.submatrix_apply, id_eq]
            rw [hCr, Matrix.submatrix_apply, eval_sm1 i rfl]
            congr 1
          rw [step1, Matrix.mul_assoc, step2, step3, hQ]
          rw [Matrix.submatrix_mul_equiv (φ' i) (g'.P (i + 1)) id (finCongr ens.symm)
                (finCongr ens.symm)]
          rw [hD'φ i, Matrix.mul_assoc]
          ext p q
          simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply]
        rw [hdrop]
        exact isPartialPerm_submatrix (D'φ' i) (Equiv.refl _) (finCongr ens.symm) (hD'φ'pp i)
    · have hi_ne_s : i ≠ s := his
      have hi_ne_s1 : i ≠ s + 1 := his1
      have hi1_ne_s : i + 1 ≠ s := hbs
      have hi1_ne_s1 : i + 1 ≠ s + 1 := by omega
      set ei : Fin (n' i) ≃ Fin (C₁.n i) := finCongr (enother i hi_ne_s hi_ne_s1) with hei
      set ei1 : Fin (n' (i + 1)) ≃ Fin (C₁.n (i + 1)) :=
        finCongr (enother (i + 1) hi1_ne_s hi1_ne_s1) with hei1
      have hPi : Ppad i = (g'.P i).submatrix ei.symm ei.symm := by
        simp only [hPpaddef, dite_eq_right hi_ne_s, dite_eq_right hi_ne_s1]
        rfl
      have hPi1 : Ppad (i + 1) = (g'.P (i + 1)).submatrix ei1.symm ei1.symm := by
        simp only [hPpaddef, dite_eq_right hi1_ne_s, dite_eq_right hi1_ne_s1]
        rfl
      have hC1 : C₁.φ i = (φ' i).submatrix ei.symm ei1.symm := by
        rw [mat_other i hi_ne_s hi1_ne_s hi_ne_s1, Matrix.submatrix_submatrix]
        rfl
      have hkey : (Ppad i)⁻¹ * C₁.φ i * Ppad (i + 1)
          = (D'φ' i).submatrix ei.symm ei1.symm := by
        rw [hPi, hPi1, hC1, hD'φ i, Matrix.inv_submatrix_equiv]
        rw [Matrix.submatrix_mul_equiv (g'.P i)⁻¹ (φ' i) ei.symm ei.symm ei1.symm]
        rw [Matrix.submatrix_mul_equiv ((g'.P i)⁻¹ * φ' i) (g'.P (i + 1)) ei.symm ei1.symm ei1.symm]
      rw [hkey]
      exact isPartialPerm_submatrix (D'φ' i) ei.symm ei1.symm (hD'φ'pp i)
/-- Over a Noetherian local ring with maximal ideal in `Ass R`, if `C` is exact and `t` satisfies
`1 ≤ t ≤ e`, `n t > 0` and `n (t + 1) = 0`, there is an exact complex `C'` of strictly smaller
total rank such that `C` is trivializable whenever `C'` is. -/
theorem split_reduction [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (IsLocalRing.maximalIdeal R) ∈ associatedPrimes R R)
    (C : BoundedFreeComplex R) (hC : C.Exact)
    (t : ℕ) (ht1 : 1 ≤ t) (hte : t ≤ C.e) (htpos : 0 < C.n t) (htzero : C.n (t + 1) = 0) :
    ∃ C' : BoundedFreeComplex R, C'.Exact ∧ C'.totalRank < C.totalRank ∧
      (Trivializable C' → Trivializable C) := by
  obtain ⟨C₁, fiso, he₁, hn₁, hrank, hC₁exact,
          α, β, hα, hβ, ψ, hcorner, hrow0, hcol0, hψ, hpivotcol⟩ :=
    exists_iso_blockDiag_one hdepth C hC t ht1 hte htpos htzero
  have hte₁ : t ≤ C₁.e := by rw [he₁]; exact hte
  have htpos₁ : 0 < C₁.n t := by rw [hn₁]; exact htpos
  have htzero₁ : C₁.n (t + 1) = 0 := by rw [hn₁]; exact htzero
  obtain ⟨C', hC'exact, hlt₁, hlift₁⟩ :=
    exists_exact_totalRank_lt_of_blockDiag_one C₁ hC₁exact t ht1 hte₁ htpos₁ htzero₁ α β hα hβ
      ψ hcorner hrow0 hcol0 hψ hpivotcol
  refine ⟨C', hC'exact, ?_, ?_⟩
  · rw [← hrank]; exact hlt₁
  · intro hC'triv
    exact iso_trivializable fiso he₁ (hlift₁ hC'triv)

/-- Over a Noetherian local ring with maximal ideal in `Ass R`, if `C` is exact and has a nonzero
term in positive degree, there is an exact complex `C'` of strictly smaller total rank such that
`C` is trivializable whenever `C'` is. -/
theorem split_off_identity_block [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (IsLocalRing.maximalIdeal R) ∈ associatedPrimes R R)
    (C : BoundedFreeComplex R) (hC : C.Exact)
    (i : ℕ) (hi : 1 ≤ i) (hpos : 0 < C.n i) :
    ∃ C' : BoundedFreeComplex R, C'.Exact ∧ C'.totalRank < C.totalRank ∧
      (Trivializable C' → Trivializable C) := by
  obtain ⟨t, ht1, hte, htpos, htzero⟩ := top_index C i hi hpos
  exact split_reduction hdepth C hC t ht1 hte htpos htzero

/-- Over a Noetherian local ring with maximal ideal in `Ass R`, every exact complex is
trivializable. -/
theorem trivializable_of_exact [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (IsLocalRing.maximalIdeal R) ∈ associatedPrimes R R)
    (C : BoundedFreeComplex R) (hC : C.Exact) :
    Trivializable C := by
  generalize hN : C.totalRank = N
  induction N using Nat.strong_induction_on generalizing C with
  | _ N IH =>
    by_cases htop : ∀ i, 1 ≤ i → C.n i = 0
    · exact trivializable_of_top_zero C htop
    · push Not at htop
      obtain ⟨i, hi, hpos⟩ := htop
      obtain ⟨C', hC'exact, hlt, hlift⟩ :=
        split_off_identity_block hdepth C hC i hi (Nat.pos_of_ne_zero hpos)
      exact hlift (IH C'.totalRank (hN ▸ hlt) C' hC'exact rfl)

end BoundedFreeComplex

/-- Let `R` be a Noetherian local ring whose maximal ideal `m` is an associated prime of `R`, i.e.
`R` has depth `0`. Then every complex of finite free `R`-modules
`0 → R^{n_e} → ⋯ → R^{n_0}` which is exact at `R^{n_e}, …, R^{n_1}` is isomorphic to a complex
of the same length and ranks all of whose differentials are partial permutation matrices, that
is, to a direct sum of trivial complexes. -/
@[stacks 00MY]
theorem exists_trivial_iso_of_exact
    [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (IsLocalRing.maximalIdeal R) ∈ associatedPrimes R R)
    (C : BoundedFreeComplex R) (hC : C.Exact) :
    ∃ D : BoundedFreeComplex R, ∃ _ : C.Iso D,
      D.e = C.e ∧ (∀ i, D.n i = C.n i) ∧ D.IsTrivial :=
  BoundedFreeComplex.trivializable_of_exact hdepth C hC

end
