module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import StacksCore.Tactic.StacksAttribute

/-!
# Irreducibility of the generic determinant

Over a field, the determinant of a square matrix of independent variables is an irreducible
multivariate polynomial, provided the matrix has positive size. The induction expands the
determinant along the first row, writing it as `f * X (0, 0) + g` with `f` the determinant of
the generic matrix one size smaller; `f` is irreducible by induction, neither `f` nor `g`
involves the variable `X (0, 0)`, and `f` does not divide `g`, which is what the
irreducibility criterion for such a linear expression needs.

## Main results

* `MvPolynomial.irreducible_det_genericMatrix`: the determinant of the generic `n × n` matrix
  over a field is irreducible.

## Implementation notes

The polynomial ring in the entries of the matrix is represented as the multivariate
polynomial ring whose variables are indexed by pairs in `Fin n × Fin n`. The generic matrix
therefore has entry `MvPolynomial.X (i, j)` in position `(i, j)`.

That `f` does not divide `g` is checked by evaluating at the permutation matrix of the
transposition `(0 1)`: that evaluation kills `f` and `X (0, 0)` but sends the whole
determinant to the sign of the transposition, hence sends `g` to `-1`.

## References

* [Stacks Project, Tag 0B2V](https://stacks.math.columbia.edu/tag/0B2V)
-/

public section

namespace MvPolynomial

/-- The generic `n × n` matrix over `k`: its entry in position `(i, j)` is the independent
variable `X (i, j)`. -/
private noncomputable def genericMatrix (k : Type*) [CommRing k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  fun i j ↦ MvPolynomial.X (i, j)

/-- The determinant of the generic matrix of size one less, viewed inside the polynomial ring
of the larger matrix: the cofactor of the entry in position `(0, 0)`. -/
private noncomputable def genericFirstMinor (k : Type*) [CommRing k] (m : ℕ) :
    MvPolynomial (Fin m.succ × Fin m.succ) k :=
  Matrix.det ((genericMatrix k m.succ).submatrix Fin.succ Fin.succ)

/-- The part of the first-row expansion of the generic determinant coming from the columns
other than the first. -/
private noncomputable def genericFirstRowTail (k : Type*) [CommRing k] (m : ℕ) :
    MvPolynomial (Fin m.succ × Fin m.succ) k :=
  ∑ j ∈ Finset.univ.erase (0 : Fin m.succ), (-1) ^ (j : ℕ) * genericMatrix k m.succ 0 j *
    Matrix.det ((genericMatrix k m.succ).submatrix Fin.succ j.succAbove)

/-- Adjoining any collection of independent variables does not make an irreducible
multivariate polynomial reducible. -/
private lemma irreducible_rename_of_injective
    {R α β : Type*} [Field R] {p : MvPolynomial α R} {f : α → β}
    (hp : Irreducible p) (hf : Function.Injective f) :
    Irreducible (MvPolynomial.rename f p) := by
  classical
  let e : α ≃ Set.range f := Equiv.ofInjective f hf
  rw [show f = ((↑) : Set.range f → β) ∘ e from rfl, ← MvPolynomial.rename_rename]
  exact ((MvPolynomial.prime_rename_iff (R := R) (Set.range f)).2
    (hp.map (MvPolynomial.renameEquiv R e)).prime).irreducible

/-- Renaming the variables of the generic determinant gives the determinant of the matrix of
the renamed variables. -/
private lemma rename_det_genericMatrix {R β : Type*} [CommRing R] {n : ℕ}
    (f : Fin n × Fin n → β) :
    MvPolynomial.rename f (genericMatrix R n).det =
      Matrix.det (fun i j : Fin n ↦ MvPolynomial.X (f (i, j)) :
        Matrix (Fin n) (Fin n) (MvPolynomial β R)) := by
  classical
  calc
    _ = ((MvPolynomial.rename f).toRingHom.mapMatrix (genericMatrix R n)).det :=
      RingHom.map_det (MvPolynomial.rename f).toRingHom (genericMatrix R n)
    _ = _ := by
      congr 1
      funext i j
      show MvPolynomial.rename f (MvPolynomial.X (i, j)) = _
      simp

/-- A variable absent from every entry of a matrix is absent from its determinant. -/
private lemma not_mem_vars_det {R ι σ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (x : σ) (M : Matrix ι ι (MvPolynomial σ R))
    (h : ∀ i j, x ∉ (M i j).vars) : x ∉ M.det.vars := by
  classical
  rw [Matrix.det_apply']
  intro hx
  have hx' := MvPolynomial.vars_sum_subset Finset.univ
    (fun p : Equiv.Perm ι ↦ (Equiv.Perm.sign p : MvPolynomial σ R) * ∏ i, M (p i) i) hx
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx'
  obtain ⟨p, hp⟩ := hx'
  have hp' := MvPolynomial.vars_mul
    (Equiv.Perm.sign p : MvPolynomial σ R) (∏ i, M (p i) i) hp
  have hconst : ((Equiv.Perm.sign p : MvPolynomial σ R)).vars = ∅ := MvPolynomial.vars_C
  rw [hconst, Finset.empty_union] at hp'
  have hp'' := MvPolynomial.vars_prod (s := Finset.univ) (fun i ↦ M (p i) i) hp'
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hp''
  obtain ⟨i, hi⟩ := hp''
  exact h (p i) i hi

/-- The variable `X (0, 0)` is not `X (i.succ, j)`: the first index is nonzero. -/
private lemma zero_zero_not_mem_vars_X_succ {k : Type*} [Field k] {m : ℕ} (i : Fin m)
    (j : Fin m.succ) :
    ((0, 0) : Fin m.succ × Fin m.succ) ∉
      (MvPolynomial.X (i.succ, j) : MvPolynomial (Fin m.succ × Fin m.succ) k).vars := by
  simp only [MvPolynomial.vars_X, Finset.mem_singleton]
  intro hzero
  exact Fin.succ_ne_zero i (congrArg Prod.fst hzero).symm

/-- The variable `X (0, 0)` does not occur in the cofactor of the entry in position
`(0, 0)`: that minor only involves variables with both indices nonzero. -/
private lemma not_mem_vars_genericFirstMinor {k : Type*} [Field k] (m : ℕ) :
    ((0, 0) : Fin m.succ × Fin m.succ) ∉ (genericFirstMinor k m).vars := by
  classical
  exact not_mem_vars_det _ _ fun i j ↦ zero_zero_not_mem_vars_X_succ i j.succ

/-- The variable `X (0, 0)` does not occur in the rest of the first-row expansion: each of its
terms involves either a first-row entry in a nonzero column or a minor avoiding the first
row. -/
private lemma not_mem_vars_genericFirstRowTail {k : Type*} [Field k] (m : ℕ) :
    ((0, 0) : Fin m.succ × Fin m.succ) ∉ (genericFirstRowTail k m).vars := by
  classical
  intro hx
  rw [genericFirstRowTail] at hx
  have hx' := MvPolynomial.vars_sum_subset (Finset.univ.erase (0 : Fin m.succ))
    (fun j ↦ (-1) ^ (j : ℕ) * genericMatrix k m.succ 0 j *
      Matrix.det ((genericMatrix k m.succ).submatrix Fin.succ j.succAbove)) hx
  simp only [Finset.mem_biUnion] at hx'
  obtain ⟨j, hj, hxj⟩ := hx'
  have hj0 : j ≠ 0 := by simpa using hj
  have h₁ := MvPolynomial.vars_mul ((-1) ^ (j : ℕ) * genericMatrix k m.succ 0 j)
    (Matrix.det ((genericMatrix k m.succ).submatrix Fin.succ j.succAbove)) hxj
  rcases Finset.mem_union.mp h₁ with hleft | hright
  · have h₂ := MvPolynomial.vars_mul ((-1) ^ (j : ℕ)) (genericMatrix k m.succ 0 j) hleft
    rcases Finset.mem_union.mp h₂ with hc | hentry
    · have hconst : ((-1 : MvPolynomial (Fin m.succ × Fin m.succ) k) ^ (j : ℕ)).vars = ∅ := by
        rw [show (-1 : MvPolynomial (Fin m.succ × Fin m.succ) k) =
          MvPolynomial.C (-1 : k) by simp, ← MvPolynomial.C_pow]
        exact MvPolynomial.vars_C
      rw [hconst] at hc
      simp at hc
    · change (0, 0) ∈ (MvPolynomial.X ((0 : Fin m.succ), j) :
        MvPolynomial (Fin m.succ × Fin m.succ) k).vars at hentry
      have heq : ((0, 0) : Fin m.succ × Fin m.succ) = (0, j) := by
        simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using hentry
      exact hj0 (congrArg Prod.snd heq).symm
  · exact not_mem_vars_det (0, 0) _
      (fun i l ↦ zero_zero_not_mem_vars_X_succ i (j.succAbove l)) hright

/-- The first-row expansion of the generic determinant, with the first column separated
out. -/
private lemma det_genericMatrix_succ (k : Type*) [CommRing k] (m : ℕ) :
    (genericMatrix k m.succ).det =
      genericFirstMinor k m * MvPolynomial.X (0, 0) + genericFirstRowTail k m := by
  classical
  rw [Matrix.det_succ_row_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin m.succ))]
  simp [genericFirstMinor, genericFirstRowTail, genericMatrix, mul_comm]

/-- The cofactor of the entry `(0, 0)` does not divide the rest of the first-row expansion:
evaluating at the permutation matrix of the transposition `(0 1)` kills the cofactor and the
variable `X (0, 0)`, so it sends the rest of the expansion to the sign of the
transposition. -/
private lemma not_genericFirstMinor_dvd_genericFirstRowTail {k : Type*} [Field k] {m : ℕ}
    (hm : m ≠ 0) : ¬ genericFirstMinor k m ∣ genericFirstRowTail k m := by
  classical
  rintro ⟨q, hq⟩
  let σ : Equiv.Perm (Fin m.succ) := Equiv.swap 0 1
  let φ : Fin m.succ × Fin m.succ → k := fun ij ↦ if ij.2 = σ ij.1 then 1 else 0
  let ev := MvPolynomial.eval φ
  have h01 : (0 : Fin m.succ) ≠ 1 := fun h ↦ hm (by simpa using congrArg Fin.val h)
  have hs0 : σ 0 = 1 := by simp [σ]
  have hs1 : σ 1 = 0 := by simp [σ]
  have hmatrix : ev.mapMatrix (genericMatrix k m.succ) = σ.permMatrix k := by
    rw [RingHom.mapMatrix_apply]
    ext i j
    show ev (MvPolynomial.X (i, j)) = (σ.permMatrix k) i j
    simp only [ev, MvPolynomial.eval_X, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp [φ, eq_comm]
  have hdet : ev (genericMatrix k m.succ).det = -1 := by
    rw [RingHom.map_det, hmatrix, Matrix.det_permutation, Equiv.Perm.sign_swap h01]
    simp
  have hminor : ev (genericFirstMinor k m) = 0 := by
    rw [genericFirstMinor, RingHom.map_det]
    let r0 : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    apply Matrix.det_eq_zero_of_row_eq_zero r0
    have hr0 : Fin.succ r0 = (1 : Fin m.succ) := by
      apply Fin.ext
      simp [r0, Nat.mod_eq_of_lt (show 1 < m + 1 by omega)]
    intro j
    show ev (MvPolynomial.X (Fin.succ r0, Fin.succ j)) = 0
    simp only [ev, MvPolynomial.eval_X]
    simp [φ, hr0, hs1]
  have hx : ev (MvPolynomial.X ((0, 0) : Fin m.succ × Fin m.succ)) = 0 := by
    simp [ev, φ, hs0, h01]
  rw [det_genericMatrix_succ, hq] at hdet
  simp [hminor, hx] at hdet

/-- The cofactor of the entry `(0, 0)` of the generic matrix is irreducible: it is the generic
determinant of size one less, with its variables renamed injectively. -/
private lemma irreducible_genericFirstMinor {k : Type*} [Field k] {m : ℕ}
    (ih : Irreducible (genericMatrix k m).det) : Irreducible (genericFirstMinor k m) := by
  let e : Fin m × Fin m → Fin m.succ × Fin m.succ := fun ij ↦ (ij.1.succ, ij.2.succ)
  have he : Function.Injective e := fun _ _ h ↦
    Prod.ext (Fin.succ_inj.mp (congrArg Prod.fst h)) (Fin.succ_inj.mp (congrArg Prod.snd h))
  have hren : genericFirstMinor k m = MvPolynomial.rename e (genericMatrix k m).det := by
    rw [rename_det_genericMatrix]
    rfl
  rw [hren]
  exact irreducible_rename_of_injective ih he

/-- **Stacks Project, Tag 0B2V.** The determinant of the generic square matrix of positive
size over a field is an irreducible multivariate polynomial. -/
@[stacks 0B2V]
lemma irreducible_det_genericMatrix (k : Type*) [Field k] (n : ℕ) (hn : 0 < n) :
    Irreducible (Matrix.det (fun i j : Fin n ↦ MvPolynomial.X (i, j) :
      Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k))) := by
  classical
  show Irreducible (genericMatrix k n).det
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      rw [show (genericMatrix k 1).det = MvPolynomial.X ((0, 0) : Fin 1 × Fin 1) from
        Matrix.det_fin_one _]
      simpa [MvPolynomial.sumSMulX] using
        (MvPolynomial.irreducible_sumSMulX
          (c := Finsupp.single ((0, 0) : Fin 1 × Fin 1) (1 : k)) (by simp) (by simp))
    · have hf := irreducible_genericFirstMinor (ih (Nat.pos_of_ne_zero hm))
      rw [det_genericMatrix_succ]
      exact MvPolynomial.irreducible_mul_X_add _ _ _ hf.ne_zero
        (not_mem_vars_genericFirstMinor m) (not_mem_vars_genericFirstRowTail m)
        (hf.isRelPrime_iff_not_dvd.mpr (not_genericFirstMinor_dvd_genericFirstRowTail hm))

end MvPolynomial
